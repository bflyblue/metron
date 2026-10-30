{- | Binding groups (design §2.2, §6.2, §6.3, §7.1): dependency analysis,
cycle construction and hashing, type inference, and entry into the
codebase. Nothing from a group is stored unless the whole group checks.
-}
module Eval.Resolve (
  ResolveError (..),
  renderResolveError,
  resolverFor,
  typeLookupFor,
  processGroup,
  enterData,
  queryScheme,
  storeTerm,
  withHint,
) where

import Control.Monad (when, zipWithM)
import Control.Monad.State.Strict (StateT, gets, lift, modify, runStateT)
import Data.Char (isLower)
import Data.Foldable (foldlM)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Desugar qualified as D
import Eval.Dimension
import Eval.Hash
import Eval.Infer
import Eval.Syntax qualified as S
import Eval.TCore (lintClosed)
import Eval.Type

data ResolveError
  = DuplicateDefinition S.Name
  | Desugar DesugarError
  | {- | A type error in the named definition, at a span when provenance
    could place it.
    -}
    TypeErrorIn S.Name (Maybe S.Span) Text
  | -- | Elaboration produced ill-typed Typed Core: an internal error.
    LintFailure S.Name Text
  | -- | A @ declaration that cannot be entered, at the offending span.
    DataError S.Span Text
  deriving stock (Eq, Show)

-- | Render without source text; "Eval.Driver" renders with the excerpt.
renderResolveError :: ResolveError -> Text
renderResolveError = \case
  DuplicateDefinition n ->
    T.pack (show n.span.from.line)
      <> ":"
      <> T.pack (show n.span.from.col)
      <> ": `"
      <> n.text
      <> "` is defined twice in the same group"
  Desugar e -> renderDesugarError e
  TypeErrorIn n sp msg ->
    S.renderSpanError
      Nothing
      (maybe n.span id sp)
      ("in `" <> n.text <> "`: " <> msg)
  LintFailure n msg ->
    "internal error: elaboration of `"
      <> n.text
      <> "` produced ill-typed core: "
      <> msg
  DataError sp msg -> S.renderSpanError Nothing sp msg

-- | Free names resolve to whatever the codebase currently binds.
resolverFor :: Codebase -> Resolver
resolverFor cb n
  -- A field is looked up under its dot, the one way it is written (design §2.3).
  | Just f <- T.stripPrefix "." n = case lookupFieldName f cb of
      Just (h, i, j)
        | Just def <- lookupTypeDef h cb
        , let arity = length (def.constructors !! i) ->
            Just (AField (FieldInfo (UserCon h i) arity j (fieldNamesOf h i arity cb)))
      _ -> Nothing
  | otherwise = case lookupName n cb of
      Just (Reference h i) -> Just (ATerm (Resolution (h, i) (isUnitName n cb) (isScaleName n cb)))
      Nothing -> case lookupConName n cb of
        Just (h, i)
          | Just def <- lookupTypeDef h cb ->
              Just
                ( AConstructor
                    ( ConInfo
                        (UserCon h i)
                        (length (def.constructors !! i))
                        [(UserCon h j, length fs) | (j, fs) <- zip [0 ..] def.constructors]
                    )
                )
        _ -> Nothing

typeLookupFor :: Codebase -> TypeLookup
typeLookupFor cb = TypeLookup (`lookupTypes` cb) (`lookupTypeDef` cb)

{- | Enter a binding group into the codebase. Statements may refer to each
other in any order; strongly connected components are hashed as cycles.
Components are processed dependencies-first, so a reference from one
component to another always sees the new hash and its type.
-}
processGroup :: Codebase -> [S.Decl] -> Either ResolveError Codebase
processGroup cb0 decls = do
  checkDuplicates decls
  -- Data declarations first, in order: the definitions may use their constructors.
  cb1 <- foldlM enterData cb0 [d | S.DData d <- decls]
  let bindings = [b | S.DBind b <- decls]
      groupNames = Set.fromList (map (.name.text) bindings)
      nodes =
        [ ( b
          , b.name.text
          , Set.toList (Set.intersection groupNames (freeNames (asLambda b)))
          )
        | b <- bindings
        ]
  foldlM enterComponent cb1 (stronglyConnComp nodes)

checkDuplicates :: [S.Decl] -> Either ResolveError ()
checkDuplicates = go Set.empty
 where
  go _ [] = Right ()
  go seen (b : bs)
    | b.name.text `Set.member` seen = Left (DuplicateDefinition b.name)
    | otherwise = go (Set.insert b.name.text seen) bs

asLambda :: S.Binding -> S.Expr
asLambda b = case b.params of
  [] -> b.body
  _ -> S.Expr b.span (S.Lam b.params b.body)

enterComponent :: Codebase -> SCC S.Binding -> Either ResolveError Codebase
enterComponent cb = \case
  AcyclicSCC b -> do
    (term, prov) <-
      either
        (Left . Desugar)
        Right
        (desugarDefinition b.name.text (resolverFor cb) (asLambda b))
    (schemes, typed) <-
      either
        (Left . typeErrorIn b prov)
        Right
        (elaborateClosed (typeLookupFor cb) term)
    linted <-
      either (Left . LintFailure b.name) Right (lintClosed (typeLookupFor cb) typed)
    let h = hashTerm term
        ref = Reference h Nothing
        cb' =
          bindName b.name.text ref (addTerm h term (preferLint schemes linted) typed cb)
    pure (markKind b.kind b.name.text cb')
  CyclicSCC bs -> enterCycle cb bs

-- | Inference and lint must agree; lint is the authority if they ever differ.
preferLint :: [Scheme] -> [Scheme] -> [Scheme]
preferLint _ linted = linted

typeErrorIn :: S.Binding -> Provenance -> TypeError -> ResolveError
typeErrorIn b prov err = located b.name (provenanceAt err.path prov) err.message

-- | A type error at a located node, with the node's hint under the message.
located :: S.Name -> Maybe (S.Span, Maybe Text) -> Text -> ResolveError
located n at msg = case at of
  Just (sp, hint) -> TypeErrorIn n (Just sp) (withHint hint msg)
  Nothing -> TypeErrorIn n Nothing msg

withHint :: Maybe Text -> Text -> Text
withHint hint msg = maybe msg (\h -> msg <> "\n  hint: " <> h) hint

{- | Design §6.2. The members are first desugared in their input order to
compute ordering hashes with the cycle variables as placeholders, then
desugared again in the resulting order to build the stored 'Cycle'.
-}
enterCycle :: Codebase -> [S.Binding] -> Either ResolveError Codebase
enterCycle cb bs = do
  ordering <- mapM (\b -> (,b) <$> placeholderHashOf bs b) bs
  let sorted = map snd (sortOn fst ordering)
  case vecFromList sorted of
    SomeVec members -> do
      let ctx = vecAppend (vecMap (.name.text) members) VNil
      desugared <- vecTraverse (desugarOne ctx) members
      let bodies = vecMap fst desugared
          provs = vecToList (vecMap snd desugared)
          cycleTerm = Cycle (vecMap (Hint . (.name.text)) members) bodies
          h = hashTerm cycleTerm
      (schemes, typed) <-
        either
          (Left . cycleTypeError sorted provs)
          Right
          (elaborateClosed (typeLookupFor cb) cycleTerm)
      linted <-
        either
          (Left . LintFailure (headName sorted))
          Right
          (lintClosed (typeLookupFor cb) typed)
      let cb' = addTerm h cycleTerm (preferLint schemes linted) typed cb
          bindMember acc (i, b) =
            let ref = Reference h (Just i)
                acc' = bindName b.name.text ref acc
             in markKind b.kind b.name.text acc'
      pure (foldl bindMember cb' (zip [0 ..] sorted))
 where
  desugarOne ::
    Vec k Text -> S.Binding -> Either ResolveError (Term k, Provenance)
  desugarOne ctx b =
    either
      (Left . Desugar)
      Right
      (D.desugarMember b.name.text (resolverFor cb) ctx (asLambda b))

  placeholderHashOf :: [S.Binding] -> S.Binding -> Either ResolveError Hash
  placeholderHashOf group b = case vecFromList (map (.name.text) group) of
    SomeVec ns -> do
      (t, _) <- desugarOne (vecAppend ns VNil) b
      pure (placeholderHash t)

  -- Inside a cycle the error path starts with the member index.
  cycleTypeError sorted provs err = case err.path of
    i : rest
      | Just b <- nth i sorted
      , Just prov <- nth i provs ->
          located b.name (provenanceAt rest prov) err.message
    _ -> TypeErrorIn (headName sorted) Nothing err.message
  nth i xs = case drop i xs of
    x : _ | i >= 0 -> Just x
    _ -> Nothing
  headName = \case
    b : _ -> b.name
    [] -> S.Name (S.Span (S.Pos 1 1) (S.Pos 1 1)) "?"

-- | Names an expression mentions that are not bound inside it.
freeNames :: S.Expr -> Set Text
freeNames = go Set.empty
 where
  go bound e = case e.node of
    S.Num _ -> Set.empty
    S.Labelled _ a -> go bound a
    S.Tuple es -> foldMap (go bound) es
    S.List es -> foldMap (go bound) es
    S.CaseOf s alts ->
      go bound s
        <> foldMap
          (\(p, b) -> go (foldr (Set.insert . (.text)) bound (patternNames p)) b)
          alts
    S.Bool _ -> Set.empty
    S.Var x -> if x `Set.member` bound then Set.empty else Set.singleton x
    S.Lam ns b -> go (foldr (Set.insert . (.text)) bound ns) b
    S.App f a -> go bound f <> go bound a
    S.Let n ps rhs body ->
      go (foldr (Set.insert . (.text)) bound ps) rhs
        <> go (Set.insert n.text bound) body
    S.If c t f -> go bound c <> go bound t <> go bound f
    S.BinOp op a b -> opNames op <> go bound a <> go bound b
    S.Neg a -> go bound a
    S.Pow a _ -> go bound a
    S.SectionL op a -> opNames op <> go bound a
    S.SectionR a op -> opNames op <> go bound a
    S.Vec es -> foldMap (go bound) es
    S.Proj a _ -> go bound a
    S.Slice a _ _ -> go bound a
    S.FieldOf a _ -> go bound a
    S.Record hd fs -> go bound hd <> foldMap (go bound . snd) fs
  opNames = \case
    S.Infix n -> Set.singleton n
    _ -> Set.empty

{- | Enter a Core term that already has its hash, as when loading a store
(design §7.4): infer, lint and add. The term must only reference hashes the
codebase already holds, which the loader ensures by ordering.
-}
storeTerm :: Hash -> Term Z -> Codebase -> Either Text Codebase
storeTerm h term cb = do
  (schemes, typed) <-
    either (Left . (.message)) Right (elaborateClosed (typeLookupFor cb) term)
  linted <- lintClosed (typeLookupFor cb) typed
  pure (addTerm h term (preferLint schemes linted) typed cb)

{- | Record what a binding declared besides its value.
| Record what a binding declared besides its value. A plain `let` clears
any unit or scale flag the name carried: `let g = 9.81 m/s^2` is a
quantity even though `g` was the gram.
-}
markKind :: S.BindKind -> Text -> Codebase -> Codebase
markKind kind n cb = case kind of
  S.Plain -> clearFlags n cb
  S.Unit -> markUnit n cb
  S.ScaleDecl -> markScale n cb

-- | The variables a pattern binds.
patternNames :: S.Pattern -> [S.Name]
patternNames p = case p.node of
  S.PCon _ ns -> ns
  S.PVar n -> [n]
  S.PWild -> []

-- Data declarations ----------------------------------------------------------------

{- | Enter a @data@ declaration (design §2.3). The parameters take their
kinds from the positions the fields use them in; the field types are
checked against the types in scope; the definition is hashed and stored,
and the type's and constructors' names bound to it.
-}
enterData :: Codebase -> S.DataDecl -> Either ResolveError Codebase
enterData cb decl = do
  distinct "parameter" decl.params
  distinct "constructor" (map fst decl.constructors)
  distinct "field" (map fst fieldLabels)
  -- Field names make a record: a type of one constructor, so that @r.f@ is total.
  case (decl.constructors, fieldLabels) of
    (_ : _ : _, (n, _) : _) ->
      Left (DataError n.span "field names need a type with one constructor")
    _ -> pure ()
  when (decl.name.text `elem` builtinTypeNames)
    $ Left
      (DataError decl.name.span ("`" <> decl.name.text <> "` is a built-in type"))
  -- Two passes: the first learns the parameters' kinds from where they
  -- appear, the second converts with the kinds known, so that the
  -- arguments of a recursive occurrence can be read by their kinds.
  (_, kinds1) <- runStateT convertAll Map.empty
  (fieldss, kinds) <- runStateT convertAll kinds1
  let params =
        [(i, Map.findWithDefault KType p.text kinds) | (i, p) <- zip [0 ..] decl.params]
      def =
        TypeDef
          params
          fieldss
          (if decl.structural then structuralLabel else Owner decl.name.text)
      h = hashTypeDef def
      cb' = bindTypeName decl.name.text h (addTypeDef h def cb)
      withCons =
        foldl
          (\acc (i, (c, _)) -> bindConName c.text h i acc)
          cb'
          (zip [0 ..] decl.constructors)
  pure
    (foldl (\acc (n, j) -> bindFieldName n.text h 0 j acc) withCons fieldLabels)
 where
  env =
    DataEnv
      { codebase = cb
      , self = decl.name
      , params = Map.fromList (zip (map (.text) decl.params) [0 ..])
      , paramNames = map (.text) decl.params
      }
  convertAll = mapM (mapM (tyType env . (.ty)) . snd) decl.constructors
  fieldLabels =
    [ (n, j)
    | (_, fs) <- decl.constructors
    , (j, S.FieldDecl (Just n) _) <- zip [0 :: Int ..] fs
    ]
  distinct what = go Set.empty
   where
    go _ [] = Right ()
    go seen (n : ns)
      | n.text `Set.member` seen =
          Left (DataError n.span (what <> " `" <> n.text <> "` appears twice"))
      | otherwise = go (Set.insert n.text seen) ns

builtinTypeNames :: [Text]
builtinTypeNames = ["Bool", "Num", "Vec", "Mat", "Tensor", "Point", "Scale"]

data DataEnv = DataEnv
  { codebase :: Codebase
  , self :: S.Name
  , params :: Map.Map Text VarId
  , paramNames :: [Text]
  }

-- | Conversion of written types, learning the parameters' kinds.
type Kinds = StateT (Map.Map Text Kind) (Either ResolveError)

bad :: S.TyExpr -> Text -> Kinds a
bad t msg = lift (Left (DataError t.span msg))

kindNoun :: Kind -> Text
kindNoun = \case
  KType -> "a type"
  KLen -> "a length"
  KShape -> "a shape"
  KDim -> "a dimension"

-- | A parameter used at a kind: record it, or report the clash.
useParam :: DataEnv -> S.TyExpr -> Text -> Kind -> Kinds VarId
useParam env t p k = do
  known <- gets (Map.lookup p)
  case known of
    Just k'
      | k' /= k ->
          bad
            t
            ( "parameter `"
                <> p
                <> "` is used both as "
                <> kindNoun k'
                <> " and as "
                <> kindNoun k
            )
    _ -> do
      modify (Map.insert p k)
      pure (Map.findWithDefault 0 p env.params)

tyType :: DataEnv -> S.TyExpr -> Kinds Type
tyType env t = case t.node of
  S.TyName n
    | Map.member n env.params -> TVar <$> useParam env t n KType
    | n == "Bool" -> pure TBool
    | n == "Num" -> pure numT
    | n `elem` builtinTypeNames -> bad t ("`" <> n <> "` needs its arguments")
    | otherwise -> applied env t n []
  S.TyApp hd args
    | Map.member hd.text env.params ->
        bad t ("parameter `" <> hd.text <> "` takes no arguments")
    | otherwise -> case (hd.text, args) of
        ("Num", [d]) -> TTensor SNil <$> tyDim env d
        ("Vec", [n]) -> (\l -> TTensor (SCons l SNil) dimOne) <$> tyLen env n
        ("Vec", [n, d]) -> (\l -> TTensor (SCons l SNil)) <$> tyLen env n <*> tyDim env d
        ("Mat", [m, n]) ->
          (\a b -> TTensor (SCons a (SCons b SNil)) dimOne)
            <$> tyLen env m
            <*> tyLen env n
        ("Mat", [m, n, d]) ->
          (\a b -> TTensor (SCons a (SCons b SNil)))
            <$> tyLen env m
            <*> tyLen env n
            <*> tyDim env d
        ("Tensor", [sh]) -> (`TTensor` dimOne) <$> tyShape env sh
        ("Tensor", [sh, d]) -> TTensor <$> tyShape env sh <*> tyDim env d
        ("Point", [a]) -> affine TPoint a
        ("Scale", [a]) -> affine TScale a
        (n, _)
          | n `elem` builtinTypeNames ->
              bad t ("`" <> n <> "` does not take these arguments")
        (n, _) -> applied env t n args
  S.TyTuple ts -> TTuple <$> mapM (tyType env) ts
  S.TyList a -> TList <$> tyType env a
  S.TyFun a b -> TFun <$> tyType env a <*> tyType env b
  S.TyInt _ -> bad t "a number is a length, not a type"
  S.TyBracket _ -> bad t "a bracket is a shape or a dimension, not a type"
 where
  -- `Point [K]` is a scalar point; `Point (Vec 3 [m])` a point over that space.
  affine mk a = case a.node of
    S.TyBracket _ -> mk SNil <$> tyDim env a
    S.TyName p | Map.member p env.params -> mk SNil <$> tyDim env a
    _ ->
      tyType env a >>= \case
        TTensor sh d -> pure (mk sh d)
        _ -> bad a "a point or scale is over a dimension or a tensor type"

-- | A declared type, or the one being declared, applied to its arguments.
applied :: DataEnv -> S.TyExpr -> Text -> [S.TyExpr] -> Kinds Type
applied env t n args
  | n == env.self.text = do
      arity (length env.paramNames)
      kinds <- mapM (gets . Map.findWithDefault KType) env.paramNames
      TData selfType <$> zipWithM (argOf env) kinds args
  | Just h <- lookupTypeName n env.codebase
  , Just def <- lookupTypeDef h env.codebase = do
      arity (length def.params)
      TData h <$> zipWithM (argOf env) (map snd def.params) args
  | otherwise = bad t ("unknown type `" <> n <> "`")
 where
  arity k =
    when (length args /= k)
      $ bad
        t
        ( "`"
            <> n
            <> "` takes "
            <> T.pack (show k)
            <> (if k == 1 then " argument" else " arguments")
            <> ", given "
            <> T.pack (show (length args))
        )

argOf :: DataEnv -> Kind -> S.TyExpr -> Kinds Arg
argOf env k a = case k of
  KType -> AType <$> tyType env a
  KLen -> ALen <$> tyLen env a
  KShape -> AShape <$> tyShape env a
  KDim -> ADim <$> tyDim env a

tyLen :: DataEnv -> S.TyExpr -> Kinds Len
tyLen env a = case a.node of
  S.TyInt k | k >= 0 -> pure (LLit (fromInteger k))
  S.TyName p | Map.member p env.params -> (`LVar` 0) <$> useParam env a p KLen
  _ -> bad a "a length is a number or a parameter"

tyShape :: DataEnv -> S.TyExpr -> Kinds Shape
tyShape env a = case a.node of
  S.TyBracket items -> foldr SCons SNil <$> mapM item items
  S.TyName p | Map.member p env.params -> SVar <$> useParam env a p KShape
  _ -> bad a "a shape is a list of lengths like [2, 3], or a parameter"
 where
  item = \case
    [(f, 1)] -> tyLen env f
    _ -> bad a "a shape is a list of lengths like [2, 3]"

{- | A dimension: a bracketed product of base units, units and parameters
with exponents (@[kg m^2 s^-2]@, @[m / s]@), a lone parameter, or @1@.
-}
tyDim :: DataEnv -> S.TyExpr -> Kinds Dim
tyDim env a = case a.node of
  S.TyBracket [] -> pure dimOne
  S.TyBracket [item] -> foldr dimMul dimOne <$> mapM factor item
  S.TyBracket _ -> bad a "a dimension is one product, not a list"
  S.TyInt 1 -> pure dimOne
  S.TyName p | Map.member p env.params -> dimVar <$> useParam env a p KDim
  _ ->
    bad
      a
      "a dimension is written in brackets, like [m s^-2], or is a parameter or 1"
 where
  factor (f, k) = case f.node of
    S.TyInt 1 -> pure dimOne
    S.TyName n
      | Map.member n env.params ->
          dimPow (fromInteger k) . dimVar <$> useParam env f n KDim
      | Just b <- lookup n [(baseSymbol b', b') | b' <- [minBound .. maxBound]] ->
          pure (dimPow (fromInteger k) (dimBase b))
      | isUnitName n env.codebase
      , Just r <- lookupName n env.codebase
      , Just (Forall [] (TTensor SNil d)) <- typeOf r env.codebase ->
          pure (dimPow (fromInteger k) d)
    _ ->
      bad
        f
        "a dimension is a product of base units (m kg s A K mol cd rad), units and parameters"

{- | A type written as a search query (design §7.3): every name that is not
a built-in type, a declared type, a base unit or a unit is a variable, of
the kind its position gives it.
-}
queryScheme :: Codebase -> S.TyExpr -> Either ResolveError Scheme
queryScheme cb t = do
  let vars = Set.toList (Set.filter isVar (names t))
      env =
        DataEnv
          { codebase = cb
          , self = S.Name t.span ""
          , params = Map.fromList (zip vars [0 ..])
          , paramNames = vars
          }
  (_, kinds1) <- runStateT (tyType env t) Map.empty
  (ty, kinds) <- runStateT (tyType env t) kinds1
  pure
    (Forall [(i, Map.findWithDefault KType v kinds) | (i, v) <- zip [0 ..] vars] ty)
 where
  isVar n =
    maybe False (isLower . fst) (T.uncons n)
      && n `notElem` builtinTypeNames
      && isNothing (lookupTypeName n cb)
      && n `notElem` [baseSymbol b | b <- [minBound .. maxBound]]
      && not (isUnitName n cb)
  names :: S.TyExpr -> Set Text
  names e = case e.node of
    S.TyName n -> Set.singleton n
    S.TyInt _ -> Set.empty
    S.TyApp hd args -> Set.insert hd.text (foldMap names args)
    S.TyTuple ts -> foldMap names ts
    S.TyList a -> names a
    S.TyFun a b -> names a <> names b
    S.TyBracket items -> foldMap (foldMap (names . fst)) items
