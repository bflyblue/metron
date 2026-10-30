{- | Binding groups (design §2.2, §6.2, §6.3, §7.1): dependency analysis,
cycle construction and hashing, type inference, and entry into the
codebase. Nothing from a group is stored unless the whole group checks.
-}
module Eval.Resolve (
  ResolveError (..),
  renderResolveError,
  LabelKind (..),
  isLabel,
  Qualified (..),
  qualifyWith,
  qualifyName,
  resolveName,
  shortestName,
  shortestNameOf,
  namespaceLabels,
  isNamespace,
  disjointness,
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
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (foldlM)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
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
      (fromMaybe n.span sp)
      ("in `" <> n.text <> "`: " <> msg)
  LintFailure n msg ->
    "internal error: elaboration of `"
      <> n.text
      <> "` produced ill-typed core: "
      <> msg
  DataError sp msg -> S.renderSpanError Nothing sp msg

-- Names and namespaces (design §7.6) ----------------------------------------------

{- | The kinds of label, each its own set of names: definitions and
constructors share one, as they share expressions.
-}
data LabelKind = TermLabel | TypeLabel | FieldLabel
  deriving stock (Eq, Show)

-- | Whether a full path is a label of a kind.
isLabel :: LabelKind -> Codebase -> Text -> Bool
isLabel kind cb n = case kind of
  TermLabel -> Map.member n cb.names || Map.member n cb.conNames
  TypeLabel -> Map.member n cb.typeNames
  FieldLabel -> Map.member n cb.fieldNames

-- | What a written name stands for.
data Qualified
  = -- | this full path
    Found Text
  | -- | two @use@d namespaces offer it, as these full paths
    Ambiguous [Text]
  | NotFound
  deriving stock (Eq, Show)

{- | The full path a written name stands for, given which full paths exist
(design §7.6). A leading dot writes an absolute path. Otherwise, in order:
the current namespace (@x@ is @current.x@), then the @use@d namespaces
(@u.x@ for each @use u@, and @u.y@ for @k.y@ under @use u as k@), which
must not offer it twice, then the root (@x@ itself), and last the
codebase's stored default @use@s (design §7.7), which must not offer it
twice either. So a root name shadows the library's @std.x@ that @use std@
offers, while a @use@ of the session still beats a root name. A local
binder comes before all of these, in the desugarer. A full path written
out resolves as itself at the root step, unless something nearer takes it
first.
-}
qualifyWith :: [S.Use] -> (Text -> Bool) -> S.Scope -> Text -> Qualified
qualifyWith stored exists scope written
  | Just p <- T.stripPrefix "." written = if exists p then Found p else NotFound
  | here : _ <-
      [ n
      | not (null scope.namespace)
      , let n = S.qualify scope.namespace written
      , exists n
      ] =
      Found here
  | otherwise = case offered scope.uses of
      [one] -> Found one
      many@(_ : _ : _) -> Ambiguous many
      []
        | exists written -> Found written
        | otherwise -> case offered stored of
            [one] -> Found one
            many@(_ : _ : _) -> Ambiguous many
            [] -> NotFound
 where
  offered = nubOrd . filter exists . mapMaybe through
  through u = case u.alias of
    Nothing -> Just (u.path <> "." <> written)
    Just k -> (\rest -> u.path <> "." <> rest) <$> T.stripPrefix (k <> ".") written

-- | 'qualifyWith' over the labels of one kind in a codebase.
qualifyName :: LabelKind -> S.Scope -> Codebase -> Text -> Qualified
qualifyName kind scope cb = qualifyWith cb.uses (isLabel kind cb) scope

{- | A free name in an expression, resolved through the scope: its full path
and what it names. Two @use@s that both offer it give 'AAmbiguous'.
-}
resolveName :: S.Scope -> Codebase -> Text -> Maybe (Text, Resolved)
resolveName scope cb written = case qualifyName TermLabel scope cb written of
  Found full -> (full,) <$> resolvedAt cb full
  Ambiguous fulls -> Just (written, AAmbiguous fulls)
  NotFound -> Nothing

-- | What a full path labels among definitions and constructors.
resolvedAt :: Codebase -> Text -> Maybe Resolved
resolvedAt cb n = case lookupName n cb of
  Just (Reference h i) -> Just (ATerm (Resolution (h, i) (isUnitName n cb) (isScaleName n cb)))
  Nothing -> case lookupConName n cb of
    Just (h, i)
      | Just def <- lookupTypeDef h cb ->
          let arity = length (def.constructors !! i)
           in Just
                ( AConstructor
                    ( ConInfo
                        (UserCon h i)
                        arity
                        [(UserCon h j, length fs) | (j, fs) <- zip [0 ..] def.constructors]
                        (fieldNamesOf h i arity cb)
                    )
                )
    _ -> Nothing

-- | The record field a full path labels.
fieldAt :: Codebase -> Text -> Maybe Resolved
fieldAt cb f = case lookupFieldName f cb of
  Just (h, i, j)
    | Just def <- lookupTypeDef h cb
    , let arity = length (def.constructors !! i) ->
        Just (AField (FieldInfo (UserCon h i) arity j (fieldNamesOf h i arity cb)))
  _ -> Nothing

{- | Free names resolve through the scope to whatever the codebase currently
binds (design §7.6). The resolver answers the three kinds of query of
'Resolver': a name, @.f@ for a field and @§p@ for an absolute path.
-}
resolverFor :: S.Scope -> Codebase -> Resolver
resolverFor = groupResolver Set.empty Set.empty

{- | A resolver inside a binding group: the group's names exist before they
are entered, and the members of the cycle being desugared are local
binders.
-}
groupResolver :: Set Text -> Set Text -> S.Scope -> Codebase -> Resolver
groupResolver group members scope cb query
  -- A field is looked up under its dot, the one way it is written (design §2.3).
  | Just f <- T.stripPrefix "." query = case qualifyName FieldLabel scope cb f of
      Found full -> fieldAt cb full
      Ambiguous fulls -> Just (AAmbiguous fulls)
      NotFound -> Nothing
  | otherwise =
      let written = maybe query ("." <>) (T.stripPrefix "§" query)
          exists n = isLabel TermLabel cb n || Set.member n group
       in case qualifyWith cb.uses exists scope written of
            Found full
              | Set.member full members -> Just (ALocal full)
              | full == query -> resolvedAt cb full
              | otherwise -> AQualified full <$> resolvedAt cb full
            Ambiguous fulls -> Just (AAmbiguous fulls)
            NotFound -> Nothing

{- | How a full path prints in a scope (design §7.6), as Unison prints names:
the shortest spelling that resolves back to the same label. Tried in order:
the last segment alone; the path relative to the current namespace; the
path relative to each @use@ (under its alias, if it has one), the
session's and then the codebase's stored ones (design §7.7); the full
path; and, only when the full path itself would resolve to something else
here, the absolute @.full.path@. At the root with no @use@, every root
name prints as itself, and so does every library name the stored @use
std@ reaches and no root name shadows.
-}
shortestName :: S.Scope -> Codebase -> Text -> Text
shortestName = shortestNameOf TermLabel

-- | 'shortestName' for a kind of label.
shortestNameOf :: LabelKind -> S.Scope -> Codebase -> Text -> Text
shortestNameOf kind scope cb n =
  case [c | c <- candidates, qualifyName kind scope cb c == Found n] of
    c : _ -> c
    -- Nothing spells it here (a name that is no longer a label): in full.
    [] -> n
 where
  candidates =
    [S.lastSegment n]
      ++ [ rel
         | not (null scope.namespace)
         , Just rel <- [T.stripPrefix (S.qualify scope.namespace "") n]
         ]
      ++ [ maybe rel (\k -> k <> "." <> rel) u.alias
         | u <- scope.uses ++ cb.uses
         , Just rel <- [T.stripPrefix (u.path <> ".") n]
         ]
      ++ [n, "." <> n]

-- | Every label of every kind, with what kind of thing it names.
allLabels :: Codebase -> [(Text, Text)]
allLabels cb =
  [(n, "definition") | n <- Map.keys cb.names]
    ++ [(n, "type") | n <- Map.keys cb.typeNames]
    ++ [(n, "constructor") | n <- Map.keys cb.conNames]
    ++ [(n, "field") | n <- Map.keys cb.fieldNames]

-- | The labels of every kind under a namespace, by full path, without duplicates.
namespaceLabels :: Codebase -> Text -> [Text]
namespaceLabels cb ns =
  Set.toList
    (Set.fromList [n | (n, _) <- allLabels cb, (ns <> ".") `T.isPrefixOf` n])

-- | Whether a path is a namespace: some label lies under it.
isNamespace :: Codebase -> Text -> Bool
isNamespace cb ns =
  any
    under
    [ Map.keys cb.names
    , Map.keys cb.typeNames
    , Map.keys cb.conNames
    , Map.keys cb.fieldNames
    ]
 where
  under = any ((ns <> ".") `T.isPrefixOf`)

{- | The rule that keeps the dot unambiguous (design §7.6): a name is never
both a label and a namespace. Given the labels a change adds (full path,
what it names, where it was written), the first that breaks the rule
against the codebase or the others, as a message at its span.
-}
disjointness :: Codebase -> [(Text, Text, S.Span)] -> Maybe (S.Span, Text)
disjointness cb new =
  case [(sp, msg) | (n, what, sp) <- new, Just msg <- [clash n what]] of
    x : _ -> Just x
    [] -> Nothing
 where
  labels =
    Map.fromListWith
      (\_ old -> old)
      (allLabels cb ++ [(n, what) | (n, what, _) <- new])
  clash n what
    | Just (k, _) <- Map.lookupGE (n <> ".") labels
    , (n <> ".") `T.isPrefixOf` k =
        Just ("`" <> n <> "` is a namespace; a " <> what <> " cannot have its name")
    | p : _ <- [p | p <- properPrefixes n, Map.member p labels] =
        Just
          ( "`"
              <> p
              <> "` is a "
              <> Map.findWithDefault "name" p labels
              <> "; it cannot also be a namespace, as `"
              <> n
              <> "` would make it"
          )
    | otherwise = Nothing
  properPrefixes n =
    let segs = T.splitOn "." n
     in [T.intercalate "." (take k segs) | k <- [1 .. length segs - 1]]

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
  -- A name is never both a label and a namespace (design §7.6).
  case disjointness cb0 (concatMap newLabels decls) of
    Just (sp, msg) -> Left (DataError sp msg)
    Nothing -> pure ()
  -- Data declarations first, in order: the definitions may use their constructors.
  cb1 <-
    foldlM (\cb (s, d) -> enterData s cb d) cb0 [(s, d) | S.DData s d <- decls]
  let bindings = [(s, b) | S.DBind s b <- decls]
      groupNames = Set.fromList [b.name.text | (_, b) <- bindings]
      exists n = isLabel TermLabel cb1 n || Set.member n groupNames
      -- Dependencies by full path: a name written in the group resolves
      -- through its scope to the group's own names first (design §7.6).
      dependsOn (s, b) =
        Set.toList
          ( Set.fromList
              [ full
              | w <- Set.toList (freeNames (asLambda b))
              , Found full <- [qualifyWith cb1.uses exists s w]
              , Set.member full groupNames
              ]
          )
      nodes = [(sb, (snd sb).name.text, dependsOn sb) | sb <- bindings]
  foldlM (enterComponent groupNames) cb1 (stronglyConnComp nodes)
 where
  newLabels = \case
    S.DBind _ b -> [(b.name.text, "definition", b.name.span)]
    S.DData _ d ->
      (d.name.text, "type", d.name.span)
        : [(c.text, "constructor", c.span) | (c, _) <- d.constructors]
        ++ [ (n.text, "field", n.span)
           | (_, fs) <- d.constructors
           , S.FieldDecl (Just n) _ <- fs
           ]

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

{- | Enter one component. A definition's declared uncertainties are labelled
with its full path (design §3.2.4), so that @lab.offset = 1 ± 0.1@ and
@field.offset = 1 ± 0.1@ are two measurements, not one.
-}
enterComponent ::
  Set Text -> Codebase -> SCC (S.Scope, S.Binding) -> Either ResolveError Codebase
enterComponent group cb = \case
  AcyclicSCC (scope, b) -> do
    (term, prov) <-
      either
        (Left . Desugar)
        Right
        ( desugarDefinition
            b.name.text
            (groupResolver group Set.empty scope cb)
            (asLambda b)
        )
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
  CyclicSCC bs -> enterCycle group cb bs

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
enterCycle ::
  Set Text -> Codebase -> [(S.Scope, S.Binding)] -> Either ResolveError Codebase
enterCycle group cb sbs = do
  ordering <- mapM (\sb -> (,sb) <$> placeholderHashOf sb) sbs
  let sortedScoped = map snd (sortOn fst ordering)
      sorted = map snd sortedScoped
  case vecFromList sortedScoped of
    SomeVec members -> do
      let ctx = vecAppend (vecMap ((.name.text) . snd) members) VNil
      desugared <- vecTraverse (desugarOne ctx) members
      let bodies = vecMap fst desugared
          provs = vecToList (vecMap snd desugared)
          cycleTerm = Cycle (vecMap (Hint . (.name.text) . snd) members) bodies
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
  -- The members are local binders by their full paths, found through each
  -- member's own scope (design §7.6).
  memberNames = Set.fromList [b.name.text | (_, b) <- sbs]
  desugarOne ::
    Vec k Text -> (S.Scope, S.Binding) -> Either ResolveError (Term k, Provenance)
  desugarOne ctx (scope, b) =
    either
      (Left . Desugar)
      Right
      ( D.desugarMember
          b.name.text
          (groupResolver group memberNames scope cb)
          ctx
          (asLambda b)
      )

  placeholderHashOf :: (S.Scope, S.Binding) -> Either ResolveError Hash
  placeholderHashOf sb = case vecFromList [b.name.text | (_, b) <- sbs] of
    SomeVec ns -> do
      (t, _) <- desugarOne (vecAppend ns VNil) sb
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

{- | Names an expression mentions that are not bound inside it. A field chain
on a free name also mentions each of its dotted prefixes, any of which may
be a qualified name (design §7.6).
-}
freeNames :: S.Expr -> Set Text
freeNames = go Set.empty
 where
  chain ex = case ex.node of
    S.Var x -> Just (x, [])
    S.FieldOf a f -> (\(x, fs) -> (x, fs ++ [f])) <$> chain a
    _ -> Nothing
  go bound e = case e.node of
    S.FieldOf _ _
      | Just (x, fs) <- chain e
      , x `Set.notMember` bound ->
          Set.fromList [T.intercalate "." (x : take k fs) | k <- [0 .. length fs]]
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
enterData :: S.Scope -> Codebase -> S.DataDecl -> Either ResolveError Codebase
enterData scope cb decl = do
  distinct "parameter" decl.params
  distinct "constructor" (map fst decl.constructors)
  distinct "field" (map fst fieldLabels)
  -- Field names make a record: a type of one constructor, so that @r.f@ is total.
  case (decl.constructors, fieldLabels) of
    (_ : _ : _, (n, _) : _) ->
      Left (DataError n.span "field names need a type with one constructor")
    _ -> pure ()
  when (S.lastSegment decl.name.text `elem` builtinTypeNames)
    $ Left
      ( DataError
          decl.name.span
          ("`" <> S.lastSegment decl.name.text <> "` is a built-in type")
      )
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
          -- The declared full path (design §2.3, §7.6): @a.Body@ and
          -- @b.Body@ with the same fields are two types.
          ( if decl.structural
              then structuralLabel
              else Owner decl.name.text
          )
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
      , scope = scope
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
  , scope :: S.Scope
  -- ^ where the type is written: its names resolve through this (design §7.6)
  , self :: S.Name
  -- ^ the type being declared, by its full path
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
  | resolved == Found env.self.text = do
      arity (length env.paramNames)
      kinds <- mapM (gets . Map.findWithDefault KType) env.paramNames
      TData selfType <$> zipWithM (argOf env) kinds args
  | Found full <- resolved
  , Just h <- lookupTypeName full env.codebase
  , Just def <- lookupTypeDef h env.codebase = do
      arity (length def.params)
      TData h <$> zipWithM (argOf env) (map snd def.params) args
  | Ambiguous fulls <- resolved =
      bad
        t
        ( "`"
            <> n
            <> "` is both "
            <> T.intercalate " and " (map (\f -> "`" <> f <> "`") fulls)
            <> "; write one of them"
        )
  | otherwise = bad t ("unknown type `" <> n <> "`")
 where
  -- The type's own name exists before it is entered.
  resolved =
    qualifyWith
      env.codebase.uses
      (\x -> x == env.self.text || isLabel TypeLabel env.codebase x)
      env.scope
      n
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
      | Found u <- qualifyName TermLabel env.scope env.codebase n
      , isUnitName u env.codebase
      , Just r <- lookupName u env.codebase
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
queryScheme :: S.Scope -> Codebase -> S.TyExpr -> Either ResolveError Scheme
queryScheme scope cb t = do
  let vars = Set.toList (Set.filter isVar (names t))
      env =
        DataEnv
          { codebase = cb
          , scope = scope
          , self = S.Name t.span ""
          , params = Map.fromList (zip vars [0 ..])
          , paramNames = vars
          }
  (_, kinds1) <- runStateT (tyType env t) Map.empty
  (ty, kinds) <- runStateT (tyType env t) kinds1
  pure
    (Forall [(i, Map.findWithDefault KType v kinds) | (i, v) <- zip [0 ..] vars] ty)
 where
  -- Names resolve through the scope (design §7.6).
  isVar n =
    maybe False (isLower . fst) (T.uncons n)
      && n `notElem` builtinTypeNames
      && qualifyName TypeLabel scope cb n == NotFound
      && n `notElem` [baseSymbol b | b <- [minBound .. maxBound]]
      && not (isUnit n)
  isUnit n = case qualifyName TermLabel scope cb n of
    Found u -> isUnitName u cb
    _ -> False
  names :: S.TyExpr -> Set Text
  names e = case e.node of
    S.TyName n -> Set.singleton n
    S.TyInt _ -> Set.empty
    S.TyApp hd args -> Set.insert hd.text (foldMap names args)
    S.TyTuple ts -> foldMap names ts
    S.TyList a -> names a
    S.TyFun a b -> names a <> names b
    S.TyBracket items -> foldMap (foldMap (names . fst)) items
