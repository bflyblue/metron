{- | Surface AST to Core (design §2.9), with a provenance table (§4.7).

Desugaring is total and local: no step needs type information. Bound
variables become de Bruijn indices through a context of names; primitives
become saturated 'PrimApp' nodes, eta-expanded when used with too few
arguments; operators, sections, composition and the quantity rule all
reduce to these. Every Core node records the span of the surface node that
produced it, keyed by its path from the root.
-}
module Eval.Desugar (
  Path,
  Provenance (..),
  provenanceAt,
  Resolver,
  noResolver,
  DesugarError (..),
  desugarClosed,
  desugarDefinition,
  desugarMember,
  desugarMarked,
  ascriptionMarker,
  ascriptionPath,
  unmarked,
  Resolution (..),
  Resolved (..),
  ConInfo (..),
  FieldInfo (..),
  desugarIn,
  renderDesugarError,
) where

import Control.Monad (when, zipWithM)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Syntax qualified as S
import Eval.TCore (baseUnit)
import Eval.Type (conText)

-- | Child positions from the root of a Core term.
type Path = [Int]

{- | Where each Core node came from, and advice attached to some spans for the
type error that may land there (design §4.7).
-}
data Provenance = Provenance
  { spans :: Map Path S.Span
  , hints :: Map S.Span Text
  , ascriptions :: [(Text, S.TyExpr)]
  {- ^ the ascriptions met (design §4.8), in order, each with the name of
  the marker that stands for it in a term desugared for checking them
  ('desugarMarked')
  -}
  }

emptyProvenance :: Provenance
emptyProvenance = Provenance Map.empty Map.empty []

-- | The span of a Core node, and the hint for an error there, if any.
provenanceAt :: Path -> Provenance -> Maybe (S.Span, Maybe Text)
provenanceAt path prov = (\sp -> (sp, Map.lookup sp prov.hints)) <$> Map.lookup path prov.spans

data DesugarError
  = UnknownName S.Span Text
  | -- | a special form applied to the wrong kind of argument
    BadSpecialForm S.Span Text
  deriving stock (Eq, Show)

renderDesugarError :: DesugarError -> Text
renderDesugarError = \case
  UnknownName sp n -> at sp ("unknown name `" <> n <> "`")
  BadSpecialForm sp msg -> at sp msg
 where
  at sp msg = T.pack (show sp.from.line) <> ":" <> T.pack (show sp.from.col) <> ": " <> msg

{- | How free names resolve to codebase references (hash and optional cycle
index). Names bound locally shadow these; these shadow primitives.
-}

{- | What a free name resolves to, and whether it was declared a display unit
(design §3.2.12), which is what the quantity rule accepts (§2.6).
-}
data Resolution = Resolution {ref :: (Hash, Maybe Int), isUnit :: Bool, isScale :: Bool}

{- | A declared constructor (design §2.3): the reference, its arity, the
whole constructor table of its type, for case analysis, and the labels of
its fields by position, for a record built with it (design §7.6).
-}
data ConInfo = ConInfo
  { con :: ConRef
  , arity :: Int
  , siblings :: [(ConRef, Int)]
  , labels :: [Maybe Text]
  }

{- | A record field (design §2.3), resolved under its dotted name: the
constructor it belongs to, that constructor's arity, the field's position,
and the names of all the constructor's fields, for hints.
-}
data FieldInfo = FieldInfo {con :: ConRef, arity :: Int, index :: Int, names :: [Maybe Text]}

data Resolved
  = ATerm Resolution
  | AConstructor ConInfo
  | AField FieldInfo
  | {- | What a name written otherwise resolves to, under its full path
    (design §7.6): @period@ inside @namespace orbital@ is @orbital.period@.
    -}
    AQualified Text Resolved
  | -- | A member of the cycle being desugared, by its full path: a local binder.
    ALocal Text
  | -- | A name two @use@d namespaces both offer, as their full paths.
    AAmbiguous [Text]

{- | A name as written, looked up: @x@ through the scope, @.f@ the field @f@
through the scope, and @§p@ the absolute path @p@, written @.p@ (design
§7.6).
-}
type Resolver = Text -> Maybe Resolved

noResolver :: Resolver
noResolver _ = Nothing

{- | What the desugarer reads: how free names resolve, and the label every
declared uncertainty gets, which is the enclosing definition's name until a
@#label@ overrides it (design §3.2.4).
-}
data Env = Env
  { resolve :: Resolver
  , owner :: Label
  , marking :: Maybe Text
  {- ^ when checking ascriptions, the prefix of their markers' tags
  ('desugarMarked'); otherwise an ascription desugars to its expression
  -}
  }

-- | Paths are built in reverse (innermost first) and reversed when stored.
type M = ReaderT Env (StateT Provenance (Either DesugarError))

type Ctx n = Vec n Text

-- | An expression that belongs to no definition.
desugarClosed :: Resolver -> S.Expr -> Either DesugarError (Term Z, Provenance)
desugarClosed = desugarDefinition ""

-- | The body of the definition with the given name.
desugarDefinition ::
  Text -> Resolver -> S.Expr -> Either DesugarError (Term Z, Provenance)
desugarDefinition name resolve = desugarMember name resolve VNil

-- | Desugar under a context of already-bound names (innermost first).
desugarIn ::
  Resolver -> Ctx n -> S.Expr -> Either DesugarError (Term n, Provenance)
desugarIn = desugarMember ""

-- | A member of a binding group, by name, under the group's context.
desugarMember ::
  Text -> Resolver -> Ctx n -> S.Expr -> Either DesugarError (Term n, Provenance)
desugarMember name resolve ctx e =
  runStateT
    (runReaderT (desugar [] ctx e) (Env resolve (Owner name) Nothing))
    emptyProvenance

{- | A member desugared for checking its ascriptions (design §4.8): each
@(e :: type)@ becomes a marker, the primitive application
@§ascribe<tag>:<k> e@, which inference reads as "unify @e@'s type with the
ascription named so" and elaborates to @e@'s own typed term. The marker
keeps the ascription's span and @e@ is one level down, so an error in the
ascription points at it. The term exists only to be checked: it is never
hashed, stored or run, and the term of 'desugarMember' is what the
definition is. The tag tells the members of a cycle apart.
-}
desugarMarked ::
  Text ->
  Text ->
  Resolver ->
  Ctx n ->
  S.Expr ->
  Either DesugarError (Term n, Provenance)
desugarMarked tag name resolve ctx e =
  runStateT
    (runReaderT (desugar [] ctx e) (Env resolve (Owner name) (Just tag)))
    emptyProvenance

-- | The name of an ascription marker starts so (design §4.8).
ascriptionMarker :: Text
ascriptionMarker = "§ascribe"

{- | The provenance key of the @k@th ascription's span in a term desugared
with markers: a path of one negative step, which no node has, so that an
error in the ascription is reported at it however the paths of the nodes
around it are laid out. In a cycle the member's index goes before it.
-}
ascriptionPath :: Int -> Int
ascriptionPath k = negate (k + 1)

-- | The expression under any ascription markers.
unmarked :: Term n -> Term n
unmarked = \case
  PrimApp p [a] | ascriptionMarker `T.isPrefixOf` p -> unmarked a
  t -> t

failWith :: DesugarError -> M a
failWith = lift . lift . Left

record :: Path -> S.Span -> M ()
record path sp = lift (modify' (\p -> p{spans = Map.insert (reverse path) sp p.spans}))

-- | Advice for a type error at a span.
hintAt :: S.Span -> Text -> M ()
hintAt sp msg = lift (modify' (\p -> p{hints = Map.insert sp msg p.hints}))

lookupCtx :: Text -> Ctx n -> Maybe (Fin n)
lookupCtx x = \case
  VNil -> Nothing
  VCons y ys
    | x == y -> Just FZ
    | otherwise -> FS <$> lookupCtx x ys

{- | The outermost binding of a name in the context: where the members of a
cycle sit, below every local binder.
-}
lookupCtxOuter :: Text -> Ctx n -> Maybe (Fin n)
lookupCtxOuter x = \case
  VNil -> Nothing
  VCons y ys -> case lookupCtxOuter x ys of
    Just i -> Just (FS i)
    Nothing
      | x == y -> Just FZ
      | otherwise -> Nothing

{- | A free name as written, looked up: its full path (design §7.6) and what
it names. A leading dot writes an absolute name.
-}
resolveWritten :: Text -> M (Maybe (Text, Resolved))
resolveWritten x = asks (\env -> unwrap <$> env.resolve query)
 where
  bare = fromMaybe x (T.stripPrefix "." x)
  query = if bare == x then x else "§" <> bare
  unwrap = \case
    AQualified full r -> (full, r)
    r -> (bare, r)

-- | Two @use@d namespaces offer the name (design §7.6).
ambiguous :: S.Span -> Text -> [Text] -> M a
ambiguous sp x fulls =
  failWith
    ( BadSpecialForm
        sp
        ( "`"
            <> x
            <> "` is both "
            <> listed (map (\f -> "`" <> f <> "`") fulls)
            <> "; write one of them"
        )
    )
 where
  listed = \case
    [] -> ""
    [a] -> a
    xs -> T.intercalate ", " (init xs) <> " and " <> last xs

{- | A field chain on a free name whose longest dotted prefix names a
definition or a constructor is a qualified reference (design §7.6):
@orbital.period@ is the definition, not the field @period@ of @orbital@.
What follows that prefix stays field access. Anything else comes back as
it was.
-}
qualifiedChain :: Ctx n -> S.Expr -> M S.Expr
qualifiedChain ctx e = case chain e of
  Just (x, fields@(_ : _)) | Nothing <- lookupCtx x ctx -> go fields (length fields)
  _ -> pure e
 where
  -- The name at the root and each field with the span of the access up to it.
  chain :: S.Expr -> Maybe (Text, [(Text, S.Span)])
  chain ex = case ex.node of
    S.Var x -> Just (x, [])
    S.FieldOf a f -> (\(x, fs) -> (x, fs ++ [(f, ex.span)])) <$> chain a
    _ -> Nothing
  go fields k
    | k < 1 = pure e
    | otherwise = do
        let (taken, rest) = splitAt k fields
            root = maybe "" fst (chain e)
            written = T.intercalate "." (root : map fst taken)
            sp = snd (last taken)
        found <- resolveWritten written
        case snd <$> found of
          Just (AField _) -> go fields (k - 1)
          Just _ ->
            pure
              ( foldl
                  (\acc (f, fsp) -> S.Expr fsp (S.FieldOf acc f))
                  (S.Expr sp (S.Var written))
                  rest
              )
          Nothing -> go fields (k - 1)

{- | A name that no user identifier can clash with, for binders the desugarer
introduces.
-}
fresh :: Text -> Int -> Text
fresh tag j = "§" <> tag <> T.pack (show j)

desugar :: Path -> Ctx n -> S.Expr -> M (Term n)
desugar path ctx e = do
  record path e.span
  case e.node of
    -- An ascription is not in Core (design §4.8): the expression is desugared
    -- in its place. Only for checking is it a marker, which inference reads.
    S.Ascribe inner t -> do
      k <- lift (gets (length . (.ascriptions)))
      tag <- asks (.marking)
      let marker = ascriptionMarker <> fromMaybe "" tag <> ":" <> T.pack (show k)
      lift (modify' (\p -> p{ascriptions = p.ascriptions ++ [(marker, t)]}))
      case tag of
        Nothing -> desugar path ctx inner
        Just _ -> do
          -- Where an error in the ascription is reported: its own key, a
          -- negative path no node has ('ascriptionPath').
          record [ascriptionPath k] e.span
          (\inner' -> PrimApp marker [inner']) <$> desugar (0 : path) ctx inner
    S.Num r -> pure (Lit (LTensor ([], [r])))
    S.Bool b -> pure (Con (Builtin (if b then "True" else "False")) [])
    S.Tuple es ->
      Con (Builtin "Tuple") <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] es
    S.List es ->
      foldr
        ( \(i, a) rest -> (\x r -> Con (Builtin "Cons") [x, r]) <$> desugar (i : path) ctx a <*> rest
        )
        (pure (Con (Builtin "Nil") []))
        (zip [0 ..] es)
    S.CaseOf scrut alts -> caseOf path ctx e.span scrut alts
    S.Var x -> headApp path ctx e x []
    S.App f a -> do
      let (hd0, args) = spine e
      -- A qualified head, @orbital.period a@, is applied as a name is.
      hd <- qualifiedChain ctx hd0
      if hd /= hd0
        then
          desugar
            path
            ctx
            (foldl (\g x -> S.Expr (S.spanUnion g.span x.span) (S.App g x)) hd args)
        else do
          quantityHints ctx hd args
          case hd.node of
            S.Var x | Nothing <- lookupCtx x ctx -> do
              bound <- resolveWritten x
              case snd <$> bound of
                -- A codebase name, or a member of the cycle: ordinary application.
                Just (ATerm _) -> App <$> desugar (0 : path) ctx f <*> desugar (1 : path) ctx a
                Just (ALocal _) -> App <$> desugar (0 : path) ctx f <*> desugar (1 : path) ctx a
                -- A primitive, constructor (or unknown): saturation and eta rules apply.
                _ -> headApp path ctx hd x args
            _ -> App <$> desugar (0 : path) ctx f <*> desugar (1 : path) ctx a
    S.Lam names body -> lams path ctx e.span names body
    S.Let n params rhs body ->
      Let (Hint n.text)
        <$> lams (0 : path) ctx rhs.span params rhs
        <*> desugar (1 : path) (VCons n.text ctx) body
    -- if is a case on Bool (design §5.1): alternatives in canonical order.
    S.If c t f -> do
      c' <- desugar (0 : path) ctx c
      t' <- desugar (1 : path) ctx t
      f' <- desugar (2 : path) ctx f
      pure (Case c' [Alt (Builtin "False") VNil f', Alt (Builtin "True") VNil t'])
    S.BinOp op a b -> case op of
      S.PlusMinus k ->
        asks (Uncertain k . (.owner))
          <*> desugar (0 : path) ctx a
          <*> desugar (1 : path) ctx b
      -- A point moves to another scale; everything else to a display unit.
      S.To -> do
        scaleName <- isScaleName ctx b
        prim (if scaleName then "toScale" else "to") [a, b]
      S.PAdd -> prim "pointAdd" [a, b]
      S.Cons ->
        (\x r -> Con (Builtin "Cons") [x, r])
          <$> desugar (0 : path) ctx a
          <*> desugar (1 : path) ctx b
      S.PSub -> prim "pointSub" [a, b]
      S.Compose ->
        -- f ∘ g  =  \x -> f (g x)
        let x = fresh "c" 0
            var = S.Expr e.span (S.Var x)
         in desugar
              path
              ctx
              (synthLam e.span x (S.Expr e.span (S.App a (S.Expr e.span (S.App b var)))))
      S.Infix f ->
        desugar
          path
          ctx
          (S.Expr e.span (S.App (S.Expr e.span (S.App (S.Expr a.span (S.Var f)) a)) b))
      -- The cross product is a prelude definition, not a primitive, so its
      -- operator resolves through the name like a backticked function.
      S.Cross ->
        desugar
          path
          ctx
          ( S.Expr
              e.span
              (S.App (S.Expr e.span (S.App (S.Expr e.span (S.Var "cross")) a)) b)
          )
      -- Juxtaposition is for units (§2.6): 5 km, 3 (m/s), [1, 0, 0] km.
      S.Scale -> do
        scaleName <- isScaleName ctx b
        ok <- unitExpr ctx b
        if scaleName
          then -- 20 degC: a point on the scale (design §3.6).
            prim "pointOn" [b, a]
          else
            if ok
              then prim "outer" [a, b]
              else
                failWith
                  ( BadSpecialForm
                      b.span
                      ( ( case b.node of
                            S.Var x -> "`" <> x <> "` is not a unit"
                            _ -> "this is not a unit expression"
                        )
                          <> ": a value next to a literal must be a unit (5 km, 3 (m/s)); write the `*`"
                      )
                  )
      _ -> prim (opPrim op) [a, b]
    -- Negating a constant is a negative constant, so that `-3` and a literal
    -- negative three are one term with one hash (core.md §6: constants are
    -- canonical). Anything else is the primitive.
    S.Neg a -> do
      a' <- desugar (0 : path) ctx a
      pure $ case a' of
        Lit (LTensor (dims, rs)) -> Lit (LTensor (dims, map negate rs))
        _ -> PrimApp "neg" [a']
    S.Pow a n -> (`Pow` n) <$> desugar (0 : path) ctx a
    S.SectionL op a ->
      -- (op a)  =  \x -> x op a
      let x = fresh "s" 0
       in desugar
            path
            ctx
            (synthLam e.span x (S.Expr e.span (S.BinOp op (S.Expr e.span (S.Var x)) a)))
    S.SectionR a op ->
      -- (a op)  =  \x -> a op x
      let x = fresh "s" 0
       in desugar
            path
            ctx
            (synthLam e.span x (S.Expr e.span (S.BinOp op a (S.Expr e.span (S.Var x)))))
    -- A bracket literal whose elements are all constants of one shape folds
    -- into a single constant; otherwise it is a construction (core.md §5).
    -- A #label names the measurement declared by the ± or noise it follows:
    -- the label replaces the owner for that subtree.
    S.Labelled l inner
      | declaresUncertainty inner ->
          local (\env -> env{owner = Tag l}) (desugar path ctx inner)
      | otherwise ->
          failWith
            ( BadSpecialForm
                inner.span
                ("a #label must follow ±, ±σ, noise or gauss; `#" <> l <> "` labels nothing here")
            )
    S.Vec es -> do
      elems <- zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] es
      pure (foldConstant elems)
    S.Proj a i -> (`Proj` i) <$> desugar (0 : path) ctx a
    -- A slice is the primitive applied to its literal axis and position
    -- (design §2.10), whatever `slice` names in scope.
    S.Slice a k i ->
      let lit n = S.Expr e.span (S.Num (fromIntegral n))
       in prim "slice" [lit k, lit i, a]
    -- A field is a case on the record's one constructor (design §2.3), unless
    -- the chain is a qualified name (design §7.6).
    S.FieldOf a f -> do
      e' <- qualifiedChain ctx e
      if e' /= e
        then desugar path ctx e'
        else do
          resolved <- asks (\env -> env.resolve ("." <> f))
          case resolved of
            Just (AField info) -> do
              a' <- desugar (0 : path) ctx a
              case vecFromList [if j == info.index then f else "_" | j <- [0 .. info.arity - 1]] of
                SomeVec hs -> case fieldVar hs ctx info.index of
                  Just v -> pure (Case a' [Alt info.con (vecMap Hint hs) (Var v)])
                  Nothing -> failWith (BadSpecialForm e.span ("field " <> f <> " is out of range"))
            Just (AAmbiguous fulls) -> ambiguous e.span f fulls
            _ -> failWith (BadSpecialForm e.span ("unknown field `" <> f <> "`"))
    S.Record hd0 fields -> do
      hd <- qualifiedChain ctx hd0
      recordExpr path ctx e hd fields
 where
  prim p args = PrimApp p <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args
  synthLam sp x body = S.Expr sp (S.Lam [S.Name sp x] body)

-- | @[Lit, Lit, …]@ of one shape becomes one 'Lit' of the stacked shape.
foldConstant :: [Term n] -> Term n
foldConstant elems = case traverse constant elems of
  Just ((dims, _) : rest)
    | all ((== dims) . fst) rest ->
        Lit (LTensor (length elems : dims, concatMap snd (constants elems)))
  _ -> Pack elems
 where
  constant = \case
    Lit (LTensor (dims, rs)) -> Just (dims, rs)
    _ -> Nothing
  constants = foldr (\e acc -> maybe acc (: acc) (constant e)) []

-- | The head and arguments of an application spine.
spine :: S.Expr -> (S.Expr, [S.Expr])
spine = go []
 where
  go acc e = case e.node of
    S.App f a -> go (a : acc) f
    _ -> (e, acc)

{- | A name in head position applied to arguments: a bound variable, a
primitive (saturated, eta-expanded, or over-applied), or unknown.
-}
headApp :: Path -> Ctx n -> S.Expr -> Text -> [S.Expr] -> M (Term n)
headApp path ctx hd x args = case lookupCtx x ctx of
  Just i -> applyAll path ctx (\_ -> pure (Var i)) args
  Nothing -> do
    found <- resolveWritten x
    case snd <$> found of
      -- The reference keeps the full path it was written as (design §7.6).
      Just (ATerm r) ->
        let (h, idx) = r.ref
            full = maybe x fst found
         in applyAll path ctx (\_ -> pure (Ref h idx (Hint full))) args
      Just (ALocal full) -> case lookupCtxOuter full ctx of
        Just i -> applyAll path ctx (\_ -> pure (Var i)) args
        Nothing -> failWith (UnknownName hd.span x)
      Just (AAmbiguous fulls) -> ambiguous hd.span x fulls
      Just (AQualified _ _) -> failWith (UnknownName hd.span x)
      -- A declared constructor applies like a primitive: saturated, eta-expanded or over-applied.
      Just (AConstructor info)
        | length args == info.arity -> saturated path ctx (Con info.con) args
        | length args < info.arity ->
            eta path ctx hd.span (Builder (Con info.con)) args (info.arity - length args)
        | otherwise ->
            applyAll
              path
              ctx
              (\p -> saturated p ctx (Con info.con) (take info.arity args))
              (drop info.arity args)
      Just (AField _) ->
        failWith
          ( BadSpecialForm
              hd.span
              ("`" <> x <> "` is a field; write it after a value, as in r." <> x)
          )
      -- noise n and gauss n take a literal count (design §3.2.5): the
      -- number of nudges is part of the type.
      Nothing
        | Just k <- lookup x [("noise", Bound), ("gauss", Stat)] -> case args of
            [a]
              | S.Num n <- a.node
              , denominator n == 1
              , n >= 0 ->
                  asks (\r -> Noise k r.owner (numerator n))
            _ ->
              failWith
                ( BadSpecialForm
                    hd.span
                    (x <> " takes one argument, a literal natural number: the count of nudges")
                )
      -- contract i j, permute [p…] and slice k i take literal index
      -- positions (design §4.2): like a projection's, the positions are part
      -- of the type. The tensor argument may be left off (eta), the
      -- positions may not.
      Nothing
        | Just (positions, rule) <- indexedForm x -> do
            when (length args < positions) (failWith (BadSpecialForm hd.span rule))
            term <- applyPrim (positions + 1) (Builder (PrimApp x))
            case indexProblem x (fromMaybe [] (primLiterals term)) of
              Nothing -> pure term
              Just (i, msg) ->
                failWith (BadSpecialForm (maybe hd.span (.span) (nthArg i args)) msg)
      Nothing ->
        asks (.owner) >>= \l -> case specialForm l x of
          Nothing -> do
            asField <- asks (\env -> env.resolve ("." <> x))
            case asField of
              Just (AField _) ->
                failWith
                  ( BadSpecialForm
                      hd.span
                      ("`" <> x <> "` is a field; write it after a value, as in r." <> x)
                  )
              _ -> failWith (UnknownName hd.span x)
          Just (arity, builder) -> applyPrim arity builder
 where
  applyPrim arity (Builder build)
    | length args == arity = saturated path ctx build args
    | length args < arity =
        eta path ctx hd.span (Builder build) args (arity - length args)
    | otherwise =
        applyAll
          path
          ctx
          (\p -> saturated p ctx build (take arity args))
          (drop arity args)
  nthArg i as = case drop i as of
    a : _ -> Just a
    [] -> Nothing

{- | The primitives whose leading arguments are literal index positions
(design §4.2): how many such arguments, and the rule to quote when they are
missing.
-}
indexedForm :: Text -> Maybe (Int, Text)
indexedForm = \case
  "contract" ->
    Just
      ( 2
      , "contract takes two literal positions and then a tensor: contract i j t, with i and j distinct natural numbers"
      )
  "permute" ->
    Just
      ( 1
      , "permute takes a literal permutation and then a tensor: permute [p0, …, pk-1] t, with the p a permutation of 0 .. k-1 and k ≥ 1"
      )
  "slice" ->
    Just
      ( 2
      , "slice takes a literal axis and a literal position and then a tensor: slice k i t, with k and i natural numbers, as in slice 1 0 m (written m._.0)"
      )
  _ -> Nothing

{- | The literal arguments of the primitive application a desugared
@contract@, @permute@ or @slice@ built, under the binders of an eta
expansion or the applications of an over-application: 'Nothing' for an
argument that is not a constant.
-}
primLiterals :: Term n -> Maybe [Maybe Lit]
primLiterals = \case
  PrimApp _ as -> Just [case unmarked a of Lit l -> Just l; _ -> Nothing | a <- as]
  Lam _ b -> primLiterals b
  App f _ -> primLiterals f
  _ -> Nothing

{- | What is wrong with the index arguments of @contract@, @permute@ or
@slice@, as the argument position and a message; 'Nothing' when they are
literal naturals, two distinct ones for @contract@, a permutation of
@0 .. k-1@ for @permute@.
-}
indexProblem :: Text -> [Maybe Lit] -> Maybe (Int, Text)
indexProblem name lits = case (name, lits) of
  ("contract", li : lj : _) -> case (natural li, natural lj) of
    (Nothing, _) -> Just (0, notNatural)
    (_, Nothing) -> Just (1, notNatural)
    (Just i, Just j)
      | i == j ->
          Just
            ( 1
            , "contract pairs two different positions, not position "
                <> tshowI i
                <> " with itself: contract i j t, with i and j distinct"
            )
      | otherwise -> Nothing
  ("permute", lp : _) -> case lp of
    Just (LTensor ([k], rs))
      | k >= 1
      , all isNatural rs
      , all ((`elem` rs) . fromIntegral) [0 .. k - 1] ->
          Nothing
      | k >= 1 ->
          Just
            ( 0
            , "permute "
                <> renderList rs
                <> " is not a permutation of 0 .. "
                <> tshowI (k - 1)
                <> ": each position from 0 to "
                <> tshowI (k - 1)
                <> " must appear exactly once"
            )
    _ ->
      Just
        ( 0
        , "permute takes a literal vector of natural numbers, a permutation of 0 .. k-1 with k ≥ 1: permute [1, 0] t"
        )
  ("slice", lk : li : _) -> case (natural lk, natural li) of
    (Nothing, _) -> Just (0, sliceNotNatural)
    (_, Nothing) -> Just (1, sliceNotNatural)
    _ -> Nothing
  _ -> Nothing
 where
  notNatural =
    "the positions of contract must be literal natural numbers: contract i j t, as in contract 0 1 t"
  sliceNotNatural =
    "the axis and position of slice must be literal natural numbers: slice k i t, as in slice 1 0 t"
  natural = \case
    Just (LTensor ([], [r])) | isNatural r -> Just (numerator r)
    _ -> Nothing
  isNatural r = denominator r == 1 && r >= 0
  tshowI :: (Show a) => a -> Text
  tshowI = T.pack . show
  renderList rs = "[" <> T.intercalate ", " (map renderR rs) <> "]"
  renderR r
    | denominator r == 1 = tshowI (numerator r)
    | otherwise = tshowI (fromRational r :: Double)

{- | A node constructor that works in any scope, so that eta-expansion can
apply it under the binders it introduces.
-}
newtype Builder = Builder (forall m. [Term m] -> Term m)

{- | Names that build a Core node when saturated: every primitive, plus the
surface names of the uncertainty operators (design §2.9).
-}
specialForm :: Label -> Text -> Maybe (Int, Builder)
specialForm l = \case
  "within" ->
    Just
      (2, Builder (\case [a, b] -> Uncertain Bound l a b; _ -> error "within: arity"))
  "sigma" ->
    Just
      (2, Builder (\case [a, b] -> Uncertain Stat l a b; _ -> error "sigma: arity"))
  p -> (,Builder (PrimApp p)) <$> primArity p

saturated :: Path -> Ctx n -> ([Term n] -> Term n) -> [S.Expr] -> M (Term n)
saturated path ctx build args = build <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args

-- | Apply a head (built at a given path) to arguments, left-nested.
applyAll :: Path -> Ctx n -> (Path -> M (Term n)) -> [S.Expr] -> M (Term n)
applyAll path ctx mkHead = \case
  [] -> mkHead path
  args -> do
    f <- applyAll (0 : path) ctx mkHead (init args)
    a <- desugar (1 : path) ctx (last args)
    pure (App f a)

{- | Eta-expand a primitive applied to too few arguments:
@add 1@ becomes @\x -> add 1 x@. The supplied arguments are desugared
under the new binders; they cannot mention the fresh names, so no shifting
is needed.
-}
eta :: Path -> Ctx n -> S.Span -> Builder -> [S.Expr] -> Int -> M (Term n)
eta path0 ctx0 sp (Builder build) args missing = go 0 path0 ctx0
 where
  go :: Int -> Path -> Ctx m -> M (Term m)
  go j path ctx
    | j == missing = do
        supplied <- zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args
        let vars = [Var v | k <- [0 .. missing - 1], Just v <- [lookupCtx (fresh "eta" k) ctx]]
        pure (build (supplied ++ vars))
    | otherwise = do
        record path sp
        Lam (Hint "x") <$> go (j + 1) (0 : path) (VCons (fresh "eta" j) ctx)

-- | Lambdas over a list of parameters, then the body.
lams :: Path -> Ctx n -> S.Span -> [S.Name] -> S.Expr -> M (Term n)
lams path ctx sp names body = case names of
  [] -> desugar path ctx body
  n : ns -> do
    record path sp
    Lam (Hint n.text) <$> lams (0 : path) (VCons n.text ctx) sp ns body

opPrim :: S.Op -> Text
opPrim = \case
  S.Add -> "add"
  S.Sub -> "sub"
  S.Outer -> "outer"
  S.Scale -> "outer"
  S.Dot -> "dot"
  S.Cross -> "cross"
  S.Wedge -> "wedge"
  S.EMul -> "emul"
  S.EDiv -> "ediv"
  S.Div -> "div"
  S.Eq -> "eq"
  S.Ne -> "ne"
  S.Lt -> "lt"
  S.Le -> "le"
  S.Gt -> "gt"
  S.Ge -> "ge"
  S.And -> "and"
  S.Or -> "or"
  S.To -> "to"
  S.PAdd -> "pointAdd"
  S.PSub -> "pointSub"
  S.Cons -> "cons"
  S.PlusMinus _ -> "uncertain"
  S.Compose -> "compose"
  S.Infix n -> n

{- | Whether an expression is one of the forms that declare an uncertainty
and so can take a @#label@.
-}
declaresUncertainty :: S.Expr -> Bool
declaresUncertainty e = case e.node of
  S.BinOp (S.PlusMinus _) _ _ -> True
  S.Labelled _ inner -> declaresUncertainty inner
  _ -> case spine e of
    (hd, _ : _) | S.Var x <- hd.node -> x `elem` ["noise", "gauss", "within", "sigma"]
    _ -> False

{- | Whether an expression may follow a literal under the quantity rule
(§2.6): a base unit or a declared unit (not shadowed by a local binder),
a number, or those combined with @*@, @/@, @^@ and juxtaposition.
-}
unitExpr :: Ctx n -> S.Expr -> M Bool
unitExpr ctx e = case e.node of
  S.Num _ -> pure True
  S.Var x
    | Just _ <- lookupCtx x ctx -> pure False
    -- A base unit is a unit; a declared name is what it was declared; any
    -- other primitive or special form (pi, sin, noise) is not; an unknown
    -- name is let through so that the ordinary path reports it as unknown,
    -- and so is a name two uses offer, which it reports as ambiguous.
    | otherwise ->
        ( \case
            Nothing ->
              isJust (baseUnit x) || (isNothing (primArity x) && x `notElem` specialNames)
            Just (_, AAmbiguous _) -> True
            Just (_, r) -> maybe False (.isUnit) (asTerm r)
        )
          <$> resolveWritten x
  -- A qualified unit, @5 orbital.furlong@ (design §7.6).
  S.FieldOf _ _ -> do
    e' <- qualifiedChain ctx e
    case e'.node of
      S.Var _ -> unitExpr ctx e'
      _ -> pure False
  S.Pow u _ -> unitExpr ctx u
  S.BinOp op a b
    | op `elem` [S.Outer, S.Div, S.Scale] ->
        (&&) <$> unitExpr ctx a <*> unitExpr ctx b
  _ -> pure False
 where
  specialNames = ["noise", "gauss", "within", "sigma"]

-- | Whether an expression is a free name declared with @scale@ (design §3.6).
isScaleName :: Ctx n -> S.Expr -> M Bool
isScaleName ctx e = case e.node of
  S.Var x
    | Nothing <- lookupCtx x ctx ->
        maybe False (maybe False (.isScale) . asTerm . snd) <$> resolveWritten x
  S.FieldOf _ _ -> do
    e' <- qualifiedChain ctx e
    case e'.node of
      S.Var _ -> isScaleName ctx e'
      _ -> pure False
  _ -> pure False

{- | A @case@ (design §2.3, §5.1): one alternative per constructor of the
scrutinee's type, in canonical order. The type is read off the constructor
patterns present; a @_@ or a variable supplies every constructor not
written, with its body weakened under that constructor's fields (and, for a
variable, the scrutinee bound once around the whole case).
-}
caseOf ::
  Path -> Ctx n -> S.Span -> S.Expr -> [(S.Pattern, S.Expr)] -> M (Term n)
caseOf path ctx sp scrut alts0 = do
  alts <- mapM promote alts0
  let written = [(c, ns, body, p) | (p@S.Pattern{node = S.PCon c ns}, body) <- alts]
      catchAll = [(p, body) | (p, body) <- alts, isCatchAll p.node]
  -- Each constructor pattern names a built-in or a declared constructor; the
  -- first one fixes the type and so the table of alternatives.
  explicit <-
    mapM
      ( \(c, ns, body, p) -> (\(cr, _) -> (cr, ns, body, p)) <$> conRefFor p c (length ns)
      )
      written
  table <- case written of
    [] ->
      failWith
        ( BadSpecialForm
            sp
            "a case needs at least one constructor pattern ((a, b), x : xs, {}, true, false or a declared constructor) to say which type it analyses"
        )
    (c, ns, _, p) : _ -> snd <$> conRefFor p c (length ns)
  mapM_
    ( \(c, ns, _, p) -> case lookup c table of
        Nothing ->
          failWith
            ( BadSpecialForm
                p.span
                ("pattern " <> conText c <> " does not belong to the type of the scrutinee")
            )
        Just k
          | k /= length ns ->
              failWith
                ( BadSpecialForm
                    p.span
                    ("pattern " <> conText c <> " has " <> T.pack (show k) <> " fields")
                )
        _ -> pure ()
    )
    explicit
  let names = [c | (c, _, _, _) <- explicit]
      dup = [c | (c, i) <- zip names [0 :: Int ..], c `elem` take i names]
      missing = [c | (c, _) <- table, c `notElem` names]
  mapM_
    ( \c ->
        failWith (BadSpecialForm sp ("constructor " <> conText c <> " appears twice"))
    )
    (take 1 dup)
  case (missing, catchAll) of
    (_ : _, []) ->
      failWith
        ( BadSpecialForm
            sp
            ("case does not cover " <> T.intercalate ", " (map conText missing))
        )
    _ -> pure ()
  scrut' <- desugar (0 : path) ctx scrut
  case catchAll of
    (S.Pattern{node = S.PVar v}, _) : _ ->
      -- let v = scrutinee in case v of …
      Let (Hint v.text) scrut'
        <$> build (VCons v.text ctx) (Var FZ) table explicit catchAll
    _ -> build ctx scrut' table explicit catchAll
 where
  -- The parser cannot tell a variable from a nullary constructor; a name
  -- that resolves to a constructor is one.
  promote (p, body) = case p.node of
    S.PVar n -> do
      resolved <- resolveWritten n.text
      pure $ case snd <$> resolved of
        Just (AConstructor _) -> (S.Pattern p.span (S.PCon n.text []), body)
        _ -> (p, body)
    _ -> pure (p, body)
  isCatchAll = \case
    S.PWild -> True
    S.PVar _ -> True
    _ -> False
  -- A constructor's reference and its type's table of (constructor, arity).
  conRefFor :: S.Pattern -> Text -> Int -> M (ConRef, [(ConRef, Int)])
  conRefFor p c k = case c of
    "True" -> pure (Builtin "True", bools)
    "False" -> pure (Builtin "False", bools)
    "Tuple" -> pure (Builtin "Tuple", [(Builtin "Tuple", k)])
    "Nil" -> pure (Builtin "Nil", lists)
    "Cons" -> pure (Builtin "Cons", lists)
    _ -> do
      resolved <- resolveWritten c
      case snd <$> resolved of
        Just (AConstructor info) -> pure (info.con, info.siblings)
        Just (AAmbiguous fulls) -> ambiguous p.span c fulls
        _ -> failWith (BadSpecialForm p.span ("unknown constructor pattern " <> c))
   where
    bools = [(Builtin "False", 0), (Builtin "True", 0)]
    lists = [(Builtin "Nil", 0), (Builtin "Cons", 2)]
  build ::
    forall m.
    Ctx m ->
    Term m ->
    [(ConRef, Int)] ->
    [(ConRef, [S.Name], S.Expr, S.Pattern)] ->
    [(S.Pattern, S.Expr)] ->
    M (Term m)
  build ctx' scrutTerm table explicit catchAll = do
    alts' <- zipWithM (alternative ctx' explicit catchAll) [1 ..] table
    pure (Case scrutTerm alts')
  alternative ::
    forall m.
    Ctx m ->
    [(ConRef, [S.Name], S.Expr, S.Pattern)] ->
    [(S.Pattern, S.Expr)] ->
    Int ->
    (ConRef, Int) ->
    M (Alt m)
  alternative ctx' explicit catchAll i (c, k) = case [(ns, body) | (c', ns, body, _) <- explicit, c' == c] of
    (ns, body) : _ -> case vecFromList (map (.text) ns) of
      SomeVec hs -> Alt c (vecMap Hint hs) <$> desugar (i : path) (vecAppend hs ctx') body
    [] -> case catchAll of
      (_, body) : _ -> case vecFromList (replicate k "_") of
        SomeVec hs -> Alt c (vecMap Hint hs) . weakenBy hs <$> desugar (i : path) ctx' body
      [] -> failWith (BadSpecialForm sp ("case does not cover " <> conText c))

-- | The term a name resolves to, if it is one.
asTerm :: Resolved -> Maybe Resolution
asTerm = \case
  ATerm r -> Just r
  _ -> Nothing

-- | The variable for field @i@ among @k@ fields bound innermost.
fieldVar :: Vec k a -> Ctx n -> Int -> Maybe (Fin (Plus k n))
fieldVar VNil _ _ = Nothing
fieldVar (VCons _ _) _ 0 = Just FZ
fieldVar (VCons _ rest) ctx i = FS <$> fieldVar rest ctx (i - 1)

{- | @C {f = e, …}@ with @C@ a constructor builds the record, every field
given once; @r {f = e, …}@ otherwise rebuilds @r@ with those fields replaced:
a case on the one constructor whose body is the constructor applied to the
old fields, except the new ones (design §2.3). The new values are desugared
outside the case and weakened, so a field name never captures a variable.
A record built with a constructor names its fields as the constructor's
own, by their last segment, wherever the type lives (design §7.6); an
update finds them through the scope.
-}
recordExpr ::
  Path -> Ctx n -> S.Expr -> S.Expr -> [(S.Name, S.Expr)] -> M (Term n)
recordExpr path ctx e hd fields = do
  headCon <- case hd.node of
    S.Var c | Nothing <- lookupCtx c ctx -> do
      resolved <- resolveWritten c
      pure $ case snd <$> resolved of
        Just (AConstructor info) -> Just info
        _ -> Nothing
    _ -> pure Nothing
  let ownField n = do
        ci <- headCon
        j <- lookup (Just n) [(S.lastSegment <$> l, k) | (k, l) <- zip [0 ..] ci.labels]
        pure (FieldInfo ci.con ci.arity j ci.labels)
  infos <-
    mapM
      ( \(n, _) -> case ownField n.text of
          Just info -> pure (n, info)
          Nothing -> do
            resolved <- asks (\env -> env.resolve ("." <> n.text))
            case resolved of
              Just (AField info) -> pure (n, info)
              Just (AAmbiguous fulls) -> ambiguous n.span n.text fulls
              _ -> failWith (BadSpecialForm n.span ("unknown field `" <> n.text <> "`"))
      )
      fields
  (lead, leadInfo) <- case infos of
    x : _ -> pure x
    [] -> failWith (BadSpecialForm e.span "a record needs at least one field")
  mapM_
    ( \(n, info) ->
        when (info.con /= leadInfo.con)
          $ failWith
            (BadSpecialForm n.span ("field `" <> n.text <> "` belongs to another type"))
    )
    infos
  let dup =
        [ n
        | ((n, info), i) <- zip infos [0 :: Int ..]
        , info.index `elem` map ((.index) . snd) (take i infos)
        ]
  mapM_
    ( \n -> failWith (BadSpecialForm n.span ("field `" <> n.text <> "` is given twice"))
    )
    (take 1 dup)
  let given = Map.fromList [(info.index, ex) | ((_, info), (_, ex)) <- zip infos fields]
      fieldName j = maybe ("_" <> T.pack (show j)) S.lastSegment (leadInfo.names !! j)
  construction <- case (hd.node, headCon) of
    (S.Var c, Just info)
      | info.con == leadInfo.con -> pure True
      | otherwise ->
          failWith
            (BadSpecialForm hd.span ("`" <> c <> "` has no field `" <> lead.text <> "`"))
    _ -> pure False
  if construction
    then do
      let missing = [fieldName j | j <- [0 .. leadInfo.arity - 1], Map.notMember j given]
      case missing of
        [] -> pure ()
        _ ->
          failWith
            ( BadSpecialForm
                e.span
                ( "missing "
                    <> (if length missing == 1 then "field " else "fields ")
                    <> T.intercalate ", " missing
                )
            )
      Con leadInfo.con
        <$> mapM (\j -> desugar (j : path) ctx (given Map.! j)) [0 .. leadInfo.arity - 1]
    else do
      hd' <- desugar (0 : path) ctx hd
      case vecFromList (map fieldName [0 .. leadInfo.arity - 1]) of
        SomeVec hs -> do
          args <-
            mapM
              ( \j -> case Map.lookup j given of
                  Just ex -> weakenBy hs <$> desugar (j + 1 : path) ctx ex
                  Nothing -> case fieldVar hs ctx j of
                    Just v -> pure (Var v)
                    Nothing -> failWith (BadSpecialForm e.span "field out of range")
              )
              [0 .. leadInfo.arity - 1]
          pure (Case hd' [Alt leadInfo.con (vecMap Hint hs) (Con leadInfo.con args)])

{- | A literal argument followed by a unit name is two arguments, which is
rarely meant; should a type error land on either, say how to write the
quantity (design §2.6).
-}
quantityHints :: Ctx n -> S.Expr -> [S.Expr] -> M ()
quantityHints ctx hd args = mapM_ check (zip args (drop 1 args))
 where
  check (a, u) = case (a.node, u.node) of
    (lit, S.Var x)
      | Just shown <- literalText lit
      , Nothing <- lookupCtx x ctx -> do
          unit <- unitExpr ctx u
          when unit $ do
            let msg =
                  shown
                    <> " and `"
                    <> x
                    <> "` are two separate arguments here; a quantity in argument position needs parentheses: ("
                    <> shown
                    <> " "
                    <> x
                    <> ")"
            -- The error may land on the literal, the unit, or the application
            -- of the head to either.
            mapM_
              (`hintAt` msg)
              [a.span, u.span, S.spanUnion hd.span a.span, S.spanUnion hd.span u.span]
    _ -> pure ()
  literalText = \case
    S.Num r
      | denominator r == 1 -> Just (T.pack (show (numerator r)))
      | otherwise -> Just "the number"
    S.Vec _ -> Just "the vector"
    _ -> Nothing
