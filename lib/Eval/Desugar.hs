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
  signatureMarker,
  ascriptionPath,
  isQuantityMarker,
  isToMarker,
  isFromMarker,
  spaceQuery,
  fillOperands,
  readingMarkerName,
  unmarked,
  Resolution (..),
  Resolved (..),
  ConInfo (..),
  FieldInfo (..),
  desugarIn,
  renderDesugarError,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, when, zipWithM)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Builtin
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
  , readings :: Int
  {- ^ the quantities and @to@s whose reading is left to the types
  (design §3.10, U4, U6) met so far, which number their markers
  -}
  , operands :: Map Path [Text]
  {- ^ the operands of each conversion as written, by its path, for an
  error that quotes them (design §3.10, F7): @«0»@ and @«1»@ in a message
  -}
  }

emptyProvenance :: Provenance
emptyProvenance = Provenance Map.empty Map.empty [] 0 Map.empty

{- | The marker of a quantity whose reading the types choose (design §3.10,
U4): @scale lit u@ after a unit, @pointOn c lit@ after a chart. Numbered,
so that inference names each marker's reading and 'Eval.Infer.rewriteReadings'
writes it in; a term with a marker is never stored.
-}
isQuantityMarker :: Text -> Bool
isQuantityMarker = T.isPrefixOf "§quantity:"

-- | The marker of a @to@ whose reading the types choose (design §3.10, U6).
isToMarker :: Text -> Bool
isToMarker = T.isPrefixOf "§to:"

-- | The marker of a @from … to@ whose reading the types choose (design §3.10, F7).
isFromMarker :: Text -> Bool
isFromMarker = T.isPrefixOf "§from:"

-- | The @k@th marker of a kind, @quantity@ or @to@.
readingMarkerName :: Text -> Int -> Text
readingMarkerName kind k = "§" <> kind <> ":" <> T.pack (show k)

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
data Resolution = Resolution
  { ref :: (Hash, Maybe Int)
  , isUnit :: Bool
  , isChart :: Bool
  , isMoving :: Bool
  -- ^ a chart declared with parameters: a moving chart, a function to a chart (design §3.8)
  }

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
  | -- | A space's declaration, by its hash, for a @%space:@ query (design §3.10, F2).
    ASpaceDecl Hash

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
  , definition :: Text
  {- ^ the full path of the definition being desugared, which a chart's
  minted axis type is stamped with (design §3.9); a @#label@ does not
  change it
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
    (runReaderT (desugar [] ctx e) (Env resolve (Owner name) Nothing name))
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
    (runReaderT (desugar [] ctx e) (Env resolve (Owner name) (Just tag) name))
    emptyProvenance

-- | The name of an ascription marker starts so (design §4.8).
ascriptionMarker :: Text
ascriptionMarker = "§ascribe"

{- | The marker around a member's body when its ascriptions name the
variables of its signature (design §4.8): the signature's type, read as an
ascription of the whole body, so that both meet the same variables. Its
body is at the marker's own path, since the desugarer did not put it
one level down. The tag tells the members of a cycle apart.
-}
signatureMarker :: Text -> Text
signatureMarker tag = ascriptionMarker <> tag <> ":signature"

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
    -- true, (a, b) and lists are constructors of the built-in declarations.
    S.Bool b -> pure (Con (boolC b) [])
    S.Tuple es
      | length es > maxTupleArity ->
          failWith
            ( BadSpecialForm
                e.span
                ("a tuple has at most " <> T.pack (show maxTupleArity) <> " components")
            )
      | otherwise ->
          Con (tupleC (length es))
            <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] es
    S.List es ->
      foldr
        (\(i, a) rest -> (\x r -> Con consC [x, r]) <$> desugar (i : path) ctx a <*> rest)
        (pure (Con nilC []))
        (zip [0 ..] es)
    S.CaseOf scrut alts -> caseOf path ctx e.span scrut alts
    S.Var x -> do
      unit <- unitName ctx e
      when unit (bareUnit e)
      headApp path ctx e x []
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
      pure (Case c' [Alt falseC VNil f', Alt trueC VNil t'])
    -- A unit's declaration (design §3.10, U7): its body made a unit.
    S.UnitBody a -> do
      unit <- staticUnit ctx a
      if unit
        then desugarUnit path ctx a
        else (\a' -> PrimApp "unit" [a']) <$> desugar (0 : path) ctx a
    S.UnitSyntax a -> desugarUnit path ctx a
    -- After a literal the quantity takes the whole unit expression (design
    -- §3.10, U5): the chain of products and quotients is regrouped first.
    S.BinOp op a b -> do
      grouped <- regroup ctx e
      if grouped /= e
        then desugar path ctx grouped
        else case op of
          S.PlusMinus k ->
            asks (Uncertain k . (.owner))
              <*> desugar (0 : path) ctx a
              <*> desugar (1 : path) ctx b
          -- An amount to a display unit, a point to another chart, or an
          -- amount along a chart's axes; which, the types say when the
          -- spelling does not (design §3.10, U6, F10). A chart with
          -- parameters must be applied first (F7).
          S.To -> do
            refuseMoving ctx asTarget b
            unit <- staticUnit ctx b
            -- A unit's name here is meant as a unit; one of the wrong
            -- dimension is not to be written as an amount.
            named <- unitName ctx b
            when
              named
              (hintAt b.span "the unit after `to` has the dimension of the value before it")
            operands [a, b]
            if unit
              then
                PrimApp "to"
                  <$> sequence [desugar (0 : path) ctx a, desugarUnit (1 : path) ctx b]
              else readingMarker "to" >>= \m -> prim m [a, b]
          -- Subtracting in a frame (design §3.10, F10): both points
          -- converted to one chart value, then subtracted.
          S.On -> case a.node of
            S.BinOp S.PSub q r -> do
              let x = fresh "on" 0
                  var = S.Expr b.span (S.Var x)
                  to p = S.Expr p.span (S.BinOp S.To p var)
              desugar
                path
                ctx
                ( S.Expr
                    e.span
                    ( S.Let
                        (S.Name b.span x)
                        []
                        b
                        (S.Expr a.span (S.BinOp S.PSub (to q) (to r)))
                    )
                )
            _ ->
              failWith
                ( BadSpecialForm
                    a.span
                    "`on` subtracts two points in a frame: write b .- a on c"
                )
          S.PAdd -> prim "pointAdd" [a, b]
          S.Cons ->
            (\x r -> Con consC [x, r])
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
          -- The quantity rule (design §3.10, U4): a literal and what follows it,
          -- the whole unit expression, juxtaposed atoms multiplied. After a
          -- unit it is the amount `scale lit u`, after a chart the point
          -- `pointOn c lit`; the spelling decides for declared units and
          -- charts, the types for anything else.
          S.Scale -> do
            let (lit, atoms) = scaleChain e
                unitE = foldl1 (binop S.Outer) atoms
            mapM_ (refuseMoving ctx asPoint) atoms
            chart <- case atoms of
              [c] -> isChartName ctx c
              _ -> pure False
            unit <- staticUnit ctx unitE
            if chart
              then prim "pointOn" [unitE, lit]
              else
                if unit
                  then
                    PrimApp "scale"
                      <$> sequence [desugar (0 : path) ctx lit, desugarUnit (1 : path) ctx unitE]
                  else readingMarker "quantity" >>= \m -> prim m [lit, unitE]
          -- Bare unit expressions are shorthand for one of that unit only
          -- at the operands of multiplication and division.
          _ | op `elem` [S.Outer, S.Div] -> do
            PrimApp (opPrim op)
              <$> sequence [desugarFactor (0 : path) ctx a, desugarFactor (1 : path) ctx b]
          _ -> prim (opPrim op) [a, b]
    -- Negating a constant is a negative constant, so that `-3` and a literal
    -- negative three are one term with one hash (core.md §6: constants are
    -- canonical); so is a quantity of a constant, `-3 K` being `scale (-3)
    -- K` as the printer writes it (design §3.10). Anything else is the
    -- primitive.
    S.Neg a
      | S.BinOp S.Scale _ _ <- a.node
      , (lit, atoms) <- scaleChain a
      , constantLiteral lit ->
          desugar
            path
            ctx
            ( foldl
                (binop S.Scale)
                (S.Expr (S.Span e.span.from lit.span.to) (S.Neg lit))
                atoms
            )
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
    -- A conversion from a configuration (design §3.10, F7): a point or an
    -- amount, which the types say.
    S.FromTo v c c1 -> do
      refuseMoving ctx asTarget c
      refuseMoving ctx asTarget c1
      readingMarker "from" >>= \m -> prim m [v, c, c1]
    -- A chart (design §3.10, F3, F10): on a space, a root, or on a parent
    -- chart. A root, an origin, axes turned or a spin mint a frame, whose
    -- type the chart primitive takes first, stamped with the chart's path;
    -- turned axes or a spin mint axes too; a step alone is a rescaling,
    -- which shares its parent's frame. Each clause is a list of none or one,
    -- so that an omitted one is inherited.
    S.ChartForm cl -> do
      space <- spaceNamed ctx cl.parent
      def <- asks (.definition)
      let turns = isJust cl.generators || isJust cl.spin
          mints = isJust space || isJust cl.origin || turns
          frameT = Con (frameTag def cl.parameterised) []
          axesT = Con (axesTag def) []
          nil = Con nilC []
          one x = Con consC [x, nil]
          optional i = \case
            Nothing -> pure nil
            Just x -> do
              record (i : path) x.span
              one <$> desugar (0 : i : path) ctx x
          gens =
            maybe
              (pure nil)
              (desugar (5 : path) ctx)
              (cl.generators <|> (S.Expr cl.parent.span (S.List []) <$ cl.spin))
      rest <-
        sequence
          [ case cl.step of
              Nothing -> pure nil
              Just x -> one <$> desugarUnit (0 : 3 : path) ctx x
          , optional 4 cl.origin
          , gens
          , optional 6 cl.spin
          ]
      case space of
        Just h ->
          pure
            ( PrimApp
                "mkRoot"
                ([frameT, if turns then one axesT else nil, Con (UserCon h 0) []] ++ rest)
            )
        Nothing -> do
          refuseMoving ctx asParent cl.parent
          parent <- desugar (2 : path) ctx cl.parent
          pure
            ( PrimApp
                "mkChart"
                ( [if mints then one frameT else nil, if turns then one axesT else nil, parent]
                    ++ rest
                )
            )
 where
  prim p args = PrimApp p <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args
  synthLam sp x body = S.Expr sp (S.Lam [S.Name sp x] body)
  -- The operands of a conversion as written, for its error (design §3.10, F7).
  operands xs =
    lift
      ( modify'
          (\p -> p{operands = Map.insert (reverse path) (map operandText xs) p.operands})
      )

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
      Just (ASpaceDecl _) -> failWith (UnknownName hd.span x)
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
              , n >= 0
              , numerator n > componentLimit ->
                  failWith
                    ( BadSpecialForm
                        a.span
                        ( x
                            <> " "
                            <> T.pack (show (numerator n))
                            <> ": a tensor has at most "
                            <> T.pack (show componentLimit)
                            <> " components"
                        )
                    )
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
indexProblem name lits
  -- Positions are machine integers: one no tensor could have is refused
  -- rather than wrapped.
  | (i, r) : _ <-
      [ (i, numerator r)
      | (i, Just (LTensor (_, rs))) <- zip [0 ..] lits
      , r <- rs
      , isNatural r
      , numerator r >= componentLimit
      ] =
      Just
        ( i
        , "position "
            <> tshowI r
            <> " is out of range: a tensor has at most "
            <> tshowI componentLimit
            <> " components"
        )
  | otherwise = case (name, lits) of
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
  S.On -> "on"
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

-- Units (design §3.10) -------------------------------------------------------------

{- | Whether an expression is a declared unit's name: a base unit or a name
declared with @unit@, not shadowed by a local binder, written bare or
qualified (@5 orbital.furlong@, design §7.6). Names decide the grouping
of a quantity (U5) and which quantities and @to@s the spelling reads
(U4, U6); the types decide everything else.
-}
unitName :: Ctx n -> S.Expr -> M Bool
unitName ctx e = case e.node of
  S.Var x
    | Just _ <- lookupCtx x ctx -> pure False
    | otherwise ->
        ( \case
            Nothing -> isJust (baseUnit x)
            Just (_, r) -> maybe False (.isUnit) (asTerm r)
        )
          <$> resolveWritten x
  S.FieldOf _ _ -> do
    e' <- qualifiedChain ctx e
    case e'.node of
      S.Var _ -> unitName ctx e'
      _ -> pure False
  _ -> pure False

-- | A declared unit's name, with or without a power: what a quantity takes in.
unitAtom :: Ctx n -> S.Expr -> M Bool
unitAtom ctx e = case e.node of
  S.Pow u _ -> unitName ctx u
  _ -> unitName ctx e

{- | Whether an expression is unit arithmetic on declared units' names alone,
@km@, @km/h@, @kg*m/s^2@: a unit by its spelling, so a quantity of it is
@scale@ and a @to@ to it the display unit's, with no reading for the
types to choose.
-}
staticUnit :: Ctx n -> S.Expr -> M Bool
staticUnit ctx e = case e.node of
  S.Pow u _ -> staticUnit ctx u
  S.BinOp op a b
    | op `elem` [S.Outer, S.Div] -> (&&) <$> staticUnit ctx a <*> staticUnit ctx b
  _ -> unitName ctx e

{- | Unit syntax has no ordinary value reading. Keep the internal unit
representation for suffixes, display targets and chart steps.
-}
bareUnit :: S.Expr -> M a
bareUnit e = do
  hint <- lift (gets (Map.lookup e.span . (.hints)))
  failWith
    ( BadSpecialForm
        e.span
        ( "a unit is not an expression: write an amount such as 1 km; bare units are allowed at * and /, in quantity suffixes, after to, and in chart steps"
            <> maybe "" ("\n  hint: " <>) hint
        )
    )

desugarFactor :: Path -> Ctx n -> S.Expr -> M (Term n)
desugarFactor path ctx e = do
  unit <- staticUnit ctx e
  if unit then unitAmount path ctx e else desugar path ctx e

unitAmount :: Path -> Ctx n -> S.Expr -> M (Term n)
unitAmount path ctx e = do
  record path e.span
  u <- desugarUnit (1 : path) ctx e
  pure (PrimApp "scale" [Lit (LTensor ([], [1])), u])

desugarUnit :: Path -> Ctx n -> S.Expr -> M (Term n)
desugarUnit path ctx e = do
  record path e.span
  unit <- staticUnit ctx e
  if not unit
    then
      failWith
        ( BadSpecialForm
            e.span
            "expected unit syntax, such as km or km/s; a unit cannot be passed as a value"
        )
    else case e.node of
      S.BinOp op a b | op `elem` [S.Outer, S.Div] -> do
        a' <- unitAmount (0 : 0 : path) ctx a
        b' <- unitAmount (1 : 0 : path) ctx b
        pure (PrimApp "unit" [PrimApp (opPrim op) [a', b']])
      S.Pow a n -> do
        a' <- unitAmount (0 : 0 : path) ctx a
        pure (PrimApp "unit" [Pow a' n])
      _ -> do
        named <- qualifiedChain ctx e
        case named.node of
          S.Var x -> headApp path ctx named x []
          _ -> bareUnit e

{- | The literal of a quantity and the atoms juxtaposed after it, @9.81 m
s^-2@ as @9.81@ and @[m, s^-2]@.
-}
scaleChain :: S.Expr -> (S.Expr, [S.Expr])
scaleChain = go []
 where
  go acc x = case x.node of
    S.BinOp S.Scale a b -> go (b : acc) a
    _ -> (x, acc)

-- | A literal of constants: a number, or a bracket literal of them.
constantLiteral :: S.Expr -> Bool
constantLiteral x = case x.node of
  S.Num _ -> True
  S.Neg y -> constantLiteral y
  S.Vec es -> all constantLiteral es
  _ -> False

{- | Whether a binary node was written in parentheses: its span is wider than
its operands'.
-}
parenthesised :: S.Expr -> Bool
parenthesised x = case x.node of
  S.BinOp _ a b -> x.span /= S.spanUnion a.span b.span
  _ -> False

binop :: S.Op -> S.Expr -> S.Expr -> S.Expr
binop o a b = S.Expr (S.spanUnion a.span b.span) (S.BinOp o a b)

{- | A quantity that a following unit may join (design §3.10, U5): its
literal, its unit expression, and how to put it back, under a minus sign
when it was written under one. Not one written in parentheses.
-}
quantityOf :: S.Expr -> Maybe (S.Expr, S.Expr, S.Expr -> S.Expr)
quantityOf q = case q.node of
  S.BinOp S.Scale _ _
    | not (parenthesised q)
    , (lit, atoms@(_ : _)) <- scaleChain q ->
        Just (lit, foldl1 (binop S.Outer) atoms, id)
  S.Neg inner
    | inner.span.to == q.span.to
    , Just (lit, u, back) <- quantityOf inner ->
        Just (lit, u, \x -> S.Expr (S.spanUnion q.span x.span) (S.Neg (back x)))
  _ -> Nothing

{- | Unit operators bind before numbers (design §3.10, U5): in a chain of
products and quotients, a quantity takes in each following factor that is
a declared unit's name, with or without a power, so @9.81 m/s^2@ is
@9.81 (m/s^2)@ and @x / 1 km/h@ is @x / (1 (km/h))@. A number, or any other
name, ends it: @6 m / 2 s@, @6 m / x@. Where a name ends a quantity, a
type error there says how to write the name into it, should it be a unit.
-}
regroup :: Ctx n -> S.Expr -> M S.Expr
regroup ctx e = case top e of
  (_, []) -> pure e
  (first, rest) -> do
    built <- foldM step [(Nothing, first)] rest
    -- The whole keeps its span, parentheses and all.
    pure (S.Expr e.span (rebuild (reverse built)).node)
 where
  -- The chain's first operand and the rest with their operators, not
  -- descending into parentheses below its top.
  top x = case x.node of
    S.BinOp op a b | op `elem` chained -> let (h, more) = links a in (h, more ++ [(op, b)])
    _ -> (x, [])
  links x
    | parenthesised x = (x, [])
    | otherwise = top x
  chained = [S.Outer, S.Dot, S.Wedge, S.EMul, S.EDiv, S.Div]
  step acc (op, b) = case acc of
    (before, q) : earlier
      | op `elem` [S.Outer, S.Div]
      , Just (lit, units, back) <- quantityOf q -> do
          atom <- unitAtom ctx b
          if atom
            then
              pure
                ( (before, back (binop S.Scale lit (binop op units b)))
                    : earlier
                )
            else do
              endsAt (spanOf acc b) lit units op b
              pure ((Just op, b) : acc)
    _ -> pure ((Just op, b) : acc)
  -- The span of the node the operand joins: from the chain's start.
  spanOf acc b = S.spanUnion (snd (last acc)).span b.span
  rebuild = \case
    (_, x) : more -> foldl (\l (op, r) -> binop (fromMaybe S.Outer op) l r) x more
    [] -> e
  endsAt sp lit units op b = case (b.node, surfaceText lit, surfaceText units) of
    (S.Var x, Just l, Just u) ->
      hintAt
        sp
        ( "`"
            <> x
            <> "` is not a declared unit, so the quantity ends before it; if it is a unit, write "
            <> l
            <> " ("
            <> u
            <> (if op == S.Div then "/" else "*")
            <> x
            <> ")"
        )
    _ -> pure ()

-- | A fresh marker of a reading the types choose, @quantity@ or @to@.
readingMarker :: Text -> M Text
readingMarker kind = do
  -- Named by the definition too: the members of a cycle are desugared
  -- apart, each counting from zero.
  def <- asks (.definition)
  k <- lift (gets (.readings))
  lift (modify' (\p -> p{readings = k + 1}))
  pure (readingMarkerName kind k <> ":" <> def)

{- | A literal or unit expression as it reads back, for a hint: numbers,
names, powers, products and quotients.
-}
surfaceText :: S.Expr -> Maybe Text
surfaceText x = case x.node of
  S.Num r -> Just (numberText r)
  S.Var n -> Just n
  S.Pow u k -> (<> ("^" <> T.pack (show k))) <$> surfaceText u
  S.BinOp S.Outer a b -> (\l r -> l <> "*" <> r) <$> surfaceText a <*> surfaceText b
  S.BinOp S.Div a b -> (\l r -> l <> "/" <> r) <$> surfaceText a <*> surfaceText b
  _ -> Nothing
 where
  numberText r
    | denominator r == 1 = T.pack (show (numerator r))
    | otherwise = case [k | k <- [1 .. 20 :: Int], denominator (r * 10 ^ k) == 1] of
        k : _ ->
          let digits = T.pack (show (abs (numerator (r * 10 ^ k))))
              padded = T.replicate (k + 1 - T.length digits) "0" <> digits
              (whole, frac) = T.splitAt (T.length padded - k) padded
           in (if r < 0 then "-" else "") <> whole <> "." <> frac
        [] -> T.pack (show (numerator r)) <> "/" <> T.pack (show (denominator r))

{- | A chart's parent when it names a space (design §3.10, F2): a free
name, perhaps qualified, that the type scope resolves to a space's
declaration, by its hash. Anything else is a chart.
-}
spaceNamed :: Ctx n -> S.Expr -> M (Maybe Hash)
spaceNamed ctx e = case written e of
  Just x
    | Nothing <- lookupCtx x ctx ->
        asks (\env -> env.resolve (spaceQuery <> x)) >>= \case
          Just (ASpaceDecl h) -> pure (Just h)
          _ -> pure Nothing
  _ -> pure Nothing
 where
  written x = case x.node of
    S.Var n -> Just n
    S.FieldOf a f -> (<> ("." <> f)) <$> written a
    _ -> Nothing

-- | The query a resolver answers with a space, @%space:name@.
spaceQuery :: Text
spaceQuery = "%space:"

{- | An operand of a conversion as written, for an error that quotes it
(design §3.10, F7): a name, an application of names, or else @p@.
-}
operandText :: S.Expr -> Text
operandText x = fromMaybe "p" (go x)
 where
  go y = case y.node of
    S.Var n -> Just n
    S.Num _ -> surfaceText y
    S.App f a -> (\f' a' -> f' <> " " <> a') <$> go f <*> atom a
    S.FieldOf a f -> (<> ("." <> f)) <$> go a
    S.Vec es -> (\ts -> "[" <> T.intercalate ", " ts <> "]") <$> mapM go es
    S.BinOp S.Scale a b -> (\a' b' -> a' <> " " <> b') <$> go a <*> atom b
    _ -> Nothing
  atom y = case y.node of
    S.App _ _ -> (\t -> "(" <> t <> ")") <$> go y
    _ -> go y

{- | A message with the operands of the conversion it is about (design
§3.10, F7): @«0»@ and @«1»@ replaced by the source of the node's first and
second operands, as the desugarer recorded them.
-}
fillOperands :: Path -> Provenance -> Text -> Text
fillOperands path prov msg = case Map.lookup path prov.operands of
  Just texts ->
    foldl
      (\m (i, t) -> T.replace ("«" <> T.pack (show i) <> "»") t m)
      msg
      (zip [0 :: Int ..] texts)
  Nothing -> T.replace "«0»" "p" (T.replace "«1»" "c" msg)

{- | Whether an expression is a free name declared with @chart@ (design
§3.6), or a moving chart applied at a time, @ecef t0@ (§3.8).
-}
isChartName :: Ctx n -> S.Expr -> M Bool
isChartName ctx e = case e.node of
  S.App _ _ -> isJust <$> movingChart ctx (fst (spine e))
  _ -> maybe False ((.isChart) . snd) <$> chartResolution ctx e

{- | A moving chart's name where a chart is wanted (design §3.8) is refused:
the chart is a function of time, and a point or a parent needs the chart
at an instant.
-}
refuseMoving :: Ctx n -> (Text -> Text) -> S.Expr -> M ()
refuseMoving ctx how e = do
  moving <- movingChart ctx e
  case moving of
    Just x ->
      failWith (BadSpecialForm e.span ("`" <> x <> "` takes arguments: " <> how x))
    Nothing -> pure ()

-- | How a chart with parameters is applied where a chart is wanted (design §3.10, F7).
asPoint, asTarget, asParent :: Text -> Text
asPoint x = "a point is written on an applied chart, as in [1, 2, 3] (" <> x <> " t0)"
asTarget x = "apply it, as in p to (" <> x <> " t0)"
asParent x = "apply it, as in chart arm t on (" <> x <> " t) at [1, 0, 0] m"

-- | The name, as written, of a moving chart, when the expression is one.
movingChart :: Ctx n -> S.Expr -> M (Maybe Text)
movingChart ctx e =
  ( \case
      Just (x, r) | r.isChart && r.isMoving -> Just x
      _ -> Nothing
  )
    <$> chartResolution ctx e

-- | What a free name, perhaps qualified, resolves to as a definition, with the name as written.
chartResolution :: Ctx n -> S.Expr -> M (Maybe (Text, Resolution))
chartResolution ctx e = case e.node of
  S.Var x
    | Nothing <- lookupCtx x ctx ->
        (>>= fmap (x,) . asTerm . snd) <$> resolveWritten x
  S.FieldOf _ _ -> do
    e' <- qualifiedChain ctx e
    case e'.node of
      S.Var _ -> chartResolution ctx e'
      _ -> pure Nothing
  _ -> pure Nothing

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
    -- The patterns the syntax builds: constructors of the built-in
    -- declarations, with their tables read off the declarations.
    "True" -> pure (trueC, builtinCons boolHash)
    "False" -> pure (falseC, builtinCons boolHash)
    "Tuple"
      | k > maxTupleArity ->
          failWith
            ( BadSpecialForm
                p.span
                ("a tuple has at most " <> T.pack (show maxTupleArity) <> " components")
            )
      | otherwise -> pure (tupleC k, builtinCons (tupleHash k))
    "Nil" -> pure (nilC, builtinCons listHash)
    "Cons" -> pure (consC, builtinCons listHash)
    _ -> do
      resolved <- resolveWritten c
      case snd <$> resolved of
        Just (AConstructor info) -> pure (info.con, info.siblings)
        Just (AAmbiguous fulls) -> ambiguous p.span c fulls
        _ -> failWith (BadSpecialForm p.span ("unknown constructor pattern " <> c))
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
          unit <- unitName ctx u
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
