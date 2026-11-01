{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{- | A direct, environment-passing, call-by-need evaluator over Typed Core
(design §8). Type abstractions and applications are erased. Because terms
have been inferred and linted, the remaining type-error cases are
unreachable; they exist to keep the pattern matches total and are reported
as internal errors.

Tensors are one runtime shape: a flat row-major buffer of element thunks
beside the list of lengths, a dimension vector, and an optional display
unit (design §3.2.12). A number is the rank-zero case with a buffer of
one. Elements are magnitudes (design §3.2): exact rationals, or affine
forms once an approximation or a declared uncertainty has entered.
Magnitudes are always in SI base units; the display unit says how to
print them. The dimension vector also supplies runtime metadata for empty tensors
and mapped results; display units affect printing only. Types are checked
before evaluation.
-}
module Metron.Eval (
  Value (..),
  pattern VBool,
  Closure (..),
  Elem,
  Thunk,
  EvalError (..),
  Config (..),
  defaultConfig,
  precisionOf,
  Runtime (..),
  UnitAtom (..),
  UnitHint (..),
  UnitFactor (..),
  Chart (..),
  Applied (..),
  coordinatesOn,
  Preferences,
  hintPow,
  hintProduct,
  covarianceMatrix,
  Site (..),
  eval,
  evalClosed,
  evalAt,
  evalDefinition,
  neededAtRuntime,
  TyEnv,
  apply,
  scalar,
) where

import Control.Monad ( foldM, when, zipWithM )
import Data.Bifunctor ( first )
import Data.Map.Strict ( Map )
import Data.Maybe ( catMaybes, fromMaybe, isJust )
import Data.Ratio ( denominator, numerator )
import Data.Text ( Text )
import Data.Vector ( Vector )
import Metron.Affine
    ( Precision,
      absM,
      acosM,
      addM,
      asinM,
      atan2M,
      atanM,
      boundRadius,
      ceilM,
      collapse,
      compareM,
      cosM,
      coshM,
      crossCovarianceRows,
      divM,
      equalM,
      expM,
      floorM,
      logM,
      midpoint,
      mulM,
      negM,
      nonLinearAt,
      piM,
      powM,
      roundM,
      sinM,
      sinhM,
      sqrtM,
      subM,
      tanM,
      tanhM,
      uncertain,
      unitNoise,
      ArithError(..),
      Collapsed(variance, bound),
      Decide(..),
      Magnitude(Exact),
      Origin(Declared, Tagged),
      Skew(operation) )
import Metron.Builtin
    ( pattern ConsC, pattern FalseC, pattern NilC, pattern TrueC, boolC, frameDefMoving, spaceOf )
import Metron.Core
    ( componentLimit,
      vecAppend,
      vecIndex,
      vecMapIndexed,
      vecToList,
      ConRef(..),
      Fin(..),
      Hash(..),
      Hint(Hint),
      Label(Tag),
      Lit(LTensor),
      Nat(Z, S),
      Plus,
      Vec(..) )
import Metron.Dimension
    ( dimAtoms,
      dimBase,
      dimDiv,
      dimFromAtoms,
      dimInv,
      dimMul,
      dimOne,
      dimPow,
      dimRoot,
      BaseDim(T, Ang),
      Dim,
      DimAtom(Base) )
import Metron.Numerical.Linear
    ( choleskyRows, determinant, invert, matrixExp )
import Metron.Primitive ( baseUnit, primArity, typedPrims )
import Metron.TCore ( TAlt(TAlt), TTerm(..) )
import Metron.Type
    ( Arg(..),
      Kind(..),
      Len(..),
      Shape(..),
      Space(..),
      Type(..),
      TypeDef,
      VarId,
      conText,
      freeVars,
      selfType,
      spaceLens,
      substOnce,
      varArg,
      pattern TTensor )
import Metron.UnitHint
    ( combine,
      hintInv,
      hintMul,
      hintPow,
      hintProduct,
      mergeAtoms,
      mkHint,
      mkHintAs,
      smallerUnit,
      unitHintDiv,
      unitHintMul,
      unitHintPow,
      HintMode(PreserveExpression),
      Preferences,
      UnitAtom(..),
      UnitFactor(..),
      UnitHint(..) )
import Data.Map.Strict qualified as Map ( null, empty, insert )
import Data.Text qualified as T ( intercalate, pack )
import Data.Vector qualified as V
    ( (!),
      all,
      concat,
      concatMap,
      empty,
      fromList,
      generate,
      head,
      imap,
      length,
      map,
      replicate,
      singleton,
      slice,
      toList,
      zipWith )

{- | Evaluation parameters: the number of significant digits printed, the
number of standard deviations a comparison must clear to be decided (design
§3.2.9), and whether output uses the unicode spellings.
-}
data Config = Config
  { precision :: Int
  , sigma :: Int
  , unicode :: Bool
  -- ^ print with the unicode spellings of design §2.8 (@:set unicode on@, §7.3)
  , nonlinear :: Rational
  {- ^ the fraction of a value's first-order σ its second-order statistical
  term may reach before the value is marked non-linear (design §3.2,
  @:set nonlinear@, in percent)
  -}
  }
  deriving stock (Show)

defaultConfig :: Config
defaultConfig = Config{precision = 20, sigma = 3, unicode = False, nonlinear = 1 / 100}

-- | Working precision: the scale plus guard digits (design §3.2.8).
precisionOf :: Config -> Precision
precisionOf cfg = cfg.precision + 4

-- | How comparisons are decided under a configuration (design §3.2.9).
decideOf :: Config -> Decide
decideOf cfg = Decide{sigma = cfg.sigma, nonlinear = cfg.nonlinear}

{- | What the evaluator needs from the codebase: the Typed Core behind a
reference, and whether a reference was declared a display unit.
-}
data Runtime = Runtime
  { typedOf :: Hash -> Maybe (TTerm Z)
  , unitName :: Hash -> Maybe Int -> Text -> Maybe Text
  -- ^ given a reference and the name written for it, the unit name it is a unit under, if any (design §3.2.12)
  , chartName :: Hash -> Maybe Int -> Text -> Maybe Text
  , typeDefOf :: Hash -> Maybe TypeDef
  {- ^ the declared types, for a space's amounts and a frame's parameters
  (design §3.10, F2, F7), which a chart's declaration names by its tags
  -}
  , shared :: Hash -> Maybe Thunk
  {- ^ the value of a definition (not a cycle member) evaluated once and
  shared by every reference to it, when the caller keeps such a table:
  @evalDefinition cfg rt h t@ under the same 'Config' and this runtime, so that an
  expensive value (a turned chart's rotation, design §3.8) is computed once
  per evaluation rather than once per reference. Pure, so sharing changes
  no result; 'Nothing' evaluates the definition afresh
  -}
  }

data EvalError
  = DivideByZero
  | -- | a function applied to an enclosure that leaves its domain
    Domain Text
  | -- | a comparison or integer rounding the enclosure cannot settle
    Undecided Text
  | UnknownRef Hash
  | BadCycleIndex Int
  | Unsupported Text
  | {- | a chart whose step's enclosure reaches zero, so that its
    coordinates are not invertible (design §3.10, F6): the chart's name,
    once a reference to it gives one, and what is wrong with the step
    -}
    ChartStep (Maybe Text) Text
  | -- | Unreachable for linted terms.
    Internal Text
  deriving stock (Eq, Show)

type Thunk = Either EvalError Value

-- | A tensor element, lazily.
type Elem = Either EvalError Magnitude

-- | The environment for a term in scope @n@.
type Env n = Vec n Thunk

{- | Where a node sits: the enclosing top-level definition and the path of
child indices down to it, innermost first. Declared uncertainty takes its
identity from here (design §3.2.4). Erased type nodes do not count, so
the path is the Core path and survives re-elaboration.
-}
data Site = Site {definition :: Hash, path :: [Int]}

{- | A chart (design §3.10): a step, an origin and axes relative to its
parent. Points store frame coordinates with the step applied. Local
offsets and generators let conversions stop at a shared configuration;
absolute transforms and kinematics remain cached for the physics helpers.
-}
data Chart = Chart
  { name :: Maybe UnitAtom
  , step :: Magnitude
  , stepHint :: Maybe UnitHint
  -- ^ the step's own display unit, which differences inherit
  , origin :: Vector Magnitude
  {- ^ the origin as an amount from the base origin along the base axes, one
  magnitude per component: the parent's origin plus the amount the chart
  was given at, which is along the parent's axes and so turned by the
  parent's rotation
  -}
  , localOrigin :: Vector Magnitude
  -- ^ the declared offset along the parent's axes, before any rotation
  , dims :: [Int]
  , dim :: Dim
  , parent :: Maybe Chart
  {- ^ the chart the origin and the generators are given in; 'Nothing' is
  the base of its space (design §3.10, F2). The chart value itself, not a hash: a
  chart need not be named, and its definition's Core already refers to the
  parent's by hash
  -}
  , generators :: [Vector Magnitude]
  {- ^ antisymmetric @n × n@ matrices, row-major, applied in order; none is
  axis-aligned with the parent
  -}
  , rotation :: Maybe (Either EvalError (Vector Magnitude))
  {- ^ the absolute rotation, row-major: the parent's times @expm g₁ · expm
  g₂ · …@, whose columns are this chart's axes along the base axes.
  'Nothing' when neither this chart nor any above it is turned. A lazy
  field, so it is computed once, when first used, and shared by every use
  of the value
  -}
  , rotationInverse :: Maybe (Either EvalError (Vector Magnitude))
  {- ^ its inverse, from the generators negated in reverse order (@… · expm
  (−g₂) · expm (−g₁)@, then the parent's inverse), never by inverting an
  enclosure
  -}
  , relativeRotation :: Maybe (Either EvalError (Vector Magnitude))
  , relativeRotationInverse :: Maybe (Either EvalError (Vector Magnitude))
  -- ^ cached local transforms, used by conversions below a shared ancestor
  , spin :: Maybe (Vector Magnitude)
  {- ^ the angular velocity of a spinning chart relative to its parent,
  along its own axes, in s⁻¹ (the radian stripped); 'Nothing' is none
  -}
  , spinAbs :: Maybe (Either EvalError (Vector Magnitude))
  {- ^ the absolute angular velocity along the base axes, @ω_abs = ω_parent
  + R_abs ω@; 'Nothing' when neither this chart nor any above it spins.
  Lazy, as the rotation is
  -}
  , originVelocity :: Maybe (Either EvalError (Vector Magnitude))
  {- ^ the velocity of the origin along the base axes, @v_parent + ω_parent
  × (R_parent a)@ for the amount @a@ the origin is given at (an origin is
  fixed relative to its parent); 'Nothing' when nothing above spins
  -}
  , applied :: Applied
  -- ^ the arguments of the moving chart this chart is an instant of, if it is one
  , frame :: Hash
  {- ^ the frame the chart is a chart of (design §3.10, F3): the one it
  minted, or a rescaling's parent's
  -}
  , moving :: Bool
  -- ^ whether its frame's chart takes parameters (design §3.10, F7)
  }
  deriving stock (Eq, Show)

{- | The arguments a moving chart was applied to (design §3.8), kept so that
the chart it gave prints as it is written, @(ecef (100 unix))@. They say
how the chart prints, not what it is, so 'Eq' ignores them.
-}
newtype Applied = Applied [Thunk]

instance Eq Applied where
  _ == _ = True

instance Show Applied where
  show (Applied xs) = "Applied <" ++ show (length xs) ++ " arguments>"

data Value
  = -- | lengths, dimension, display unit, flat row-major elements in SI base units
    VTensor [Int] Dim (Maybe UnitHint) (Vector Elem)
  | {- | a point on a frame (design §3.10, F6): lengths, dimension, the chart
    it was written on, for printing, and its coordinates on its frame with
    the step applied, an amount from the frame's origin along its axes
    -}
    VPoint [Int] Dim Chart (Vector Elem)
  | VChart Chart
  | -- | a constructor with its fields as thunks (design §8); a boolean is one, 'VBool'
    VData ConRef [Thunk]
  | VClosure Closure
  | {- | a unit (design §3.10, U1): a newtype around a number, its magnitude
    in base units with its display hint, which is the unit expression it
    prints as (U8); kept apart only so that it prints as a unit wherever
    it is, inside a tuple or a record as at the top
    -}
    VUnit Value
  | {- | a polymorphic value waiting for the argument of its type-level
    variable (design §8); only a type application consumes one
    -}
    VTyAbs VarId Kind (Arg -> Thunk)

-- | A boolean: @True@ or @False@ of the built-in @Bool@ ("Metron.Builtin").
pattern VBool :: Bool -> Value
pattern VBool b <- VData (asBool -> Just b) []
  where
    VBool b = VData (boolC b) []

asBool :: ConRef -> Maybe Bool
asBool = \case
  TrueC -> Just True
  FalseC -> Just False
  _ -> Nothing

{- | A function value: a body under one binder, closed over its environment
and its site.
-}
data Closure = forall n. Closure TyEnv Site (Env n) (TTerm (S n))

{- | The type-level arguments in force at a point of a term, by the
variables of that term's abstractions (design §8). Types are erased except
where a value's runtime shape or dimension comes from them alone: an
empty tensor literal, and the result of a mapping primitive. A variable
with no argument here is unconstrained, and any instance is a valid one.
-}
type TyEnv = Map VarId Arg

-- | Evaluate a closed term that belongs to no definition.
evalClosed :: Config -> Runtime -> TTerm Z -> Thunk
evalClosed cfg rt = evalAt cfg rt (Hash mempty)

{- | Evaluate a closed term as the body of the definition with the given
hash, for its value: abstractions over type-level variables still
unapplied at the top are applied to the variables themselves, which
nothing constrains.
-}
evalAt :: Config -> Runtime -> Hash -> TTerm Z -> Thunk
evalAt cfg rt h t = instantiated =<< evalDefinition cfg rt h t
 where
  instantiated = \case
    VTyAbs v k f -> instantiated =<< f (varArg k v)
    x -> Right x

{- | Evaluate a closed term as the definition with the given hash, as a
reference to it sees it: polymorphic definitions stay abstractions, which
each use applies to its type-level arguments.
-}
evalDefinition :: Config -> Runtime -> Hash -> TTerm Z -> Thunk
evalDefinition cfg rt h = eval cfg rt Map.empty (Site h []) VNil

eval :: Config -> Runtime -> TyEnv -> Site -> Env n -> TTerm n -> Thunk
eval cfg rt = go
 where
  p = precisionOf cfg

  go :: TyEnv -> Site -> Env m -> TTerm m -> Thunk
  go tenv site env = \case
    TVr i -> lookupEnv i env
    TRef h mi (Hint written) -> case rt.typedOf h of
      Nothing -> Left (UnknownRef h)
      Just t -> do
        -- A chart whose step may be zero is named by its reference. A
        -- definition is its own term: its type-level variables are its own.
        v <- first (namedChart (rt.chartName h mi written)) $ case mi of
          Nothing -> fromMaybe (go Map.empty (Site h []) VNil t) (rt.shared h)
          Just i -> case t of
            TCycle vars _ bodies -> cycleMember h i vars bodies
            _ -> Left (BadCycleIndex i)
        -- A declared unit is its own display unit (design §3.2.12).
        case (rt.unitName h mi written, rt.chartName h mi written) of
          (Just u, _) -> asUnit (UnitNamed u) v
          (_, Just s) -> asChart (UnitNamed s) v
          _ -> Right v
    TPrimApp prim ty args ->
      runPrim
        cfg
        rt
        prim
        (resolveType tenv ty)
        (zipWith (\i a -> go tenv (child i) env a) [0 ..] args)
    TLit (LTensor (dims, rs)) _ -> Right (VTensor dims dimOne Nothing (V.fromList (map (Right . Exact) rs)))
    -- Data (design §8): fields stay thunks; a case forces only the scrutinee.
    -- A boolean is data like any other: @if@ is a case on its constructor.
    TCon c _ args -> Right (VData c (zipWith (\i a -> go tenv (child i) env a) [0 ..] args))
    TCase sc _ alts ->
      go tenv (child 0) env sc >>= \case
        VData c fields ->
          case [(i, alt) | (i, alt@(TAlt c' _ _)) <- zip [1 ..] alts, c' == c] of
            (i, TAlt _ bs body) : _ -> go tenv (child i) (vecAppend (attach bs fields) env) body
            [] -> Left (Internal ("case: no alternative for " <> conText c))
        _ -> Left (Internal "case: the scrutinee is not data")
    TLam _ _ body -> Right (VClosure (Closure tenv (child 0) env body))
    TApp f a -> do
      fv <- go tenv (child 0) env f
      v <- apply cfg rt fv (go tenv (child 1) env a)
      -- A moving chart applied is an instant of it (design §3.8), named
      -- after it with the arguments it was applied to.
      Right $ case (v, instantOf site [] (TApp f a)) of
        (VChart c, Just (n, args)) ->
          VChart
            c
              { name = Just (UnitNamed n)
              , applied = Applied [go tenv s env x | (s, x) <- args]
              }
        _ -> v
    TLet _ _ e body -> go tenv (child 1) (VCons (go tenv (child 0) env e) env) body
    TPow t n -> do
      v <- go tenv (child 0) env t
      (x, d, hint) <- scalarFull v
      r <- arith (powM p x n)
      Right $ case v of
        -- A power of a unit is a unit (design §3.10, U2).
        VUnit _ ->
          VUnit
            (num (dimPow n d) (unitHintPow p n =<< hint) r)
        _ -> num (dimPow n d) (hintPow p n =<< hint) r
    -- Fresh unit nudges, one per component (design §3.2.5).
    TNoise k l n ->
      let count = fromInteger n
       in Right
            ( VTensor
                [count]
                dimOne
                Nothing
                (V.generate count (Right . unitNoise k . originOf site l))
            )
    -- One independent nudge per component, the component index in its
    -- identity (design §3.4); a scalar uncertainty applies to every component.
    TUncertain k l x e -> do
      (dims, d, hint, xs) <- tensor =<< go tenv (child 0) env x
      (edims, _, _, es) <- tensor =<< go tenv (child 1) env e
      case (dims, edims) of
        -- v ±σ P: v + cholesky P · gauss n, one statistical nudge per
        -- component, identified by this site (design §3.5).
        ([n], [en, _]) | en == n -> do
          pRows <- chunksOf n <$> sequence (V.toList es)
          lrows <-
            arith
              ( choleskyRows
                  "±σ needs a symmetric covariance"
                  (decideOf cfg)
                  (precisionOf cfg)
                  pRows
              )
          let noise j = unitNoise k (originOf site l j)
              component i =
                ( \vi ->
                    foldl
                      addM
                      vi
                      [mulM (precisionOf cfg) lij (noise j) | (j, lij) <- zip [0 ..] (lrows !! i)]
                )
                  <$> (xs V.! i)
          Right (VTensor dims d hint (V.generate n component))
        _ ->
          let errAt i = if null edims then es V.! 0 else es V.! i
           in Right
                ( VTensor
                    dims
                    d
                    hint
                    (V.imap (\i xm -> uncertain k (originOf site l i) <$> xm <*> errAt i) xs)
                )
    -- shape the other components have, so an error in one component is
    -- only raised when that component is used. The first component's
    -- display unit is kept.
    -- With none, the element type alone says what the stack holds.
    TPack _ ty ts ->
      let results = zipWith (\i t -> tensor =<< go tenv (child i) env t) [0 ..] ts
          known = [(dims, d, hint) | Right (dims, d, hint, _) <- results]
       in case (results, known) of
            ([], _) -> case resolveType tenv ty of
              TTensor sh d -> Right (VTensor (0 : runtimeShape sh) (runtimeDim d) Nothing V.empty)
              _ -> Left (Internal "an empty pack of non-tensors")
            (_, (dims, d, hint) : _) ->
              let block = \case
                    Right (_, _, _, buf) -> buf
                    Left err -> V.replicate (product dims) (Left err)
               in Right (VTensor (length results : dims) d hint (V.concat (map block results)))
            (Left err : _, []) -> Left err
            (Right _ : _, []) -> Left (Internal "unreachable: a tensor with no shape")
    -- Slice out component i: a view, not a copy.
    TProj t i -> do
      v <- go tenv (child 0) env t
      case v of
        VTensor dims d hint buf -> slice dims (\rest -> VTensor rest d hint) buf
        -- A coordinate of a point (design §3.10, F5): the amount along one
        -- of its frame's axes, the step applied, in the chart's step.
        VPoint dims d sc buf -> slice dims (\rest -> VTensor rest d sc.stepHint) buf
        _ -> Left (Internal "projection from a non-tensor")
     where
      slice :: [Int] -> ([Int] -> Vector a -> Value) -> Vector a -> Thunk
      slice dims mk buf = case dims of
        k : rest
          | i < k ->
              let stride = product rest
               in Right (mk rest (V.slice (i * stride) stride buf))
        _ -> Left (Internal ("projection ." <> tshow i <> " out of range"))
    -- An abstraction over a type-level variable waits for its argument
    -- only if the body's runtime needs it; otherwise the body is evaluated
    -- once, shared by every application (design §8).
    TTyLam v k b ->
      let erased = go tenv site env b
       in Right
            ( VTyAbs
                v
                k
                ( if neededAtRuntime v k b
                    then \a -> go (Map.insert v a tenv) site env b
                    else const erased
                )
            )
    TTyApp b a ->
      go tenv site env b >>= \case
        VTyAbs _ _ f -> f (resolveArg tenv a)
        _ -> Left (Internal "type application to a value that is not polymorphic")
    -- A cycle is not itself a value; it is reached through @TRef h (Just i)@.
    TCycle{} -> Left (BadCycleIndex (-1))
   where
    child i = site{path = i : site.path}

  -- The chart name at the head of an application spine, and the arguments
  -- with their sites.
  instantOf ::
    Site -> [(Site, TTerm m)] -> TTerm m -> Maybe (Text, [(Site, TTerm m)])
  instantOf site acc = \case
    TApp g x ->
      instantOf (site{path = 0 : site.path}) ((site{path = 1 : site.path}, x) : acc) g
    TTyApp g _ -> instantOf site acc g
    TRef h mi (Hint written) | not (null acc) -> (,acc) <$> rt.chartName h mi written
    _ -> Nothing

  -- Knot-tying: every member is evaluated in an environment that already
  -- contains all the members. 'vecMap' and 'vecAppend' inspect only the
  -- spine, so the recursion is productive.
  cycleMembers :: TyEnv -> Hash -> Vec k (TTerm (Plus k Z)) -> Vec k Thunk
  cycleMembers tenv h bodies = members
   where
    members = vecMapIndexed (\i -> go tenv (Site h [i]) (vecAppend members VNil)) bodies

  -- A member of a cycle, abstracted over the cycle's type-level variables
  -- as its stored scheme is (every member's lists them all, in order).
  -- The members are evaluated once for every application only when some
  -- body needs the arguments at run time.
  cycleMember ::
    Hash -> Int -> [(VarId, Kind)] -> Vec k (TTerm (Plus k Z)) -> Thunk
  cycleMember h i vars bodies = abstract vars Map.empty
   where
    needed = any (\(v, k) -> any (neededAtRuntime v k) (vecToList bodies)) vars
    shared = member Map.empty
    member tenv = fromMaybe (Left (BadCycleIndex i)) (vecIndex i (cycleMembers tenv h bodies))
    abstract vs tenv = case vs of
      [] -> if needed then member tenv else shared
      (v, k) : rest -> Right (VTyAbs v k (\a -> abstract rest (Map.insert v a tenv)))

{- | The identity of a declared nudge (design §3.2.4): where it sits, unless
it carries a tag.
-}
originOf :: Site -> Label -> Int -> Origin
originOf site l i = case l of
  Tag t -> Tagged t i
  -- No uncertainty carries an axes stamp; it would be its site's.
  _ -> Declared site.definition (reverse site.path) i

tshow :: (Show a) => a -> Text
tshow = T.pack . show

lookupEnv :: Fin n -> Env n -> Thunk
lookupEnv i env = case (i, env) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupEnv j xs

-- Types at run time ---------------------------------------------------------------

{- | Whether a term's run time needs the argument of a type-level variable
(design §8): the element type of an empty pack, the instantiated type of
a mapping primitive, whose result's dimension it gives, or an argument
passed on to another abstraction. Only lengths, shapes and dimensions
are ever needed; a variable of another kind never is.
-}
neededAtRuntime :: VarId -> Kind -> TTerm n -> Bool
neededAtRuntime v k body = k `elem` [KLen, KShape, KDim] && go body
 where
  go :: TTerm m -> Bool
  go = \case
    TVr _ -> False
    TRef{} -> False
    TPrimApp prim ty args -> (prim `elem` typedPrims && mentions ty) || any go args
    TLit{} -> False
    TLam _ _ b -> go b
    TApp f a -> go f || go a
    TLet _ _ e b -> go e || go b
    TCon _ _ args -> any go args
    TCase s _ alts -> go s || any (\(TAlt _ _ b) -> go b) alts
    TPow t _ -> go t
    TNoise{} -> False
    TUncertain _ _ a b -> go a || go b
    TPack _ ty [] -> mentions ty
    TPack _ _ ts -> any go ts
    TProj t _ -> go t
    TTyLam _ _ b -> go b
    TTyApp b a -> mentions (TData selfType [a]) || go b
    TCycle _ _ bodies -> any go (vecToList bodies)
  mentions t = v `elem` map fst (freeVars t)

resolveType :: TyEnv -> Type -> Type
resolveType tenv
  | Map.null tenv = id
  | otherwise = substOnce tenv

-- | A type application's argument under the arguments in force where it is written.
resolveArg :: TyEnv -> Arg -> Arg
resolveArg tenv a
  | Map.null tenv = a
  | otherwise = case substOnce tenv (TData selfType [a]) of
      TData _ [a'] -> a'
      _ -> a

{- | The lengths of a shape at run time. A variable still in it is
unconstrained, so any instance is a valid one: an unknown shape is @[]@,
and an unknown length its offset alone.
-}
runtimeShape :: Shape -> [Int]
runtimeShape = \case
  SNil -> []
  SCons l _ rest -> lenOf l : runtimeShape rest
  SVar _ -> []
 where
  lenOf = \case
    LLit k -> k
    LVar _ k -> k
    LRank _ k -> k

-- | A dimension at run time: an unconstrained variable is dimensionless.
runtimeDim :: Dim -> Dim
runtimeDim d = dimFromAtoms [(a, k) | (a@(Base _), k) <- dimAtoms d]

-- | Apply a function value to an argument thunk.
apply :: Config -> Runtime -> Value -> Thunk -> Thunk
apply cfg rt f arg = case f of
  VClosure (Closure tenv site env body) -> eval cfg rt tenv site (VCons arg env) body
  _ -> Left (Internal "application of a non-function")

arith :: Either ArithError a -> Either EvalError a
arith = either (Left . convert) Right
 where
  convert = \case
    Metron.Affine.DivideByZero -> Metron.Eval.DivideByZero
    Metron.Affine.Domain msg -> Metron.Eval.Domain msg
    Metron.Affine.Undecided msg -> Metron.Eval.Undecided msg

-- Values ---------------------------------------------------------------------------

num :: Dim -> Maybe UnitHint -> Magnitude -> Value
num d hint r = VTensor [] d hint (V.singleton (Right r))

-- | A tensor's parts; a unit's, which are a number's (design §3.10, U1).
tensor :: Value -> Either EvalError ([Int], Dim, Maybe UnitHint, Vector Elem)
tensor = \case
  VTensor dims d hint buf -> Right (dims, d, hint, buf)
  VUnit v -> tensor v
  _ -> Left (Internal "expected a tensor")

point :: Value -> Either EvalError ([Int], Dim, Chart, Vector Elem)
point = \case
  VPoint dims d sc buf -> Right (dims, d, sc, buf)
  _ -> Left (Internal "expected a point")

chartOf :: Value -> Either EvalError Chart
chartOf = \case
  VChart s -> Right s
  _ -> Left (Internal "expected a chart")

-- | A number or a point: what the comparisons order.
ordered :: Value -> Either EvalError Magnitude
ordered = \case
  VPoint [] _ _ buf | V.length buf == 1 -> V.head buf
  v -> scalar v

-- | The one element of a rank-zero tensor.
scalar :: Value -> Either EvalError Magnitude
scalar v = (\(x, _, _) -> x) <$> scalarFull v

scalarFull :: Value -> Either EvalError (Magnitude, Dim, Maybe UnitHint)
scalarFull = \case
  VTensor [] d hint buf | V.length buf == 1 -> (,d,hint) <$> V.head buf
  VUnit v -> scalarFull v
  _ -> Left (Internal "expected a number")

bool :: Value -> Either EvalError Bool
bool = \case
  VBool b -> Right b
  _ -> Left (Internal "expected a boolean")

{- | Make a scalar value its own display unit. Forces its magnitude, which
for a unit definition is a constant.
-}
asUnit :: UnitAtom -> Value -> Thunk
asUnit atom = \case
  VTensor [] d _ buf | V.length buf == 1 -> do
    x <- V.head buf
    Right (VTensor [] d (Just (UnitHint [UnitFactor atom 1 d x] x d False)) buf)
  VUnit v -> VUnit <$> asUnit atom v
  v -> Right v

-- | Name a chart value after the definition it came from.
asChart :: UnitAtom -> Value -> Thunk
asChart atom = \case
  VChart s -> Right (VChart s{name = Just atom})
  v -> Right v

-- Display units ----------------------------------------------------------------------

{- | A hint from its atoms: powers of zero go, units of one dimension that
appear with opposite signs cancel ( rad^-1@ is a number,  m^-1@ is
1000, ^2 m^-1@ is @), and the total factor and dimension are
recomputed from what is left. Nothing when a factor cannot be raised to its
power, which drops the hint.
-}
{- | Two units combined (design §3.10, U2): their magnitudes and dimensions
as two numbers', their hints as written.
-}
unitOp ::
  (Magnitude -> Magnitude -> Either EvalError Magnitude) ->
  (Dim -> Dim -> Dim) ->
  (UnitHint -> UnitHint -> Maybe UnitHint) ->
  Value ->
  Value ->
  Thunk
unitOp f dimF hintF x y = do
  (mx, dx, hx) <- scalarFull x
  (my, dy, hy) <- scalarFull y
  m <- f mx my
  Right (VUnit (num (dimF dx dy) (combine hintF hx hy) m))

-- Primitives -------------------------------------------------------------------------

{- | Run a saturated primitive. Arguments are in source order and are forced
only as the primitive needs them; elementwise operations stay lazy per
element. Dimensions follow the rules of design §4.3, display units those
of §3.2.12, magnitudes those of §3.2. The type is the primitive's, as
instantiated where it is used, under the type-level arguments in force.
-}
runPrim :: Config -> Runtime -> Text -> Type -> [Thunk] -> Thunk
runPrim cfg rt prim ty args = case (prim, args) of
  -- A base unit is a unit (design §3.10, U1).
  (unit, [])
    | Just b <- baseUnit unit ->
        Right
          ( VUnit
              ( num
                  (dimBase b)
                  ( Just
                      ( UnitHint
                          [UnitFactor (UnitBase unit) 1 (dimBase b) (Exact 1)]
                          (Exact 1)
                          (dimBase b)
                          False
                      )
                  )
                  (Exact 1)
              )
          )
  -- A unit's declaration (U7): its size, or a unit, as a unit.
  ("unit", [a]) ->
    a >>= \case
      VUnit v -> Right (VUnit v)
      v -> Right (VUnit v)
  -- The quantity rule after a unit (U4): the literal times the unit's
  -- magnitude, in the unit as written, its units of one dimension
  -- cancelled as a product's are.
  ("scale", [a, u]) -> do
    (dims, _, _, xs) <- tensor =<< a
    (k, d, h) <- scalarFull =<< u
    Right
      ( VTensor
          dims
          d
          (h >>= \hh -> mkHint p hh.atoms)
          (V.map (fmap (\x -> mulM p x k)) xs)
      )
  -- Sum: the left operand's display unit wins.
  ("add", [a, b]) -> elementwise2 (pureOp addM) const (combine smallerUnit) a b
  ("sub", [a, b]) -> elementwise2 (pureOp subM) const (combine smallerUnit) a b
  ("neg", [a]) -> elementwise1 negM a
  ("abs", [a]) -> elementwise1 (absM p) a
  -- The parts of an enclosure as the printer collapses it (design §3.2.9,
  -- §3.2.10), each exact but sd: the midpoint, the bound radius
  -- Σ_bound |cᵢ| + slack, and the standard deviation √(Σ_stat cᵢ²), exact
  -- when the variance is a square and otherwise an enclosure of the root.
  -- A value marked non-linear has no mean and σ that describe it (design
  -- §3.2), so mid and sd refuse it; its bound is still rigorous.
  ("mid", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    Right
      (VTensor dims d hint (V.map (>>= described "mid" (Right . Exact . midpoint)) buf))
  ("bound", [a]) -> elementwise1 (\x -> Exact (collapse x).bound) a
  ("sd", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    let root x = arith (sqrtM p (Exact (collapse x).variance))
    Right (VTensor dims d hint (V.map (>>= described "sd" root) buf))
  ("emul", [a, b]) -> elementwise2 (pureOp (mulM p)) dimMul (combine (hintMul p)) a b
  ("ediv", [a, b]) ->
    elementwise2
      (\x y -> arith (divM p x y))
      dimDiv
      (\h1 h2 -> combine (hintMul p) h1 (hintInv p =<< h2))
      a
      b
  -- Tensor product: ranks add, dimensions multiply, every pair of elements
  -- multiplied.
  ("outer", [a, b]) -> do
    va <- a
    vb <- b
    case (va, vb) of
      -- Two units (design §3.10, U2).
      (VUnit x, VUnit y) -> unitOp (\m n -> Right (mulM p m n)) dimMul (unitHintMul p) x y
      _ -> do
        (d1, dim1, h1, xs) <- tensor va
        (d2, dim2, h2, ys) <- tensor vb
        allocation (d1 ++ d2)
        Right
          ( VTensor
              (d1 ++ d2)
              (dimMul dim1 dim2)
              (combine (hintMul p) h1 h2)
              (V.concatMap (\x -> V.map (\y -> mulM p <$> x <*> y) ys) xs)
          )
  -- Contracting product: the left operand's last index against the right
  -- operand's first.
  ("dot", [a, b]) -> do
    (dl, dim1, h1, xs) <- tensor =<< a
    (dr, dim2, h2, ys) <- tensor =<< b
    case (reverse dl, dr) of
      (n : d1rev, n' : d2)
        | n == n' -> do
            allocation (reverse d1rev ++ d2)
            let d1 = reverse d1rev
                stride2 = product d2
                rows = product d1
                element k =
                  let (i, j) = k `divMod` stride2
                   in sumM
                        <$> sequence
                          [ mulM p <$> (xs V.! (i * n + c)) <*> (ys V.! (c * stride2 + j))
                          | c <- [0 .. n - 1]
                          ]
            Right
              ( VTensor
                  (d1 ++ d2)
                  (dimMul dim1 dim2)
                  (combine (hintMul p) h1 h2)
                  (V.generate (rows * stride2) element)
              )
      _ -> Left (Internal "dot: operand shapes do not contract")
  ("div", [a, b]) -> do
    va <- a
    vb <- b
    case (va, vb) of
      -- Two units (design §3.10, U2).
      (VUnit x, VUnit y) -> unitOp (\m n -> arith (divM p m n)) dimDiv (unitHintDiv p) x y
      _ -> do
        (dims, d1, h1, xs) <- tensor va
        (k, d2, h2) <- scalarFull vb
        Right
          ( VTensor
              dims
              (dimDiv d1 d2)
              (combine (hintMul p) h1 (hintInv p =<< h2))
              (V.map (\x -> x >>= \x' -> arith (divM p x' k)) xs)
          )
  ("eq", [a, b]) -> VBool <$> equal a b
  ("ne", [a, b]) -> VBool . not <$> equal a b
  ("lt", [a, b]) -> compareWith (== LT) a b
  ("le", [a, b]) -> compareWith (/= GT) a b
  ("gt", [a, b]) -> compareWith (== GT) a b
  ("ge", [a, b]) -> compareWith (/= LT) a b
  -- Lazy in the second argument.
  ("and", [a, b]) -> do
    x <- bool =<< a
    if x then VBool <$> (bool =<< b) else Right (VBool False)
  ("or", [a, b]) -> do
    x <- bool =<< a
    if x then Right (VBool True) else VBool <$> (bool =<< b)
  ("not", [a]) -> VBool . not <$> (bool =<< a)
  ("floor", [a]) -> dimensionless (arith . floorM (decideOf cfg) p) a
  ("ceil", [a]) -> dimensionless (arith . ceilM (decideOf cfg) p) a
  ("round", [a]) -> dimensionless (arith . roundM (decideOf cfg) p) a
  -- Elementary functions (design §3.2.2). Their arguments are dimensionless
  -- by type, except sqrt, which halves the dimension.
  ("sqrt", [a]) -> do
    (x, d, _) <- scalarFull =<< a
    r <- arith (sqrtM p x)
    d2 <-
      maybe
        (Left (Internal "sqrt of a dimension that is not a square"))
        Right
        (dimRoot 2 d)
    Right (num d2 Nothing r)
  ("exp", [a]) -> dimensionless (Right . expM p) a
  ("log", [a]) -> dimensionless (arith . logM p) a
  ("sin", [a]) -> dimensionless (Right . sinM p) a
  ("cos", [a]) -> dimensionless (Right . cosM p) a
  ("tan", [a]) -> dimensionless (arith . tanM p) a
  ("asin", [a]) -> angle (arith . asinM p) a
  ("acos", [a]) -> angle (arith . acosM p) a
  ("atan", [a]) -> angle (Right . atanM p) a
  ("sinh", [a]) -> dimensionless (Right . sinhM p) a
  ("cosh", [a]) -> dimensionless (Right . coshM p) a
  ("tanh", [a]) -> dimensionless (arith . tanhM p) a
  ("atan2", [a, b]) -> do
    y <- scalar =<< a
    x <- scalar =<< b
    num (dimBase Ang) Nothing <$> arith (atan2M p y x)
  ("pi", []) -> Right (num dimOne Nothing (piM p))
  -- Euclidean norm of a vector.
  ("norm", [a]) -> do
    (_, d, hint, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    r <- arith (sqrtM p (sumM [mulM p x x | x <- xs]))
    Right (num d hint r)
  ("det", [a]) -> do
    (dims, _, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        num dimOne Nothing <$> arith (determinant p n rows)
      _ -> Left (Internal "det of a non-square matrix")
  ("cholesky", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        l <-
          arith (choleskyRows "cholesky needs a symmetric matrix" (decideOf cfg) p rows)
        d2 <-
          maybe
            (Left (Internal "cholesky of a dimension that is not a square"))
            Right
            (dimRoot 2 d)
        Right (VTensor [n, n] d2 Nothing (V.fromList (map Right (concat l))))
      _ -> Left (Internal "cholesky of a non-square matrix")
  -- Σ cᵢ cᵢᵀ over the statistical nudges (design §3.5): exact, from the
  -- coefficients. The covariance is the cross-covariance of a vector with
  -- itself, with no display unit of its own.
  ("covariance", [a]) -> do
    (_, d, _, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    Right (covarianceMatrix cfg (dimPow 2 d) Nothing xs xs)
  -- Σ cᵢ c'ⱼᵀ over the statistical nudges the two vectors share: exact, in
  -- the product of their dimensions and display units, as for outer.
  ("crossCovariance", [a, b]) -> do
    (_, d1, h1, xs) <- tensor =<< a
    (_, d2, h2, ys) <- tensor =<< b
    as <- sequence (V.toList xs)
    bs <- sequence (V.toList ys)
    Right (covarianceMatrix cfg (dimMul d1 d2) (hintProduct p h1 h2) as bs)
  ("inverse", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        inv <- arith (invert p n rows)
        Right (VTensor [n, n] (dimInv d) Nothing (V.fromList (map Right (concat inv))))
      _ -> Left (Internal "inverse of a non-square matrix")
  -- Wedge product: the antisymmetrised outer product, (a ∧ b)ⱼₖ = aⱼbₖ − aₖbⱼ,
  -- stored as an ordinary matrix. Entries are thunks, so a consumer that
  -- reads three of the nine (the 3D Hodge star) computes only those.
  ("wedge", [a, b]) -> do
    (da, dim1, h1, xs) <- tensor =<< a
    (_, dim2, h2, ys) <- tensor =<< b
    case da of
      [n] ->
        allocation [n, n]
          >> Right
            ( VTensor
                [n, n]
                (dimMul dim1 dim2)
                (combine (hintMul p) h1 h2)
                ( V.generate
                    (n * n)
                    ( \k ->
                        let (j, i) = k `divMod` n
                         in (\x y x' y' -> subM (mulM p x y) (mulM p x' y'))
                              <$> (xs V.! j)
                              <*> (ys V.! i)
                              <*> (xs V.! i)
                              <*> (ys V.! j)
                    )
                )
            )
      _ -> Left (Internal "wedge of non-vectors")
  -- 3D Hodge star of a bivector: (⋆M) = (M₁₂, M₂₀, M₀₁).
  ("star", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    case dims of
      [3, 3] -> Right (VTensor [3] d hint (V.fromList [buf V.! 5, buf V.! 6, buf V.! 1]))
      _ -> Left (Internal "star of a non-3x3 matrix")
  ("transpose", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    case dims of
      [r, c] ->
        Right
          ( VTensor
              [c, r]
              d
              hint
              (V.generate (r * c) (\k -> let (j, i) = k `divMod` r in buf V.! (i * c + j)))
          )
      _ -> Left (Internal "transpose of a non-matrix")
  -- The matrix exponential (design §3.3): Rodrigues' formula for a single
  -- plane, the scaled and squared series otherwise ('matrixExp').
  ("expm", [a]) -> do
    (dims, _, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        r <- arith (matrixExp p n rows)
        Right (VTensor [n, n] dimOne Nothing (V.fromList (map Right (concat r))))
      _ -> Left (Internal "expm of a non-square matrix")
  -- R applied along every axis of a tensor (design §3.3): R v, R P Rᵀ, and
  -- R on each index at any rank, one contraction per axis. The type cannot
  -- say that every length is R's, so this is the one primitive with a
  -- runtime shape check (design §4.3).
  ("transformBy", [r, a]) -> do
    (rdims, _, _, rbuf) <- tensor =<< r
    (dims, d, hint, buf) <- tensor =<< a
    case rdims of
      [n, n']
        | n == n' ->
            if all (== n) dims
              then
                Right
                  (VTensor dims d hint (foldl (alongAxis n rbuf dims) buf [0 .. length dims - 1]))
              else
                Left
                  ( Metron.Eval.Domain
                      ( "transformBy: every axis must have length n: the matrix is "
                          <> T.pack (show n <> " × " <> show n)
                          <> " and the tensor's lengths are "
                          <> ("[" <> T.intercalate ", " (map (T.pack . show) dims) <> "]")
                      )
                  )
      _ -> Left (Internal "transformBy of a non-square matrix")
  -- Contraction (design §4.2): the sum over the diagonal of two positions
  -- of equal length, an affine sum, so shared nudges correlate as in norm.
  ("contract", [i, j, a]) -> do
    pos <- concat <$> mapM positions [i, j]
    (dims, d, hint, buf) <- tensor =<< a
    case pos of
      [x, y]
        | let lo = min x y
        , let hi = max x y
        , lo /= hi
        , hi < length dims
        , dims !! lo == dims !! hi ->
            let st = strides dims
                dropped = [(l, s) | (q, l, s) <- zip3 [0 ..] dims st, q /= lo, q /= hi]
                outDims = map fst dropped
                diagonal = st !! lo + st !! hi
                element k =
                  let base = sum (zipWith (*) (unflatten outDims k) (map snd dropped))
                   in sumM <$> sequence [buf V.! (base + c * diagonal) | c <- [0 .. dims !! lo - 1]]
             in Right (VTensor outDims d hint (V.generate (product outDims) element))
      _ -> Left (Internal "contract: positions out of range or of different lengths")
  -- Index permutation: position q of the result is position p_q of the
  -- operand; lengths after the permuted ones stay where they are.
  ("permute", [ps, a]) -> do
    perm <- positions ps
    (dims, d, hint, buf) <- tensor =<< a
    let (front, rest) = splitAt (length perm) dims
    if length front /= length perm || any (>= length front) perm
      then Left (Internal "permute: positions out of range")
      else
        let st = strides dims
            outFront = map (front !!) perm
            block = product rest
            element k =
              let (q, r) = k `divMod` block
               in buf V.! (sum (zipWith (*) (unflatten outFront q) (map (st !!) perm)) + r)
         in Right
              ( VTensor
                  (outFront ++ rest)
                  d
                  hint
                  (V.generate (product outFront * block) element)
              )
  -- A slice along axis k at position i (design §2.10): a strided gather of
  -- the result's components, which are not forced.
  ("slice", [k, i, a]) -> do
    axis <- positions k
    pos <- positions i
    (dims, d, hint, buf) <- tensor =<< a
    case (axis, pos) of
      ([ax], [at])
        | (before, len : after) <- splitAt ax dims
        , at < len ->
            let inner = product after
                element q =
                  let (o, r) = q `divMod` inner
                   in buf V.! ((o * len + at) * inner + r)
             in Right
                  ( VTensor
                      (before ++ after)
                      d
                      hint
                      (V.generate (product before * inner) element)
                  )
      _ -> Left (Internal "slice: axis or position out of range")
  ("vmap", [f, a]) -> do
    fv <- f
    (dims, d, _, buf) <- tensor =<< a
    let results =
          V.map (apply cfg rt fv . Right . VTensor [] d Nothing . V.singleton) buf
    -- The result's dimension is the function's result's, which the
    -- instantiated type says: no element is forced to find it, and an
    -- empty tensor has one too.
    outDim <- resultDim
    Right (VTensor dims outDim Nothing (V.map (>>= scalar) results))
  -- The positions of a vector as exact dimensionless values; the argument's
  -- elements are not forced.
  ("indices", [a]) -> do
    (dims, _, _, _) <- tensor =<< a
    case dims of
      [k] ->
        Right (VTensor [k] dimOne Nothing (V.generate k (Right . Exact . fromIntegral)))
      _ -> Left (Internal "indices of a non-vector")
  -- vmap over two tensors of one shape, with the same strictness.
  ("vzipWith", [f, a, b]) -> do
    fv <- f
    (dims, d1, _, xs) <- tensor =<< a
    (_, d2, _, ys) <- tensor =<< b
    let element u x = Right (VTensor [] u Nothing (V.singleton x))
        results =
          V.zipWith
            (\x y -> apply cfg rt fv (element d1 x) >>= \g -> apply cfg rt g (element d2 y))
            xs
            ys
    outDim <- resultDim
    Right (VTensor dims outDim Nothing (V.map (>>= scalar) results))
  -- vmap that first passes each component's multi-index, read off its
  -- row-major offset, as a vector of exact dimensionless naturals as long
  -- as the rank (design §3.3). Same strictness as vmap.
  ("timap", [f, a]) -> do
    fv <- f
    (dims, d, _, buf) <- tensor =<< a
    let rank = length dims
        index q =
          VTensor
            [rank]
            dimOne
            Nothing
            (V.fromList (map (Right . Exact . fromIntegral) (unflatten dims q)))
        results =
          V.imap
            ( \q x ->
                apply cfg rt fv (Right (index q))
                  >>= \g -> apply cfg rt g (Right (VTensor [] d Nothing (V.singleton x)))
            )
            buf
    outDim <- resultDim
    Right (VTensor dims outDim Nothing (V.map (>>= scalar) results))
  -- Conversion: the value, displayed in the unit's terms. A unit expression
  -- without a display unit of its own (a bare number) clears the hint.
  ("to", [a, u]) -> do
    (dims, d, _, buf) <- tensor =<< a
    (_, _, uh) <- scalarFull =<< u
    -- A unit written twice is one (design §3.10, U9): to dozen/dozen
    -- shows a plain number.
    let shown h = (\h' -> h'{pinned = True}) <$> mkHintAs PreserveExpression p (mergeAtoms [] h.atoms)
    Right (VTensor dims d (shown =<< uh) buf)
  -- Charts (design §3.10, F3, F10). The frame and axes a chart mints are
  -- type-level tags with nothing to compute; every clause is a list of
  -- none or one, and an omitted one is inherited: on a space, the origin
  -- zero and the step the space's base unit; on a chart, its parent's.
  ("mkRoot", [frameT, _, spaceT, st, o, g, w]) -> do
    hf <- tagHash =<< frameT
    hs <- tagHash =<< spaceT
    (lens, d) <- case rt.typeDefOf hs >>= spaceOf hs of
      Just sp -> Right ([k | LLit k <- fromMaybe [] (spaceLens sp)], sp.dim)
      Nothing -> Left (Internal "mkRoot: a space with no declaration")
    stepI <- maybe (Right (Exact 1, d, Nothing)) scalarFull =<< optional st
    amount <-
      maybe (Right (V.replicate (product lens) (Exact 0))) amountOf =<< optional o
    gens <- mapM antisymmetric =<< listElems =<< g
    spinM <- traverse amountOf =<< optional w
    mkChart hf (frameMoving hf) stepI lens amount Nothing gens spinM
  ("mkChart", [frameO, _, par, st, o, g, w]) -> do
    parentChart <- chartOf =<< par
    minted <- traverse tagHash =<< optional frameO
    stepI <-
      maybe
        (Right (parentChart.step, parentChart.dim, parentChart.stepHint))
        scalarFull
        =<< optional st
    amount <-
      maybe (Right (V.replicate (V.length parentChart.origin) (Exact 0))) amountOf
        =<< optional o
    gens <- mapM antisymmetric =<< listElems =<< g
    spinM <- traverse amountOf =<< optional w
    mkChart
      (fromMaybe parentChart.frame minted)
      (maybe parentChart.moving frameMoving minted)
      stepI
      parentChart.dims
      amount
      (Just parentChart)
      gens
      spinM
  -- A point holds its coordinates on its frame with the step applied
  -- (design §3.10, F6): an exact multiplication. The origin and the
  -- rotation are applied by a conversion only.
  ("pointOn", [s, x]) -> do
    sc <- chartOf =<< s
    (_, _, _, ks) <- tensor =<< x
    Right (VPoint sc.dims sc.dim sc (V.map (fmap (\k -> mulM p k sc.step)) ks))
  -- Within a frame, coordinate arithmetic. A difference carries the step
  -- unit of the chart both points were written on.
  ("pointAdd", [pt, v]) -> do
    (dims, d, sc, buf) <- point =<< pt
    (_, _, _, vs) <- tensor =<< v
    Right (VPoint dims d sc (V.zipWith (\m dv -> addM <$> m <*> dv) buf vs))
  ("pointSub", [pt, q]) -> do
    (dims, d, sc1, m1) <- point =<< pt
    (_, _, sc2, m2) <- point =<< q
    let hint = if sc1.name == sc2.name then sc1.stepHint else Nothing
    Right (VTensor dims d hint (V.zipWith (\x y -> subM <$> x <*> y) m1 m2))
  -- A point to another chart (design §3.10, F5, F7): through the space's
  -- base, from its frame's configuration, which a chart with no parameters
  -- has one of, so the chart it was written on serves; one with parameters
  -- names it with `from`.
  ("toChart", [pt, s]) -> do
    (dims, d, src, buf) <- point =<< pt
    sc <- chartOf =<< s
    when src.moving (Left (Metron.Eval.Domain (takesArguments src)))
    convertPoint src sc dims d buf
  ("fromTo", [pt, c0, s]) -> do
    (dims, d, _, buf) <- point =<< pt
    src <- chartOf =<< c0
    sc <- chartOf =<< s
    convertPoint src sc dims d buf
  -- An amount along a chart's axes (design §3.10, F10): from the space's
  -- base axes, or from a configuration's, by the rotations alone, along its
  -- leading position.
  ("toAxes", [v, s]) -> do
    sc <- chartOf =<< s
    turnAmount [sc.rotationInverse] =<< v
  ("axesFromTo", [v, c0, s]) -> do
    src <- chartOf =<< c0
    sc <- chartOf =<< s
    let (up, down) = chartRoute src sc
    turnAmount (map (.relativeRotation) up ++ map (.relativeRotationInverse) down)
      =<< v
  -- A chart's absolute rotation (design §3.8): its axes, as columns along
  -- the base axes, computed once with the chart. Exactly the identity for a
  -- chart that is not turned.
  -- A vector with anonymous axes relabelled as along a chart's (design
  -- §3.9): the numbers do not change.
  ("withAxes", [_, v]) -> v
  ("rotationOf", [s]) -> do
    sc <- chartOf =<< s
    let n = V.length sc.origin
    rm <- fromMaybe (Right (identityMatrix n)) sc.rotation
    Right (VTensor [n, n] dimOne Nothing (V.map Right rm))
  -- A chart's absolute angular velocity and the velocity of its origin,
  -- along the base axes (design §3.8): exactly zero for a chart that does
  -- not move.
  ("spinOf", [s]) -> do
    sc <- chartOf =<< s
    let n = V.length sc.origin
    ws <- fromMaybe (Right (V.replicate n (Exact 0))) sc.spinAbs
    Right (VTensor [n] (dimInv (dimBase T)) Nothing (V.map Right ws))
  ("originVelocityOf", [s]) -> do
    sc <- chartOf =<< s
    let n = V.length sc.origin
    vs <- fromMaybe (Right (V.replicate n (Exact 0))) sc.originVelocity
    Right (VTensor [n] (dimDiv sc.dim (dimBase T)) Nothing (V.map Right vs))
  -- Its origin, an amount from the space's base origin along the base
  -- axes (design §3.10, part F, as built).
  ("originOf", [s]) -> do
    sc <- chartOf =<< s
    Right (VTensor [V.length sc.origin] sc.dim Nothing (V.map Right sc.origin))
  _
    | primArity prim == Just (length args) ->
        Left (Unsupported (prim <> ": not implemented yet"))
    | otherwise ->
        Left
          ( Internal
              ( "primitive "
                  <> prim
                  <> " is unknown or applied to the wrong number of arguments"
              )
          )
 where
  p = precisionOf cfg
  -- An accessor of a mean or a σ, refusing a value marked non-linear.
  described what f x = case nonLinearAt cfg.nonlinear x of
    Just sk ->
      Left
        ( Metron.Eval.Domain
            ( what
                <> " of a value marked non-linear by "
                <> sk.operation
                <> ": a mean and a σ do not describe it (design §3.2)"
            )
        )
    Nothing -> f x
  -- The dimension of the result the instantiated type gives.
  resultDim = case finalResult ty of
    TTensor _ d -> Right (runtimeDim d)
    _ -> Left (Internal (prim <> ": a result that is not a tensor"))
  finalResult = \case
    TFun _ r -> finalResult r
    r -> r
  -- A chart's absolute frame (design §3.8). The origin is stored from the
  -- base origin along the base axes: the parent's origin plus the amount it
  -- was given at, which is along the parent's axes and so turned by the
  -- parent's absolute rotation. The rotation and its inverse are left
  -- lazy, to be computed once when first used ('chartFrame'), and so are
  -- the kinematics ('chartMotion').
  mkChart frameH movingF (stepM, d, stepHint) odims amount parentChart gens spinM = do
    invertibleStep stepM
    let n = V.length amount
    -- R_parent a: the amount along the base axes.
    along <- case parentChart >>= (.rotation) of
      Nothing -> Right amount
      Just r -> do
        rm <- r
        Right (rotateVector p n rm amount)
    let originM = maybe along (\pc -> V.zipWith addM pc.origin along) parentChart
        (forward, backward) = chartFrame p n parentChart gens
        (localForward, localBackward) = chartFrame p n Nothing gens
        (spinAbsM, originVelocityM) = chartMotion p n parentChart forward along spinM
    Right
      ( VChart
          ( Chart
              Nothing
              stepM
              stepHint
              originM
              amount
              odims
              d
              parentChart
              gens
              forward
              backward
              localForward
              localBackward
              spinM
              spinAbsM
              originVelocityM
              (Applied [])
              frameH
              movingF
          )
      )
  -- A clause of a chart's declaration: a list of none or one (design
  -- §3.10, F10).
  optional x =
    (x >>= listElems) >>= \case
      [] -> Right Nothing
      [y] -> Just <$> y
      _ -> Left (Internal "a chart's clause of more than one")
  amountOf v = do
    (_, _, _, buf) <- tensor v
    V.fromList <$> sequence (V.toList buf)
  tagHash = \case
    VData (UserCon h _) [] -> Right h
    _ -> Left (Internal "expected a frame, axes or a space")
  frameMoving h = maybe False (fromMaybe False . frameDefMoving) (rt.typeDefOf h)
  -- Walk only the edges below the shared configuration. Its uncertainty
  -- cancels structurally, before affine arithmetic can lose correlation.
  convertPoint src sc dims d buf
    | src.frame == sc.frame = Right (VPoint dims d sc buf)
    | otherwise = do
        xs <- V.fromList <$> sequence (V.toList buf)
        let n = V.length xs
        let (up, down) = chartRoute src sc
            ascend x c = V.zipWith addM c.localOrigin <$> turn n c.relativeRotation x
            descend x c = turn n c.relativeRotationInverse (V.zipWith subM x c.localOrigin)
        above <- foldM ascend xs up
        coords <- foldM descend above down
        Right (VPoint dims d sc (V.map Right coords))
  turn n r xs = case r of
    Nothing -> Right xs
    Just rm -> (\m -> rotateVector p n m xs) <$> rm
  -- An amount turned by rotations in order along its leading position.
  turnAmount rs v = do
    (dims, d, hint, buf) <- tensor v
    case dims of
      n : _ -> do
        ms <- sequence (catMaybes rs)
        Right
          ( VTensor
              dims
              d
              hint
              (foldl (\b m -> alongAxis n (V.map Right m) dims b 0) buf ms)
          )
      [] -> Right (VTensor dims d hint buf)
  -- A generator of a chart: an exactly antisymmetric matrix.
  antisymmetric g = do
    (gdims, _, _, gbuf) <- tensor =<< g
    gs <- sequence gbuf
    let n = case gdims of
          [k, _] -> k
          _ -> 0
        entry i j = gs V.! (i * n + j)
    if and [entry j i == negM (entry i j) | i <- [0 .. n - 1], j <- [i .. n - 1]]
      then Right gs
      else
        Left
          ( Metron.Eval.Domain
              "the generator of a chart must be antisymmetric: a bivector, such as rotz θ or a ∧ b"
          )
  pureOp op x y = Right (op x y)
  elementwise1 op a = do
    (dims, d, hint, buf) <- tensor =<< a
    Right (VTensor dims d hint (V.map (fmap op) buf))
  elementwise2 op dimOp hintOp a b = do
    (dims, d1, h1, xs) <- tensor =<< a
    (_, d2, h2, ys) <- tensor =<< b
    Right
      ( VTensor
          dims
          (dimOp d1 d2)
          (hintOp h1 h2)
          (V.zipWith (\x y -> do x' <- x; y' <- y; op x' y') xs ys)
      )
  -- A scalar function whose result is a bare dimensionless number.
  dimensionless f a = do
    x <- scalar =<< a
    num dimOne Nothing <$> f x
  -- A scalar function whose result is an angle in radians.
  angle f a = do
    x <- scalar =<< a
    num (dimBase Ang) Nothing <$> f x
  compareWith decide a b = do
    x <- ordered =<< a
    y <- ordered =<< b
    VBool . decide <$> arith (compareM (decideOf cfg) p x y)
  -- Tensors of one shape (lint agrees), data or points: the equality
  -- instances of design §4.2. Tensors are equal when every component is
  -- decided equal (design §3.2.9).
  equal a b = do
    x <- a
    y <- b
    case (x, y) of
      (VTensor _ _ _ xs, VTensor _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        and <$> mapM (\(u, v) -> arith (equalM (decideOf cfg) p u v)) (zip xs' ys')
      (VData c xs, VData c' ys)
        | c == c' && length xs == length ys -> and <$> zipWithM equal xs ys
        | otherwise -> Right False
      (VPoint _ _ _ xs, VPoint _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        and <$> mapM (\(u, v) -> arith (equalM (decideOf cfg) p u v)) (zip xs' ys')
      _ ->
        Left
          (Internal "==: operands are not both tensors, both data or both points")
  matrixRows n buf = do
    xs <- sequence (V.toList buf)
    pure (chunks n xs)
  chunks n xs
    | null xs = []
    | otherwise = let (r, rest) = splitAt n xs in r : chunks n rest
  -- R contracted into one axis of a tensor whose lengths are all n: the
  -- component at index i on that axis is Σⱼ R_ij t_(…j…). Lazy per element.
  alongAxis n rbuf dims buf ax =
    let st = strides dims !! ax
        element k =
          let i = (k `div` st) `mod` n
              base = k - i * st
           in sumM
                <$> sequence
                  [ mulM p <$> (rbuf V.! (i * n + j)) <*> (buf V.! (base + j * st))
                  | j <- [0 .. n - 1]
                  ]
     in V.generate (product dims) element

sumM :: [Magnitude] -> Magnitude
sumM = foldl' addM (Exact 0)

{- | Whether a tensor of these lengths may be allocated: at most
'componentLimit' components, counted without overflow (design §3.3). A
product whose operands are each within the limit can exceed it.
-}
allocation :: [Int] -> Either EvalError ()
allocation dims
  | n > componentLimit =
      Left
        ( Metron.Eval.Domain
            ( "the result would have "
                <> tshow n
                <> " components: a tensor has at most "
                <> tshow componentLimit
                <> " components"
            )
        )
  | otherwise = Right ()
 where
  n = product (map toInteger dims)

-- Index arithmetic ----------------------------------------------------------------------

{- | The literal index positions of @contract@, @permute@ or @slice@: a number or a
vector of exact naturals (the desugarer admits nothing else).
-}
positions :: Thunk -> Either EvalError [Int]
positions t = do
  (_, _, _, buf) <- tensor =<< t
  xs <- sequence (V.toList buf)
  mapM natural xs
 where
  natural = \case
    Exact r
      | denominator r == 1
      , r >= 0
      , numerator r < componentLimit ->
          Right (fromInteger (numerator r))
    _ -> Left (Internal "an index position is not a literal natural number")

-- | The row-major strides of a shape.
strides :: [Int] -> [Int]
strides = drop 1 . scanr (*) 1

-- | The multi-index of a row-major offset into a shape.
unflatten :: [Int] -> Int -> [Int]
unflatten dims k = zipWith (\s n -> (k `div` s) `mod` n) (strides dims) dims

-- Linear algebra ----------------------------------------------------------------------

-- Charts ------------------------------------------------------------------------------

{- | The edges from source to their common configuration, then down to the
target. Equality here is structural equality of the affine forms defining
the pose, not numerical equality of enclosures or equality of frame names.
Different configurations of the same moving frame must not cancel. Steps
and display names do not affect a pose; rescalings add no edge.
-}
chartRoute :: Chart -> Chart -> ([Chart], [Chart])
chartRoute source target = shared (reverse (path source)) (reverse (path target))
 where
  path c = case c.parent of
    Just parent
      | c.frame == parent.frame
      , null c.generators
      , V.all (== Exact 0) c.localOrigin ->
          path parent
    parent -> c : maybe [] path parent
  shared (a : as) (b : bs)
    | a.frame == b.frame
    , a.dims == b.dims
    , a.dim == b.dim
    , a.localOrigin == b.localOrigin
    , a.generators == b.generators =
        shared as bs
  shared as bs = (reverse as, bs)

{- | The absolute rotation of a chart and its inverse (design §3.8), from its
parent's and its own generators, as lazy values: @R = R_parent · expm g₁ ·
expm g₂ · …@ and @R⁻¹ = … · expm (−g₂) · expm (−g₁) · R_parent⁻¹@. The
inverse comes from the generators, each inverted exactly by negation, and
never from inverting a matrix of enclosures. 'Nothing' is the identity: no
generator here or above.
-}
chartFrame ::
  Precision ->
  Int ->
  Maybe Chart ->
  [Vector Magnitude] ->
  ( Maybe (Either EvalError (Vector Magnitude))
  , Maybe (Either EvalError (Vector Magnitude))
  )
chartFrame p n parentChart gens =
  ( compose (parentChart >>= (.rotation)) (local id gens)
  , compose (local (V.map negM) (reverse gens)) (parentChart >>= (.rotationInverse))
  )
 where
  local _ [] = Nothing
  local sign gs = Just (foldr1 (\a b -> matrixProduct p n <$> a <*> b) (map (expOf . sign) gs))
  expOf g = do
    rows <- arith (matrixExp p n (chunk (V.toList g)))
    Right (V.fromList (concat rows))
  chunk xs
    | null xs = []
    | otherwise = let (r, rest) = splitAt n xs in r : chunk rest
  compose Nothing b = b
  compose a Nothing = a
  compose (Just a) (Just b) = Just (matrixProduct p n <$> a <*> b)

{- | The absolute kinematics of a chart (design §3.8), from its parent's,
its absolute rotation @R_abs@, the amount its origin is given at turned
to the base axes (@R_parent a@), and its own spin @ω@ along its own axes:

@
ω_abs = ω_parent + R_abs ω
v_o   = v_parent + ω_parent × (R_parent a)
@

An origin is fixed relative to its parent, so the origin moves only with
the parent's frame. Both are lazy, and 'Nothing' is exactly zero: no
chart here or above spins.
-}
chartMotion ::
  Precision ->
  Int ->
  Maybe Chart ->
  Maybe (Either EvalError (Vector Magnitude)) ->
  Vector Magnitude ->
  Maybe (Vector Magnitude) ->
  ( Maybe (Either EvalError (Vector Magnitude))
  , Maybe (Either EvalError (Vector Magnitude))
  )
chartMotion p n parentChart rotationAbs along spinM =
  ( plus (parentChart >>= (.spinAbs)) (turn <$> spinM)
  , case parentChart of
      Nothing -> Nothing
      Just pc -> case (pc.originVelocity, pc.spinAbs) of
        (Nothing, Nothing) -> Nothing
        (vp, wp) ->
          Just $ do
            v <- fromMaybe (Right zeros) vp
            transport <- maybe (Right zeros) (>>= \w -> cross3 p w along) wp
            Right (V.zipWith addM v transport)
  )
 where
  zeros = V.replicate n (Exact 0)
  turn w = case rotationAbs of
    Nothing -> Right w
    Just r -> (\rm -> rotateVector p n rm w) <$> r
  plus Nothing b = b
  plus a Nothing = a
  plus (Just a) (Just b) = Just (V.zipWith addM <$> a <*> b)

-- | The cross product of two three-vectors of magnitudes.
cross3 ::
  Precision ->
  Vector Magnitude ->
  Vector Magnitude ->
  Either EvalError (Vector Magnitude)
cross3 p a b
  | V.length a == 3 && V.length b == 3 =
      let x i j = subM (mulM p (a V.! i) (b V.! j)) (mulM p (a V.! j) (b V.! i))
       in Right (V.fromList [x 1 2, x 2 0, x 0 1])
  | otherwise = Left (Internal "a spin is a three-vector")

{- | A chart's coordinates are its amounts divided by its step (design
§3.10, F6), so the step must be invertible: its enclosure must exclude
zero. A negative step reverses the chart's direction and is allowed.
-}
invertibleStep :: Magnitude -> Either EvalError ()
invertibleStep step
  | step == Exact 0 = Left (ChartStep Nothing "its step is zero")
  | abs (midpoint step) <= boundRadius step =
      Left (ChartStep Nothing "its step's enclosure reaches zero")
  | otherwise = Right ()

-- | Name a chart whose step may be zero after the reference that reached it.
namedChart :: Maybe Text -> EvalError -> EvalError
namedChart name = \case
  ChartStep Nothing why | Just _ <- name -> ChartStep name why
  err -> err

{- | The coordinates of a point on the chart it was written on (design
§3.10, F6): its coordinates on its frame, the step divided out.
-}
coordinatesOn ::
  Precision -> Chart -> [Magnitude] -> Either EvalError [Magnitude]
coordinatesOn p c = arith . mapM (\x -> divM p x c.step)

-- | The elements of a list value, as thunks.
listElems :: Value -> Either EvalError [Thunk]
listElems = \case
  VData NilC [] -> Right []
  VData ConsC [x, xs] -> (x :) <$> (listElems =<< xs)
  _ -> Left (Internal "expected a list")

-- | The @n × n@ identity, row-major and exact.
identityMatrix :: Int -> Vector Magnitude
identityMatrix n =
  V.generate (n * n) (\k -> if k `div` n == k `mod` n then Exact 1 else Exact 0)

-- | The product of two row-major @n × n@ matrices.
matrixProduct ::
  Precision -> Int -> Vector Magnitude -> Vector Magnitude -> Vector Magnitude
matrixProduct p n a b =
  V.generate
    (n * n)
    ( \k ->
        let (i, j) = k `divMod` n
         in sumM [mulM p (a V.! (i * n + l)) (b V.! (l * n + j)) | l <- [0 .. n - 1]]
    )

-- | A row-major @n × n@ matrix applied to a vector.
rotateVector ::
  Precision -> Int -> Vector Magnitude -> Vector Magnitude -> Vector Magnitude
rotateVector p n r v =
  V.generate
    n
    (\i -> sumM [mulM p (r V.! (i * n + j)) (v V.! j) | j <- [0 .. n - 1]])

chunksOf :: Int -> [a] -> [[a]]
chunksOf n xs
  | null xs = []
  | otherwise = let (r, rest) = splitAt n xs in r : chunksOf n rest

{- | The @m × n@ matrix of exact cross-covariances of two lists of
magnitudes (design §3.5), in the given dimension and display unit. Shared
by @covariance@, @crossCovariance@ and the REPL's @:covariance@.
-}
covarianceMatrix :: Config -> Dim -> Maybe UnitHint -> [Magnitude] -> [Magnitude] -> Value
covarianceMatrix cfg d hint as bs =
  VTensor
    [length as, length bs]
    d
    hint
    (V.fromList [entry a b c | (a, row) <- zip as (crossCovarianceRows as bs), (b, c) <- zip bs row])
 where
  entry a b c
    | any (isJust . nonLinearAt cfg.nonlinear) [a, b] =
        Left (Metron.Eval.Domain "covariance of a value marked non-linear is not supported")
    | otherwise = Right (Exact c)

{- | Pair the fields of a constructor with an alternative's binders; the
counts agree by lint.
-}
attach :: Vec k a -> [Thunk] -> Vec k Thunk
attach bs fields = case bs of
  VNil -> VNil
  VCons _ rest -> case fields of
    f : fs -> VCons f (attach rest fs)
    [] -> VCons (Left (Internal "case: missing field")) (attach rest [])

{- | A point converted from a frame whose chart takes parameters with no
@from@, when no type said so (design §3.10, F7): refused, never read off
the chart it was written on.
-}
takesArguments :: Chart -> Text
takesArguments c =
  n <> " takes arguments: write p from (" <> n <> " …) to c"
 where
  n = case c.name of
    Just (UnitNamed t) -> t
    Just (UnitBase t) -> t
    Nothing -> "its frame"
