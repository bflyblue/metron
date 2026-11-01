{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedTuples #-}
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
  ValueOf (.., VData),
  Narrowing (..),
  narrow,
  placesWithin,
  Mixture (..),
  Option (..),
  Choice (..),
  Value,
  pattern VBool,
  ClosureOf (..),
  Closure,
  ElemOf,
  ThunkOf,
  Thunk,
  EvalError (..),
  Config (..),
  defaultConfig,
  precisionOf,
  batchMembers,
  RuntimeOf (..),
  Runtime,
  UnitAtom (..),
  UnitHint (..),
  UnitFactor (..),
  ChartOf (..),
  Chart,
  Applied (..),
  coordinatesOn,
  Preferences,
  covarianceMatrix,
  Site (..),
  evalClosed,
  evalAt,
  evalDefinition,
  neededAtRuntime,
  TyEnv,
) where

import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.IntSet qualified as IntSet (
  IntSet,
  empty,
  fromList,
  member,
  size,
  toAscList,
  union,
  unions,
 )
import Data.List (findIndex)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (empty, insert, null)
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T (intercalate, pack)
import Data.Vector (Vector)
import Data.Vector qualified as V (
  all,
  concat,
  concatMap,
  empty,
  foldl',
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
  zipWith,
  (!),
 )
import Data.Vector.Unboxed qualified as VU
import Metron.Affine (
  ArithError (..),
  Decide (..),
  Magnitude (Exact),
  Origin (Declared, Tagged),
  Precision,
 )
import Metron.Builtin (
  boolC,
  frameDefMoving,
  spaceOf,
  pattern ConsC,
  pattern FalseC,
  pattern NilC,
  pattern TrueC,
 )
import Metron.Core (
  ConRef (..),
  Fin (..),
  Hash (..),
  Hint (Hint),
  Label (Tag),
  Lit (LTensor),
  Nat (S, Z),
  Plus,
  Vec (..),
  lengthLimit,
  vecAppend,
  vecIndex,
  vecMap,
  vecMapIndexed,
  vecToList,
 )
import Metron.Dimension (
  BaseDim (Ang, T),
  Dim,
  DimAtom (Base),
  dimAtoms,
  dimBase,
  dimDiv,
  dimFromAtoms,
  dimInv,
  dimMul,
  dimOne,
  dimPow,
  dimRoot,
 )
import Metron.Double (Dbl)
import Metron.Limits (
  Budget,
  Context (..),
  Limit (..),
  Limits (..),
  beyond,
  defaultLimits,
  departing,
  enter,
  inSorted,
  log10Abs,
  nested,
  reach,
  spend,
  within,
 )
import Metron.Primitive (baseUnit, primArity, typedPrims)
import Metron.Remark (Cause (..), Site (..))
import Metron.Scalar (
  Backend (..),
  Batch (..),
  Decision (..),
  Members (..),
  Outcomes (..),
  Own (..),
  Rel (..),
  Rounding (..),
  Scalar (..),
  Settings (..),
  affineCovariance,
  lacks,
  memberAt,
  memberCount,
  memberVector,
  ownerOf,
  settingsAt,
 )
import Metron.Scalar qualified as Scalar (Shape (..))
import Metron.Strictness (strictMarker)
import Metron.TCore (TAlt (TAlt), TTerm (..))
import Metron.Type (
  Arg (..),
  Kind (..),
  Len (..),
  Shape (..),
  Space (..),
  Type (..),
  TypeDef,
  VarId,
  conText,
  freeVars,
  selfType,
  spaceLens,
  substOnce,
  varArg,
  pattern TTensor,
 )
import Metron.UnitHint (
  HintMode (PreserveExpression),
  Preferences,
  UnitAtom (..),
  UnitFactor (..),
  UnitHint (..),
  combine,
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
 )

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
  , limits :: Limits
  -- ^ what an evaluation may ask of the machine (design §8.1)
  , backend :: Backend
  -- ^ which evaluator of the scalars runs (design §8.2, @:backend@)
  , samples :: Int
  {- ^ the double backend's estimate: 0 a running error bound, N copies
  under random rounding (design §8.2, @:set samples@)
  -}
  , seed :: Int
  -- ^ the seed of those copies' random choices (@:set seed@)
  , rounding :: Rounding
  -- ^ how those copies round (design §8.2, @:set rounding@)
  , cores :: Int
  {- ^ how many evaluations carry the copies in parallel, each a batch of
  them (design §8.2, @:set cores@); the command line starts it at the
  machine's logical cores, a library session at 1
  -}
  , batch :: Maybe Batch
  {- ^ the batch of the copies this evaluation carries, set only by the
  evaluation that runs the batches; 'Nothing', all of them
  -}
  , group :: Maybe Members
  {- ^ the copies this evaluation carries when a branch point split them
  and sent them down one alternative (design §8.2); 'Nothing', the batch's
  -}
  }
  deriving stock (Show)

{- | The session's settings at their defaults (design §7.3): those a backend
reads are 'settingsAt''s, so that each default has one definition.
-}
defaultConfig :: Config
defaultConfig =
  Config
    { precision = 20
    , sigma = backendDefaults.decide.sigma
    , unicode = False
    , nonlinear = backendDefaults.decide.nonlinear
    , limits = defaultLimits
    , backend = AffineBackend
    , samples = backendDefaults.samples
    , seed = backendDefaults.seed
    , rounding = backendDefaults.rounding
    , cores = 1
    , batch = Nothing
    , group = Nothing
    }
 where
  backendDefaults = settingsAt 0

-- | Working precision: the scale plus guard digits (design §3.2.8).
precisionOf :: Config -> Precision
precisionOf cfg = cfg.precision + 4

-- | How comparisons are decided under a configuration (design §3.2.9).
decideOf :: Config -> Decide
decideOf cfg = Decide{sigma = cfg.sigma, nonlinear = cfg.nonlinear}

-- | What a backend's arithmetic needs from a configuration (design §8.2).
settingsOf :: Config -> Settings
settingsOf cfg =
  Settings
    { precision = precisionOf cfg
    , decide = decideOf cfg
    , samples = cfg.samples
    , seed = cfg.seed
    , rounding = cfg.rounding
    , copies = fromMaybe (batchMembers cfg) cfg.group
    }

-- | The copies an evaluation of the whole batch carries (design §8.2).
batchMembers :: Config -> Members
batchMembers cfg = case cfg.batch of
  Just b -> Range b.first b.count
  Nothing -> Range 0 cfg.samples

{- | What the evaluator needs from the codebase: the Typed Core behind a
reference, and whether a reference was declared a display unit. Its
values are a backend's ('Scalar'); 'Runtime' is the affine backend's.
-}
type Runtime = RuntimeOf Magnitude

data RuntimeOf s = Runtime
  { typedOf :: Hash -> Maybe (TTerm Z)
  , unitName :: Hash -> Maybe Int -> Text -> Maybe Text
  -- ^ given a reference and the name written for it, the unit name it is a unit under, if any (design §3.2.12)
  , chartName :: Hash -> Maybe Int -> Text -> Maybe Text
  , typeDefOf :: Hash -> Maybe TypeDef
  {- ^ the declared types, for a space's amounts and a frame's parameters
  (design §3.10, F2, F7), which a chart's declaration names by its tags
  -}
  , shared :: Hash -> Maybe (ThunkOf s)
  {- ^ the value of a definition (not a cycle member) evaluated once and
  shared by every reference to it, when the caller keeps such a table:
  @evalDefinition cfg rt h t@ under the same 'Config' and this runtime, so that an
  expensive value (a turned chart's rotation, design §3.8) is computed once
  per evaluation rather than once per reference. Pure, so sharing changes
  no result; 'Nothing' evaluates the definition afresh
  -}
  , budget :: Budget
  -- ^ the steps and nesting this evaluation has spent (design §8.1), its own
  , context :: Context
  {- ^ where the evaluation is among the double backend's copies (design
  §8.2): the copies it carries and its place below the branch points
  that split them
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
  | -- | a resource limit reached (design §8.1), and what reached it
    Exceeded Limit Text
  | -- | Unreachable for linted terms.
    Internal Text
  deriving stock (Eq, Show)

type ThunkOf s = Either EvalError (ValueOf s)

type Thunk = ThunkOf Magnitude

-- | A tensor element, lazily.
type ElemOf s = Either EvalError s

-- | The environment for a term in scope @n@.
type Env s n = Vec n (ThunkOf s)

{- | A chart (design §3.10): a step, an origin and axes relative to its
parent. Points store frame coordinates with the step applied. Local
offsets and generators let conversions stop at a shared configuration;
absolute transforms and kinematics remain cached for the physics helpers.
-}
data ChartOf s = Chart
  { name :: Maybe UnitAtom
  , step :: s
  , stepHint :: Maybe UnitHint
  -- ^ the step's own display unit, which differences inherit
  , origin :: Vector s
  {- ^ the origin as an amount from the base origin along the base axes, one
  magnitude per component: the parent's origin plus the amount the chart
  was given at, which is along the parent's axes and so turned by the
  parent's rotation
  -}
  , localOrigin :: Vector s
  -- ^ the declared offset along the parent's axes, before any rotation
  , dims :: [Int]
  , dim :: Dim
  , parent :: Maybe (ChartOf s)
  {- ^ the chart the origin and the generators are given in; 'Nothing' is
  the base of its space (design §3.10, F2). The chart value itself, not a hash: a
  chart need not be named, and its definition's Core already refers to the
  parent's by hash
  -}
  , generators :: [Vector s]
  {- ^ antisymmetric @n × n@ matrices, row-major, applied in order; none is
  axis-aligned with the parent
  -}
  , rotation :: Maybe (Either EvalError (Vector s))
  {- ^ the absolute rotation, row-major: the parent's times @expm g₁ · expm
  g₂ · …@, whose columns are this chart's axes along the base axes.
  'Nothing' when neither this chart nor any above it is turned. A lazy
  field, so it is computed once, when first used, and shared by every use
  of the value
  -}
  , rotationInverse :: Maybe (Either EvalError (Vector s))
  {- ^ its inverse, from the generators negated in reverse order (@… · expm
  (−g₂) · expm (−g₁)@, then the parent's inverse), never by inverting an
  enclosure
  -}
  , relativeRotation :: Maybe (Either EvalError (Vector s))
  , relativeRotationInverse :: Maybe (Either EvalError (Vector s))
  -- ^ cached local transforms, used by conversions below a shared ancestor
  , spin :: Maybe (Vector s)
  {- ^ the angular velocity of a spinning chart relative to its parent,
  along its own axes, in s⁻¹ (the radian stripped); 'Nothing' is none
  -}
  , spinAbs :: Maybe (Either EvalError (Vector s))
  {- ^ the absolute angular velocity along the base axes, @ω_abs = ω_parent
  + R_abs ω@; 'Nothing' when neither this chart nor any above it spins.
  Lazy, as the rotation is
  -}
  , originVelocity :: Maybe (Either EvalError (Vector s))
  {- ^ the velocity of the origin along the base axes, @v_parent + ω_parent
  × (R_parent a)@ for the amount @a@ the origin is given at (an origin is
  fixed relative to its parent); 'Nothing' when nothing above spins
  -}
  , applied :: Applied s
  -- ^ the arguments of the moving chart this chart is an instant of, if it is one
  , frame :: Hash
  {- ^ the frame the chart is a chart of (design §3.10, F3): the one it
  minted, or a rescaling's parent's
  -}
  , moving :: Bool
  -- ^ whether its frame's chart takes parameters (design §3.10, F7)
  }
  deriving stock (Eq, Show)

-- | A chart of the affine backend.
type Chart = ChartOf Magnitude

{- | The arguments a moving chart was applied to (design §3.8), kept so that
the chart it gave prints as it is written, @(ecef (100 unix))@. They say
how the chart prints, not what it is, so 'Eq' ignores them.
-}
newtype Applied s = Applied [ThunkOf s]

instance Eq (Applied s) where
  _ == _ = True

instance Show (Applied s) where
  show (Applied xs) = "Applied <" ++ show (length xs) ++ " arguments>"

{- | A value whose numbers are a backend's scalars (design §8.2); 'Value' is
the affine backend's.
-}
data ValueOf s
  = -- | lengths, dimension, display unit, flat row-major elements in SI base units
    VTensor ![Int] !Dim !(Maybe UnitHint) (Vector (ElemOf s))
  | {- | a point on a frame (design §3.10, F6): lengths, dimension, the chart
    it was written on, for printing, and its coordinates on its frame with
    the step applied, an amount from the frame's origin along its axes
    -}
    VPoint ![Int] !Dim (ChartOf s) (Vector (ElemOf s))
  | VChart (ChartOf s)
  | {- | a constructor with its fields as thunks (design §8), and what the
    copies choose, when they carry their own (design §8.2); a boolean is
    one, 'VBool'. 'VData' is one whose copies say nothing
    -}
    VCon ConRef [ThunkOf s] !Choice
  | VClosure (ClosureOf s)
  | {- | a unit (design §3.10, U1): a newtype around a number, its magnitude
    in base units with its display hint, which is the unit expression it
    prints as (U8); kept apart only so that it prints as a unit wherever
    it is, inside a tuple or a record as at the top
    -}
    VUnit (ValueOf s)
  | {- | a polymorphic value waiting for the argument of its type-level
    variable (design §8); only a type application consumes one
    -}
    VTyAbs VarId Kind (Arg -> ThunkOf s)
  | {- | a value whose samples differ in what it is (design §8.2): the
    double backend's copies, when they carry draws, grouped by the
    outcome each has, a constructor or a function, never a number
    -}
    VMixture (Mixture s)
  | {- | the groups of a split in tail position, not yet put back together
    (design §8.2): only the evaluator's own tail calls pass one on, and
    whatever waits for the value puts the groups together ('settle'), so
    that a loop through a split runs in constant stack. Never seen outside
    "Metron.Eval"
    -}
    VSplit (Split s)

type Value = ValueOf Magnitude

{- | A mixture (design §8.2, "Branches under copies"): options, each a
group of the copies, by global number, ascending, with the value they
share, its numbers' copies those of the group. The options together are
the copies of the evaluation the mixture is in, and no two have the same
constructor. On the nominal path one option is the nominal one, the
nominal value's, even when none of the copies has it; off it, none is.
An option's value is never a mixture itself; its fields may be.
-}
data Mixture s = Mixture {nominal :: Maybe Int, options :: [Option s]}

-- | One outcome of a mixture: the copies that have it, and its value for them.
data Option s = Option {members :: VU.Vector Int, value :: ValueOf s}

{- | What a data value's copies choose (design §8.2, "Branches under
copies"): nothing of their own, or each copy's own constructor, by its
number in its type, in the order of the evaluation's copies, what the
copies spread by, and which of them, by global number, were already off
their own path when it was decided. A comparison's copies each have their
own result, which an @if@ on it counts; the value is still the nominal
one.
-}
data Choice
  = NoCopies
  | Copied !Cause !IntSet.IntSet !(VU.Vector Int)
  deriving stock (Eq, Show)

-- | A constructor whose copies choose nothing of their own.
pattern VData :: ConRef -> [ThunkOf s] -> ValueOf s
pattern VData c fields <- VCon c fields _
  where
    VData c fields = VCon c fields NoCopies

{-# COMPLETE VTensor, VPoint, VChart, VData, VClosure, VUnit, VTyAbs, VMixture #-}

-- | A boolean: @True@ or @False@ of the built-in @Bool@ ("Metron.Builtin").
pattern VBool :: Bool -> ValueOf s
pattern VBool b <- VData (asBool -> Just b) []
  where
    VBool b = VData (boolC b) []

{- | A condition as a value, in the evaluation of a context's copies (design
§8.2): the nominal result, and what the copies say. Copies that differ by
rounding alone follow the nominal result and keep their own beside it.
Copies that carry draws are samples, each with its own result: a mixture
of the two when they differ among themselves or from the nominal one,
else the result they share. Off the nominal path the nominal result means
nothing, and only the copies decide.
-}
conditionIn :: Context -> Bool -> Maybe Outcomes -> ValueOf s
conditionIn ctx b = \case
  Nothing -> VBool b
  Just o
    | o.cause == Rounding ->
        VCon (boolC b) [] (Copied o.cause o.left (VU.map fromEnum o.each))
    | otherwise ->
        let globals = memberVector ctx.members
            holding h = VU.map snd (VU.filter ((== h) . fst) (VU.zip o.each globals))
         in mixtureOf ctx.nominal [Option (holding h) (VBool h) | h <- [b, not b]]

{- | Options as a value: those with copies, and, on the nominal path, the
nominal one, the first given, even with none. A single option is its
value.
-}
mixtureOf :: Bool -> [Option s] -> ValueOf s
mixtureOf onNominal given = case kept of
  [o] -> o.value
  _ -> VMixture (Mixture (if onNominal then Just 0 else Nothing) kept)
 where
  kept = case given of
    o : rest | onNominal -> o : filter (not . VU.null . (.members)) rest
    _ -> filter (not . VU.null . (.members)) given

-- | A boolean's copies' own results, if it has copies.
outcomesOf :: ValueOf s -> Maybe Outcomes
outcomesOf = \case
  VCon _ [] (Copied cause left alts) -> Just (Outcomes cause left (VU.map (/= 0) alts))
  _ -> Nothing

{- | Two conditions combined copy by copy; a condition without copies is its
nominal result in every copy.
-}
combined ::
  (Bool -> Bool -> Bool) ->
  (Bool, Maybe Outcomes) ->
  (Bool, Maybe Outcomes) ->
  (Bool, Maybe Outcomes)
combined f (a, oa) (b, ob) = (f a b, both)
 where
  both = case (oa, ob) of
    (Just x, Just y) ->
      Just
        ( Outcomes
            (x.cause <> y.cause)
            (IntSet.union x.left y.left)
            (VU.zipWith f x.each y.each)
        )
    (Just x, Nothing) -> Just x{each = VU.map (`f` b) x.each}
    (Nothing, Just y) -> Just y{each = VU.map (f a) y.each}
    (Nothing, Nothing) -> Nothing

asBool :: ConRef -> Maybe Bool
asBool = \case
  TrueC -> Just True
  FalseC -> Just False
  _ -> Nothing

-- | A constructor's number in its type, which is its alternative's in a case.
conIndex :: ConRef -> Int
conIndex (UserCon _ k) = k

{- | A function value: a body under one binder, closed over its environment
and its site. For a function narrowed to a group of the double backend's
copies (design §8.2), the environment as it was made, the narrowing from
it, and the environment so narrowed, lazily, which every application
shares. Narrowing it again composes the two narrowings and narrows the
environment as it was made, so a function passed down through a loop
that splits at every step stays one narrowing from where it was made, not
a chain of them.
-}
data ClosureOf s
  = forall n.
    Closure TyEnv Site !(Env s n) (TTerm (S n)) !(Maybe Narrowing) (Env s n)

type Closure = ClosureOf Magnitude

{- | The type-level arguments in force at a point of a term, by the
variables of that term's abstractions (design §8). Types are erased except
where a value's runtime shape or dimension comes from them alone: an
empty tensor literal, and the result of a mapping primitive. A variable
with no argument here is unconstrained, and any instance is a valid one.
-}
type TyEnv = Map VarId Arg

-- | Evaluate a closed term that belongs to no definition.
evalClosed :: (Scalar s) => Config -> RuntimeOf s -> TTerm Z -> ThunkOf s
evalClosed cfg rt = evalAt cfg rt (Hash mempty)

{- | Evaluate a closed term as the body of the definition with the given
hash, for its value: abstractions over type-level variables still
unapplied at the top are applied to the variables themselves, which
nothing constrains.
-}
evalAt :: (Scalar s) => Config -> RuntimeOf s -> Hash -> TTerm Z -> ThunkOf s
evalAt cfg rt h t = instantiated =<< evalDefinition cfg rt h t
 where
  instantiated = \case
    VTyAbs v k f -> instantiated =<< f (varArg k v)
    x -> Right x

{- | Evaluate a closed term as the definition with the given hash, as a
reference to it sees it: polymorphic definitions stay abstractions, which
each use applies to its type-level arguments.
-}
evalDefinition ::
  (Scalar s) => Config -> RuntimeOf s -> Hash -> TTerm Z -> ThunkOf s
evalDefinition cfg rt h = settle . eval cfg rt Map.empty (Site h []) VNil

eval ::
  forall s n.
  (Scalar s) =>
  Config -> RuntimeOf s -> TyEnv -> Site -> Env s n -> TTerm n -> ThunkOf s
-- Each backend's own copy of the evaluator, so that its hot path calls the
-- arithmetic directly rather than through the class.
{-# SPECIALIZE eval ::
  Config -> Runtime -> TyEnv -> Site -> Env Magnitude n -> TTerm n -> Thunk
  #-}
{-# SPECIALIZE eval ::
  Config -> RuntimeOf Dbl -> TyEnv -> Site -> Env Dbl n -> TTerm n -> ThunkOf Dbl
  #-}
eval cfg rt = go
 where
  p = settingsOf cfg
  hp = precisionOf cfg
  -- Whether the evaluation carries copies, whose branch points are noted
  -- (design §8.2).
  copied = cfg.samples > 0 && backendOf @s == DoubleBackend

  -- A definition the batch shares, for this evaluation's copies: in a
  -- group of them (design §8.2), narrowed from the batch's copies to the
  -- group's at once, not once for every split between them.
  sharedValue h = case cfg.group of
    Nothing -> rt.shared h
    Just g ->
      let gs = memberVector g
          fromBatch = Narrowing (placesIn (batchMembers cfg) gs) gs rt.context.nominal
       in fmap (narrow fromBatch) <$> rt.shared h

  -- One step of the evaluation (design §8.1): every reduction counts.
  go :: TyEnv -> Site -> Env s m -> TTerm m -> ThunkOf s
  go tenv site env t
    | spend rt.budget rt.context t = reduce tenv site env t
    | otherwise =
        Left
          ( Exceeded
              Steps
              ("the evaluation took more than " <> tshow cfg.limits.steps <> " steps")
          )

  {- A value something waits for, so one level deeper (design §8.1): an
  operand, a scrutinee, the function of a call, a thunk when forced. A
  call in tail position waits for nothing and is no deeper. A split in
  tail position is put together here, where its value is waited for
  (design §8.2). -}
  inner :: TyEnv -> Site -> Env s m -> TTerm m -> ThunkOf s
  inner tenv site env t = nested rt.budget tooDeep (settle (go tenv site env t))
  tooDeep =
    Left
      ( Exceeded
          Depth
          ("the evaluation nested more than " <> tshow cfg.limits.depth <> " calls deep")
      )

  reduce :: TyEnv -> Site -> Env s m -> TTerm m -> ThunkOf s
  reduce tenv site env = \case
    TVr i -> lookupEnv i env
    TRef h mi (Hint written) -> case rt.typedOf h of
      Nothing -> Left (UnknownRef h)
      Just t -> do
        -- A chart whose step may be zero is named by its reference. A
        -- definition is its own term: its type-level variables are its own.
        v <- first (namedChart (rt.chartName h mi written)) $ case mi of
          Nothing -> fromMaybe (inner Map.empty (Site h []) VNil t) (sharedValue h)
          Just i -> case t of
            TCycle vars _ bodies -> cycleMember h i vars bodies
            _ -> Left (BadCycleIndex i)
        -- A declared unit is its own display unit (design §3.2.12).
        case (rt.unitName h mi written, rt.chartName h mi written) of
          (Just u, _) -> asUnit (UnitNamed u) v
          (_, Just s) -> asChart (UnitNamed s) v
          _ -> Right v
    -- The first evaluated, the second in tail position, so that a strict
    -- left fold runs in constant stack (design §7.7).
    TPrimApp "seq" _ [a, b] -> do
      v <- inner tenv (child 0) env a
      forceValue v `seq` go tenv (child 1) env b
    -- Marked where its call is evaluated; anywhere else the term itself,
    -- at the same site, so a nudge's identity does not see the mark.
    TPrimApp marker _ [a] | marker == strictMarker -> go tenv site env a
    TPrimApp prim ty args ->
      runPrim
        cfg
        rt
        prim
        (resolveType tenv ty)
        (delays tenv site env args)
    TLit (LTensor (dims, rs)) _ ->
      Right (VTensor dims dimOne Nothing (V.fromList (map (Right . literal p) rs)))
    -- Data (design §8): fields stay thunks; a case forces only the scrutinee.
    -- A boolean is data like any other: @if@ is a case on its constructor.
    TCon c _ args -> Right (VData c (delays tenv site env args))
    -- A scrutinee whose copies choose for themselves is a branch point
    -- (design §8.2): the copies are counted by their own alternative,
    -- and those taken along by the nominal one are off their path inside
    -- it.
    --
    -- Under copies every case is noted, so that each copy is counted
    -- wherever it reaches one, whichever batch carries it. On a mixture
    -- the copies split: each option goes down its own alternative in a
    -- group of its own, and the groups' results are put back together.
    TCase sc _ alts ->
      inner tenv (child 0) env sc >>= \case
        VCon c fields choice ->
          case alternative c of
            Just (i, TAlt _ bs body) ->
              let env' = vecAppend (attach bs fields) env
               in case choice of
                    NoCopies
                      | copied ->
                          case reach rt.budget rt.context site (conIndex c) Rounding False IntSet.empty Nothing of
                            !_ -> go tenv (child i) env' body
                      | otherwise -> go tenv (child i) env' body
                    Copied cause left chosen ->
                      let off = reach rt.budget rt.context site (conIndex c) cause False left (Just chosen)
                       in if IntSet.size off == IntSet.size rt.context.departed
                            then go tenv (child i) env' body
                            else
                              eval cfg rt{context = departing off rt.context} tenv (child i) env' body
            Nothing -> Left (Internal ("case: no alternative for " <> conText c))
        VMixture m -> caseOnMixture cfg rt tenv site env alts m
        _ -> Left (Internal "case: the scrutinee is not data")
     where
      alternative = alternativeFor alts
    TLamWith _ _ body free ->
      let kept = keepFree free env
       in Right (VClosure (Closure tenv (child 0) kept body Nothing kept))
    TApp f a -> do
      fv <- inner tenv (child 0) env f
      -- A moving chart applied is an instant of it (design §3.8), named
      -- after it with the arguments it was applied to. Any other
      -- application is a tail call, so a loop runs in constant stack:
      -- the call is made in each branch, not shared as a thunk.
      case delay tenv (child 1) env a of
        (# arg #) -> case instantOf site [] (TApp f a) of
          Nothing -> applyTail cfg rt fv arg
          Just (n, args) ->
            apply cfg rt fv arg >>= \case
              VChart c ->
                Right
                  ( VChart
                      c
                        { name = Just (UnitNamed n)
                        , applied = Applied [settle (go tenv s env x) | (s, x) <- args]
                        }
                  )
              v -> Right v
    TLet _ _ e body -> case delay tenv (child 0) env e of
      (# x #) -> go tenv (child 1) (VCons x env) body
    TPow t n -> do
      v <- inner tenv (child 0) env t
      (x, d, hint) <- scalarFull v
      -- Its size is known before it is computed (design §8.1).
      case sizeOf x >>= \m -> beyond cfg.limits (fromInteger n * log10Abs m) of
        Just err -> Left (Exceeded Digits ("the power " <> err))
        Nothing -> Right ()
      r <- sized cfg.limits =<< arith (powM p x n)
      Right $ case v of
        -- A power of a unit is a unit (design §3.10, U2).
        VUnit _ ->
          VUnit
            (num (dimPow n d) (unitHintPow hp n =<< hint) r)
        _ -> num (dimPow n d) (hintPow hp n =<< hint) r
    -- Fresh unit nudges, one per component (design §3.2.5).
    TNoise k l n -> do
      allocation cfg.limits [fromInteger n]
      let count = fromInteger n
      Right
        ( VTensor
            [count]
            dimOne
            Nothing
            (V.generate count (arith . noiseM p k . originOf site l))
        )
    -- One independent nudge per component, the component index in its
    -- identity (design §3.4); a scalar uncertainty applies to every component.
    TUncertain k l x e -> do
      (dims, d, hint, xs) <- tensor =<< inner tenv (child 0) env x
      (edims, _, _, es) <- tensor =<< inner tenv (child 1) env e
      case (dims, edims) of
        -- v ±σ P: v + cholesky P · gauss n, one statistical nudge per
        -- component, identified by this site (design §3.5).
        ([n], [en, _]) | en == n -> do
          pRows <- chunksOf n <$> sequence (V.toList es)
          lrows <- arith (choleskyM p "±σ needs a symmetric covariance" pRows)
          let noise j = arith (noiseM p k (originOf site l j))
              component i = do
                vi <- xs V.! i
                terms <- sequence [mulM p lij <$> noise j | (j, lij) <- zip [0 ..] (lrows !! i)]
                Right (foldl (addM p) vi terms)
          Right (VTensor dims d hint (V.generate n component))
        _ ->
          let errAt i = if null edims then es V.! 0 else es V.! i
           in Right
                ( VTensor
                    dims
                    d
                    hint
                    ( V.imap
                        ( \i xm -> do
                            x' <- xm
                            e' <- errAt i
                            arith (uncertainM p k (originOf site l i) x' e')
                        )
                        xs
                    )
                )
    -- shape the other components have, so an error in one component is
    -- only raised when that component is used. The first component's
    -- display unit is kept.
    -- With none, the element type alone says what the stack holds.
    TPack _ ty ts ->
      let results = zipWith (\i t -> tensor =<< inner tenv (child i) env t) [0 ..] ts
          known = [(dims, d, hint) | Right (dims, d, hint, _) <- results]
       in case (results, known) of
            ([], _) -> case resolveType tenv ty of
              TTensor sh d -> Right (VTensor (0 : runtimeShape sh) (runtimeDim d) Nothing V.empty)
              _ -> Left (Internal "an empty pack of non-tensors")
            (_, (dims, d, hint) : _) -> do
              allocation cfg.limits (length results : dims)
              let block = \case
                    Right (_, _, _, buf) -> buf
                    Left err -> V.replicate (product dims) (Left err)
              Right (VTensor (length results : dims) d hint (V.concat (map block results)))
            (Left err : _, []) -> Left err
            (Right _ : _, []) -> Left (Internal "unreachable: a tensor with no shape")
    -- Slice out component i: a view, not a copy.
    TProj t i -> do
      v <- inner tenv (child 0) env t
      case v of
        VTensor dims d hint buf -> slice dims (\rest -> VTensor rest d hint) buf
        -- A coordinate of a point (design §3.10, F5): the amount along one
        -- of its frame's axes, the step applied, in the chart's step.
        VPoint dims d sc buf -> slice dims (\rest -> VTensor rest d sc.stepHint) buf
        _ -> Left (Internal "projection from a non-tensor")
     where
      slice :: [Int] -> ([Int] -> Vector a -> ValueOf s) -> Vector a -> ThunkOf s
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
      let erased = inner tenv site env b
       in Right
            ( VTyAbs
                v
                k
                ( if neededAtRuntime v k b
                    then \a -> settle (go (Map.insert v a tenv) site env b)
                    else const erased
                )
            )
    TTyApp b a ->
      inner tenv site env b >>= \case
        VTyAbs _ _ f -> f (resolveArg tenv a)
        VMixture m ->
          perOption cfg rt m $ \_ _ _ -> \case
            VTyAbs _ _ f -> f (resolveArg tenv a)
            _ -> Left (Internal "type application to a value that is not polymorphic")
        _ -> Left (Internal "type application to a value that is not polymorphic")
    -- A cycle is not itself a value; it is reached through @TRef h (Just i)@.
    TCycle{} -> Left (BadCycleIndex (-1))
   where
    child i = site{path = i : site.path}

  {- A subterm as a thunk, without forcing it. A variable is the thunk it
  is bound to, not a new one around the environment: a new one would keep
  the whole environment alive until forced, so a loop that passes a
  variable on (@loop n = loop n@) would chain every environment it went
  through. A literal is built at once: it costs nothing and cannot fail.
  An argument its call is strict in ("Metron.Strictness") is evaluated
  now, a number's one component with it, so that an accumulator carries
  a value and not a chain of pending sums. The unboxed result lets the
  lookup run now while the thunk found stays unforced. -}
  delay :: TyEnv -> Site -> Env s m -> TTerm m -> (# ThunkOf s #)
  delay tenv site env = \case
    TVr i -> lookupThunk i env
    t@TLit{} -> let !v = go tenv site env t in (# v #)
    TPrimApp marker _ [a]
      | marker == strictMarker ->
          let !v = evaluated (inner tenv site env a) in (# v #)
    t -> (# inner tenv site env t #)

  -- 'delay' over arguments in order, the i-th at child i.
  delays :: TyEnv -> Site -> Env s m -> [TTerm m] -> [ThunkOf s]
  delays tenv site env = loop 0
   where
    loop i = \case
      [] -> []
      t : ts -> case delay tenv site{path = i : site.path} env t of
        (# x #) -> let !rest = loop (i + 1) ts in x : rest

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
  cycleMembers :: TyEnv -> Hash -> Vec k (TTerm (Plus k Z)) -> Vec k (ThunkOf s)
  cycleMembers tenv h bodies = members
   where
    members = vecMapIndexed (\i -> inner tenv (Site h [i]) (vecAppend members VNil)) bodies

  -- A member of a cycle, abstracted over the cycle's type-level variables
  -- as its stored scheme is (every member's lists them all, in order).
  -- The members are evaluated once for every application only when some
  -- body needs the arguments at run time.
  cycleMember ::
    Hash -> Int -> [(VarId, Kind)] -> Vec k (TTerm (Plus k Z)) -> ThunkOf s
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

lookupEnv :: Fin n -> Env s n -> ThunkOf s
lookupEnv i env = case (i, env) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupEnv j xs

-- | 'lookupEnv' that walks the environment now and leaves the thunk unforced.
lookupThunk :: Fin n -> Env s n -> (# ThunkOf s #)
lookupThunk i env = case (i, env) of
  (FZ, VCons x _) -> (# x #)
  (FS j, VCons _ xs) -> lookupThunk j xs

{- | The environment a closure keeps: the variables its body uses, every
other place emptied. A closure over the whole environment would keep
alive whatever it holds, so @\\n _ -> n + 1@ written inside @length xs@
kept the head of @xs@, and with it the whole list, for the whole fold.
The set is the body's free variables, the function's own argument at 0.
-}
keepFree :: IntSet.IntSet -> Env s n -> Env s n
keepFree used = go 1
 where
  go :: Int -> Env s k -> Env s k
  go i = \case
    VNil -> VNil
    VCons x xs ->
      -- The choice is made now: a thunk choosing later would keep x.
      let !rest = go (i + 1) xs
       in if IntSet.member i used then VCons x rest else VCons unused rest
  unused = Left (Internal "a variable the closure does not use")

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

-- | Apply a function value to an argument thunk, for its value.
apply ::
  (Scalar s) => Config -> RuntimeOf s -> ValueOf s -> ThunkOf s -> ThunkOf s
apply cfg rt f arg = settle (applyTail cfg rt f arg)

{- | Apply a function value to an argument thunk in tail position: a split
the call ends in is passed on, not put together (design §8.2).
-}
applyTail ::
  (Scalar s) => Config -> RuntimeOf s -> ValueOf s -> ThunkOf s -> ThunkOf s
{-# SPECIALIZE applyTail :: Config -> Runtime -> Value -> Thunk -> Thunk #-}
{-# SPECIALIZE applyTail ::
  Config -> RuntimeOf Dbl -> ValueOf Dbl -> ThunkOf Dbl -> ThunkOf Dbl
  #-}
applyTail cfg rt f arg = case f of
  VClosure (Closure tenv site _ body _ applied) ->
    eval cfg rt tenv site (VCons arg applied) body
  -- A mixture of functions (design §8.2): each applied for its own copies.
  VMixture m ->
    perOption cfg rt m (\cfg' rt' r g -> applyTail cfg' rt' g (narrow r <$> arg))
  _ -> Left (Internal "application of a non-function")

-- Splitting the copies ----------------------------------------------------------------

-- | A case's alternative for a constructor, and its place among them, from 1.
alternativeFor :: [TAlt n] -> ConRef -> Maybe (Int, TAlt n)
alternativeFor alts c = case [(i, alt) | (i, alt@(TAlt c' _ _)) <- zip [1 ..] alts, c' == c] of
  found : _ -> Just found
  [] -> Nothing

{- | A case on a mixture (design §8.2): a branch point where the copies
split, noted, and each option sent down its own alternative in a group of
its own. The case is in tail position, so the groups are passed on to be
put together where the value is waited for ('settle'): a loop whose
condition splits the copies then runs in constant stack, each group
going on with its own iterations.
-}
caseOnMixture ::
  (Scalar s) =>
  Config ->
  RuntimeOf s ->
  TyEnv ->
  Site ->
  Env s n ->
  [TAlt n] ->
  Mixture s ->
  ThunkOf s
caseOnMixture cfg rt tenv site env alts m =
  case reach rt.budget ctx site taken Draws True IntSet.empty (Just chosen) of
    !_ ->
      splitOver cfg rt m $ \cfg' rt' r -> \case
        VCon c fields _
          | Just (i, TAlt _ bs body) <- alternativeFor alts c ->
              eval
                cfg'
                rt'
                tenv
                site{path = i : site.path}
                (vecAppend (attach bs fields) (vecMap (fmap (narrow r)) env))
                body
        _ -> Left (Internal "case: an option of the scrutinee is not data")
 where
  ctx = rt.context
  conOf o = case o.value of
    VCon c _ _ -> conIndex c
    _ -> -1
  chosen =
    VU.update
      (VU.replicate (memberCount ctx.members) (-1))
      (VU.concat [VU.map (,conOf o) (placesIn ctx.members o.members) | o <- m.options])
  taken =
    maybe (-1) (\k -> maybe (-1) conOf (listToMaybe (drop k m.options))) m.nominal

{- | How a value made for an evaluation's copies is narrowed to a group of
them (design §8.2): the places of the group's copies among the
evaluation's, the group's copies by global number, and whether the group
is on the nominal path.
-}
data Narrowing = Narrowing {places :: VU.Vector Int, copies :: VU.Vector Int, nominal :: Bool}

{- | Two narrowings, the second to a group of the first's: one narrowing
that does both.
-}
andThen :: Narrowing -> Narrowing -> Narrowing
andThen outer r = Narrowing (VU.backpermute outer.places r.places) r.copies r.nominal

{- | The places, among an evaluation's copies, of a group of them, by
global number; both ascending.
-}
placesIn :: Members -> VU.Vector Int -> VU.Vector Int
placesIn outer group = case outer of
  Range from _ -> VU.map (subtract from) group
  Listed all' -> VU.findIndices (inSorted group) all'

{- | A value for a group of the copies it was made for, lazily: every
number keeps the group's copies, a mixture the options the group has, and
a function or a chart what it holds narrowed alike.
-}
narrow :: (Scalar s) => Narrowing -> ValueOf s -> ValueOf s
narrow r = \case
  VTensor dims d hint buf -> VTensor dims d hint (V.map (fmap (restrictM r.places)) buf)
  VPoint dims d c buf -> VPoint dims d (narrowChart r c) (V.map (fmap (restrictM r.places)) buf)
  VChart c -> VChart (narrowChart r c)
  VCon c fields choice ->
    VCon
      c
      (map (fmap (narrow r)) fields)
      ( case choice of
          NoCopies -> NoCopies
          Copied cause left alts -> Copied cause left (VU.backpermute alts r.places)
      )
  VClosure (Closure tenv site env body narrowing _) ->
    let r' = maybe r (`andThen` r) narrowing
     in VClosure (Closure tenv site env body (Just r') (vecMap (fmap (narrow r')) env))
  VUnit v -> VUnit (narrow r v)
  VTyAbs v k f -> VTyAbs v k (fmap (narrow r) . f)
  -- Never held where a group narrows it: whatever holds a value waited
  -- for it, and a split is put together where it is waited for.
  VSplit sp -> VSplit sp
  VMixture m ->
    let kept =
          [ ( nominal
            , Option
                shared
                (narrow (Narrowing (placesIn (Listed o.members) shared) shared nominal) o.value)
            )
          | (i, o) <- zip [0 :: Int ..] m.options
          , let shared = VU.filter (inSorted r.copies) o.members
                nominal = r.nominal && m.nominal == Just i
          , nominal || not (VU.null shared)
          ]
     in case kept of
          [(_, o)] -> o.value
          _ -> VMixture (Mixture (findIndex fst kept) (map snd kept))

-- | A chart narrowed to a group of the copies: every number in it.
narrowChart :: (Scalar s) => Narrowing -> ChartOf s -> ChartOf s
narrowChart r c =
  Chart
    { name = c.name
    , step = one c.step
    , stepHint = c.stepHint
    , origin = V.map one c.origin
    , localOrigin = V.map one c.localOrigin
    , dims = c.dims
    , dim = c.dim
    , parent = narrowChart r <$> c.parent
    , generators = map (V.map one) c.generators
    , rotation = many c.rotation
    , rotationInverse = many c.rotationInverse
    , relativeRotation = many c.relativeRotation
    , relativeRotationInverse = many c.relativeRotationInverse
    , spin = V.map one <$> c.spin
    , spinAbs = many c.spinAbs
    , originVelocity = many c.originVelocity
    , applied = case c.applied of
        Applied args -> Applied (map (fmap (narrow r)) args)
    , frame = c.frame
    , moving = c.moving
    }
 where
  one = restrictM r.places
  many = fmap (fmap (V.map one))

{- | The evaluation of a group of the copies (design §8.2): its settings
carry the group's copies, its context is new, and every value it takes
from the evaluation around it, its environment, is narrowed to the group;
a definition the batch shares is narrowed where it is referenced.
-}
groupOf ::
  (Scalar s) =>
  Config ->
  RuntimeOf s ->
  VU.Vector Int ->
  Bool ->
  (Config, RuntimeOf s, Narrowing)
groupOf cfg rt group nominal = (cfg{group = Just (Listed group)}, rt', r)
 where
  r = Narrowing (placesIn rt.context.members group) group nominal
  rt' = rt{context = enter rt.budget rt.context (Listed group) nominal}

{- | An operation on a mixture (design §8.2): done for each option, in a
group of its own with the option's copies, given the option's value and
how to narrow the evaluation's other values to the group, and the
results put back together. The nominal option is done even with no
copies, for the nominal value; another with none is not done at all.
-}
perOption ::
  (Scalar s) =>
  Config ->
  RuntimeOf s ->
  Mixture s ->
  (Config -> RuntimeOf s -> Narrowing -> ValueOf s -> ThunkOf s) ->
  ThunkOf s
perOption cfg rt m k = settle (splitOver cfg rt m k)

{- | 'perOption' with the groups' results not yet put together: a split
(design §8.2), for a case in tail position to pass on.
-}
splitOver ::
  (Scalar s) =>
  Config ->
  RuntimeOf s ->
  Mixture s ->
  (Config -> RuntimeOf s -> Narrowing -> ValueOf s -> ThunkOf s) ->
  ThunkOf s
splitOver cfg rt m k =
  -- Every group is entered before any evaluates, so that each path
  -- starts from the steps taken before the split (design §8.1).
  foldr
    (\(Part ctx _ _) rest -> ctx `seq` rest)
    ( Right
        ( VSplit
            ( Split
                (Join rt.budget rt.context)
                cfg.limits.outcomes
                parts
            )
        )
    )
    parts
 where
  parts =
    [ Part rt'.context nominal (k cfg' rt' r o.value)
    | (i, o) <- zip [0 :: Int ..] m.options
    , let nominal = rt.context.nominal && m.nominal == Just i
    , nominal || not (VU.null o.members)
    , let (cfg', rt', r) = groupOf cfg rt o.members nominal
    ]

{- | A group's result: its evaluation, whether it is the nominal one, and
the value, for the group's copies.
-}
data Part s = Part Context Bool (ThunkOf s)

{- | A split's groups, not yet put together: where they join, the
@outcomes@ limit, and their results.
-}
data Split s = Split Join Int [Part s]

{- | A value as something waiting for it sees it: a split put together
(design §8.2), any other value as it is.
-}
settle :: (Scalar s) => ThunkOf s -> ThunkOf s
settle = \case
  Right (VSplit sp) -> recombine sp
  t -> t

{- | The groups' results put back together, copy by copy (design §8.2):
numbers, tensors and units as one, each copy from its own group, the
nominal value from the nominal group; data by outcome, a constructor's
groups merged field by field, and where the groups give different
constructors, or functions, a mixture with an option for each. More
options than the @outcomes@ limit stop the evaluation. A group whose
result is a split of its own gives its groups instead, in its place, so
a split in tail position, however deep, is put together once.
-}
recombine :: (Scalar s) => Split s -> ThunkOf s
recombine (Split j@(Join _ ctx) limit parts) =
  assemble j limit (memberVector ctx.members) (piecesOf parts)

-- | A split's groups as pieces, the nominal one first.
piecesOf :: [Part s] -> [Piece s]
piecesOf parts =
  [ Piece ctx (memberVector ctx.members) nominal t
  | Part ctx nominal t <- filter isNominal parts ++ filter (not . isNominal) parts
  ]
 where
  isNominal (Part _ n _) = n

{- | A value for some of the copies: the evaluation that makes it, the
copies by global number, whether it is the nominal value, and the value.
-}
data Piece s = Piece Context (VU.Vector Int) Bool (ThunkOf s)

{- | Where groups' results are put back together: the budget, and the
evaluation they were split from, whose path continues from theirs
(design §8.1).
-}
data Join = Join Budget Context

{- | Pieces that together are a value for the given copies, put together:
'recombine', for a value or for one field of the data its groups share.
The nominal piece, if any, first.
-}
assemble ::
  (Scalar s) => Join -> Int -> VU.Vector Int -> [Piece s] -> ThunkOf s
assemble b limit target pieces = do
  values <- leaves [] pieces
  let flat = concatMap explode values
  case flat of
    [] -> Left (Internal "a split with no group")
    (_, _, _, v0) : _
      | numeric v0 ->
          numbersOf
            [(ctx, placesWithin target ms, nominal, v) | (ctx, ms, nominal, v) <- flat]
      | otherwise -> outcomesFrom (classes flat)
 where
  -- Each piece forced, nominal first, in turn; a piece that is a split
  -- of its own is replaced by its groups, so the groups of a loop that
  -- splits at every step are forced one after another, not one inside
  -- another. The groups go in front of the rest strictly: a lazy append
  -- would wrap the rest in one more thunk at every step.
  leaves acc = \case
    [] -> Right (reverse acc)
    Piece ctx ms nominal t : rest ->
      forcedFor b ctx t >>= \case
        VSplit (Split _ _ parts) ->
          leaves acc (foldl' (flip (:)) rest (reverse (piecesOf parts)))
        v -> leaves ((ctx, ms, nominal, v) : acc) rest
  explode (ctx, ms, nominal, v) = case v of
    VMixture m ->
      [ (ctx, o.members, nominal && m.nominal == Just i, o.value)
      | (i, o) <- zip [0 :: Int ..] m.options
      ]
    _ -> [(ctx, ms, nominal, v)]
  numeric = \case
    VTensor{} -> True
    VPoint{} -> True
    VUnit _ -> True
    _ -> False
  -- Numbers: element by element, each from every piece.
  numbersOf ps = case ps of
    (_, _, _, VUnit _) : _ -> VUnit <$> numbersOf [(c, pl, n, u) | (c, pl, n, VUnit u) <- ps]
    (_, _, _, VTensor dims d hint buf) : _ ->
      Right (VTensor dims d hint (V.generate (V.length buf) (element ps)))
    (_, _, _, VPoint dims d c buf) : _ ->
      Right (VPoint dims d c (V.generate (V.length buf) (element ps)))
    _ -> Left (Internal "a split's groups give numbers of different kinds")
  -- A loop that splits at every step leaves a group for each, so the
  -- groups are taken in turn, in constant stack.
  element ps k = do
    xs <-
      inTurn (\(c, pl, n, v) -> (pl,n,) <$> forcedElement b c (bufferOf v V.! k)) ps
    Right
      ( scatterM
          (VU.length target)
          (listToMaybe [x | (_, True, x) <- xs])
          [(pl, x) | (pl, _, x) <- xs]
      )
  bufferOf = \case
    VTensor _ _ _ buf -> buf
    VPoint _ _ _ buf -> buf
    VUnit u -> bufferOf u
    _ -> V.empty
  -- Data by its constructor; anything else, a function, a chart, alone.
  classes = foldl' place []
  place acc piece@(_, _, _, v) = case v of
    VCon c _ _
      | (before, (k, ps) : after) <- break ((== Just c) . fst) acc ->
          before ++ (k, ps ++ [piece]) : after
      | otherwise -> acc ++ [(Just c, [piece])]
    _ -> acc ++ [(Nothing, [piece])]
  outcomesFrom groups
    | length groups > limit =
        Left
          ( Exceeded
              OutcomeCount
              ("the value would have more than " <> tshow limit <> " outcomes")
          )
    | otherwise = do
        options <- traverse (classOf . snd) groups
        case options of
          [(_, _, v)] -> Right v
          _ ->
            Right
              ( VMixture
                  ( Mixture
                      (findIndex (\(_, n, _) -> n) options)
                      [Option ms v | (ms, _, v) <- options]
                  )
              )
  classOf = \case
    [(ctx, ms, nominal, v)] -> Right (ms, nominal, bracketed b ctx v)
    ps@((_, _, _, VCon c fields0 _) : _) -> do
      let ms =
            VU.fromList
              (IntSet.toAscList (IntSet.fromList (concat [VU.toList m | (_, m, _, _) <- ps])))
          nominal = or [n | (_, _, n, _) <- ps]
          fieldsOf = \case
            VCon _ fs _ -> fs
            _ -> []
          field j =
            assemble
              b
              limit
              ms
              [Piece ctx m n (fieldAt (fieldsOf v) j) | (ctx, m, n, v) <- ps]
          choice = case [ch | (_, _, _, VCon _ _ ch@Copied{}) <- ps] of
            [] -> NoCopies
            Copied cause _ _ : _ ->
              Copied
                cause
                (IntSet.unions [l | (_, _, _, VCon _ _ (Copied _ l _)) <- ps])
                ( VU.update
                    (VU.replicate (VU.length ms) (conIndex c))
                    ( VU.concat
                        [ VU.zip (placesWithin ms m) as
                        | (_, m, _, VCon _ _ (Copied _ _ as)) <- ps
                        ]
                    )
                )
            NoCopies : _ -> NoCopies
      Right (ms, nominal, VCon c (map field (zipWith const [0 ..] fields0)) choice)
    _ -> Left (Internal "a split's groups give outcomes of different kinds")

{- | A value whose samples differ in what it is (a mixture, design §8.2)
given where only one kind of value will do and nothing splits it: a
primitive on charts or lists, which the evaluator does not yet run once
for each outcome.
-}
mixed :: EvalError
mixed =
  Unsupported
    "an operation on a value whose samples have different outcomes (a mixture): only `case`, application and the conditions split one"

-- | The evaluator's own primitive for every field of data compared: see 'runPrim'.
conjunctionName :: Text
conjunctionName = "§all"

-- | A constructor's field by its place; lint makes the counts agree.
fieldAt :: [ThunkOf s] -> Int -> ThunkOf s
fieldAt fields j = case drop j fields of
  f : _ -> f
  [] -> Left (Internal "a missing field")

{- | 'traverse' for 'Either' in constant stack, for the long lists of
groups a loop that splits at every step leaves.
-}
inTurn :: (a -> Either e b) -> [a] -> Either e [b]
inTurn f = go []
 where
  go acc = \case
    [] -> Right (reverse acc)
    x : xs -> f x >>= \y -> go (y : acc) xs

-- | The places of some copies among others, both by global number, ascending.
placesWithin :: VU.Vector Int -> VU.Vector Int -> VU.Vector Int
placesWithin outer group = VU.findIndices (inSorted group) outer

{- | A value forced for a group's copies, so that a branch point it
reaches counts only them (design §8.2), and the path of the evaluation
they were split from continues from the group's (design §8.1).
-}
forcedFor :: Join -> Context -> ThunkOf s -> ThunkOf s
forcedFor (Join b outer) ctx t = within b outer ctx (either (const t) (`seq` t) t)

-- | A tensor element forced for a group's copies.
forcedElement :: Join -> Context -> ElemOf s -> ElemOf s
forcedElement (Join b outer) ctx e = within b outer ctx (either (const e) (`seq` e) e)

{- | A group's value passed on whole, its parts forced, whenever they are,
for the group's copies: its branch points count them, not those of
whatever group forces the value later.
-}
bracketed :: Join -> Context -> ValueOf s -> ValueOf s
bracketed b ctx = \case
  VCon c fields choice -> VCon c (map (forcedFor b ctx . fmap (bracketed b ctx)) fields) choice
  VTensor dims d hint buf -> VTensor dims d hint (V.map (forcedElement b ctx) buf)
  VPoint dims d c buf -> VPoint dims d c (V.map (forcedElement b ctx) buf)
  VUnit v -> VUnit (bracketed b ctx v)
  VMixture m ->
    VMixture
      m{options = [Option o.members (bracketed b ctx o.value) | o <- m.options]}
  v -> v

arith :: Either ArithError a -> Either EvalError a
arith = either (Left . convert) Right
 where
  convert = \case
    Metron.Affine.DivideByZero -> Metron.Eval.DivideByZero
    Metron.Affine.Domain msg -> Metron.Eval.Domain msg
    Metron.Affine.Undecided msg -> Metron.Eval.Undecided msg

-- Values ---------------------------------------------------------------------------

num :: Dim -> Maybe UnitHint -> s -> ValueOf s
num d hint r = VTensor [] d hint (V.singleton (Right r))

-- | A tensor's parts; a unit's, which are a number's (design §3.10, U1).
tensor ::
  ValueOf s -> Either EvalError ([Int], Dim, Maybe UnitHint, Vector (ElemOf s))
tensor = \case
  VTensor dims d hint buf -> Right (dims, d, hint, buf)
  VUnit v -> tensor v
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a tensor")

point ::
  ValueOf s -> Either EvalError ([Int], Dim, ChartOf s, Vector (ElemOf s))
point = \case
  VPoint dims d sc buf -> Right (dims, d, sc, buf)
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a point")

chartOf :: ValueOf s -> Either EvalError (ChartOf s)
chartOf = \case
  VChart s -> Right s
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a chart")

-- | A number or a point: what the comparisons order.
ordered :: ValueOf s -> Either EvalError s
ordered = \case
  VPoint [] _ _ buf | V.length buf == 1 -> V.head buf
  v -> scalar v

-- | The one element of a rank-zero tensor.
scalar :: ValueOf s -> Either EvalError s
scalar v = (\(x, _, _) -> x) <$> scalarFull v

scalarFull :: ValueOf s -> Either EvalError (s, Dim, Maybe UnitHint)
scalarFull = \case
  VTensor [] d hint buf | V.length buf == 1 -> (,d,hint) <$> V.head buf
  VUnit v -> scalarFull v
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a number")

{- | What @seq@ evaluates (design §7.7): every component of a number, a
tensor or a point, so that an accumulator holds no chain of pending
arithmetic; of data, its constructor only. A component that fails keeps
its error to itself, as it would unforced.
-}

{- | A thunk evaluated before its call: to a value and, for a number or a
small tensor or point (a state vector, a small matrix), its components,
so that an accumulator holds no chain of pending sums; a component that
fails still fails only where used. A large tensor's stay lazy, so a
function strict in it computes only the components it reads.
-}
evaluated :: ThunkOf s -> ThunkOf s
evaluated = \case
  r@(Right v) -> small v `seq` r
  r -> r
 where
  small = \case
    t@(VTensor _ _ _ buf) | V.length buf <= smallTensor -> forceValue t
    t@(VPoint _ _ _ buf) | V.length buf <= smallTensor -> forceValue t
    VUnit u -> small u
    _ -> ()

-- | The most components a tensor evaluated before its call may have.
smallTensor :: Int
smallTensor = 64

forceValue :: ValueOf s -> ()
forceValue = \case
  VTensor _ _ _ buf -> components buf
  VPoint _ _ _ buf -> components buf
  VUnit v -> forceValue v
  _ -> ()
 where
  components = V.foldl' (\() e -> either (const ()) (`seq` ()) e) ()

bool :: ValueOf s -> Either EvalError Bool
bool = \case
  VBool b -> Right b
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a boolean")

{- | Make a scalar value its own display unit. Forces its magnitude, which
for a unit definition is a constant.
-}
asUnit :: (Scalar s) => UnitAtom -> ValueOf s -> ThunkOf s
asUnit atom = \case
  VTensor [] d _ buf | V.length buf == 1 -> do
    x <- V.head buf
    let f = hintFactor x
    Right (VTensor [] d (Just (UnitHint [UnitFactor atom 1 d f] f d False)) buf)
  VUnit v -> VUnit <$> asUnit atom v
  v -> Right v

-- | Name a chart value after the definition it came from.
asChart :: UnitAtom -> ValueOf s -> ThunkOf s
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
  (s -> s -> Either EvalError s) ->
  (Dim -> Dim -> Dim) ->
  (UnitHint -> UnitHint -> Maybe UnitHint) ->
  ValueOf s ->
  ValueOf s ->
  ThunkOf s
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
runPrim ::
  forall s.
  (Scalar s) =>
  Config -> RuntimeOf s -> Text -> Type -> [ThunkOf s] -> ThunkOf s
{-# SPECIALIZE runPrim ::
  Config -> Runtime -> Text -> Type -> [Thunk] -> Thunk
  #-}
{-# SPECIALIZE runPrim ::
  Config -> RuntimeOf Dbl -> Text -> Type -> [ThunkOf Dbl] -> ThunkOf Dbl
  #-}
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
                  (literal p 1)
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
          (h >>= \hh -> mkHint hp hh.atoms)
          (V.map (fmap (\x -> mulM p x k)) xs)
      )
  -- Sum: the left operand's display unit wins.
  ("add", [a, b]) -> elementwise2 (pureOp (addM p)) const (combine smallerUnit) a b
  ("sub", [a, b]) -> elementwise2 (pureOp (subM p)) const (combine smallerUnit) a b
  ("neg", [a]) -> elementwise1 negM a
  ("abs", [a]) -> elementwise1 (absM p) a
  ("emul", [a, b]) -> elementwise2 (pureOp (mulM p)) dimMul (combine (hintMul hp)) a b
  ("ediv", [a, b]) ->
    elementwise2
      (\x y -> arith (divM p x y))
      dimDiv
      (\h1 h2 -> combine (hintMul hp) h1 (hintInv hp =<< h2))
      a
      b
  -- Tensor product: ranks add, dimensions multiply, every pair of elements
  -- multiplied.
  ("outer", [a, b]) -> do
    va <- a
    vb <- b
    case (va, vb) of
      -- Two units (design §3.10, U2).
      (VUnit x, VUnit y) -> unitOp (\m n -> Right (mulM p m n)) dimMul (unitHintMul hp) x y
      _ -> do
        (d1, dim1, h1, xs) <- tensor va
        (d2, dim2, h2, ys) <- tensor vb
        allocation cfg.limits (d1 ++ d2)
        Right
          ( VTensor
              (d1 ++ d2)
              (dimMul dim1 dim2)
              (combine (hintMul hp) h1 h2)
              ( V.concatMap
                  (\x -> V.map (\y -> do x' <- x; y' <- y; sized cfg.limits (mulM p x' y')) ys)
                  xs
              )
          )
  -- Contracting product: the left operand's last index against the right
  -- operand's first.
  ("dot", [a, b]) -> do
    (dl, dim1, h1, xs) <- tensor =<< a
    (dr, dim2, h2, ys) <- tensor =<< b
    case (reverse dl, dr) of
      (n : d1rev, n' : d2)
        | n == n' -> do
            allocation cfg.limits (reverse d1rev ++ d2)
            let d1 = reverse d1rev
                stride2 = product d2
                rows = product d1
                element k =
                  let (i, j) = k `divMod` stride2
                   in sized cfg.limits . sumM p
                        =<< sequence
                          [ mulM p <$> (xs V.! (i * n + c)) <*> (ys V.! (c * stride2 + j))
                          | c <- [0 .. n - 1]
                          ]
            Right
              ( VTensor
                  (d1 ++ d2)
                  (dimMul dim1 dim2)
                  (combine (hintMul hp) h1 h2)
                  (V.generate (rows * stride2) element)
              )
      _ -> Left (Internal "dot: operand shapes do not contract")
  ("div", [a, b]) -> do
    va <- a
    vb <- b
    case (va, vb) of
      -- Two units (design §3.10, U2).
      (VUnit x, VUnit y) -> unitOp (\m n -> arith (divM p m n)) dimDiv (unitHintDiv hp) x y
      _ -> do
        (dims, d1, h1, xs) <- tensor va
        (k, d2, h2) <- scalarFull vb
        Right
          ( VTensor
              dims
              (dimDiv d1 d2)
              (combine (hintMul hp) h1 (hintInv hp =<< h2))
              (V.map (\x -> x >>= \x' -> sized cfg.limits =<< arith (divM p x' k)) xs)
          )
  -- A condition keeps its copies' own results (design §8.2).
  ("eq", [a, b]) -> equal a b
  ("ne", [a, b]) -> negation (equal a b)
  ("lt", [a, b]) -> compareWith Lt a b
  ("le", [a, b]) -> compareWith Le a b
  ("gt", [a, b]) -> compareWith Gt a b
  ("ge", [a, b]) -> compareWith Ge a b
  -- Lazy in the second argument.
  ("and", [a, b]) -> shortCircuit True a b
  ("or", [a, b]) -> shortCircuit False a b
  ("not", [a]) -> negation a
  ("floor", [a]) -> dimensionless (arith . floorM p) a
  ("ceil", [a]) -> dimensionless (arith . ceilM p) a
  ("round", [a]) -> dimensionless (arith . roundM p) a
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
  ("exp", [a]) -> dimensionless (\x -> exponential id x >> Right (expM p x)) a
  ("log", [a]) -> dimensionless (arith . logM p) a
  ("sin", [a]) -> dimensionless (Right . sinM p) a
  ("cos", [a]) -> dimensionless (Right . cosM p) a
  ("tan", [a]) -> dimensionless (arith . tanM p) a
  ("asin", [a]) -> angle (arith . asinM p) a
  ("acos", [a]) -> angle (arith . acosM p) a
  ("atan", [a]) -> angle (Right . atanM p) a
  ("sinh", [a]) -> dimensionless (\x -> exponential abs x >> Right (sinhM p x)) a
  ("cosh", [a]) -> dimensionless (\x -> exponential abs x >> Right (coshM p x)) a
  ("tanh", [a]) -> dimensionless (Right . tanhM p) a
  ("atan2", [a, b]) -> do
    y <- scalar =<< a
    x <- scalar =<< b
    num (dimBase Ang) Nothing <$> arith (atan2M p y x)
  ("pi", []) -> Right (num dimOne Nothing (piM p))
  -- Euclidean norm of a vector.
  ("norm", [a]) -> do
    (_, d, hint, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    r <- arith (sqrtM p (sumM p [mulM p x x | x <- xs]))
    Right (num d hint r)
  ("det", [a]) -> do
    (dims, _, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        num dimOne Nothing <$> arith (determinantM p n rows)
      _ -> Left (Internal "det of a non-square matrix")
  ("cholesky", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        l <-
          arith (choleskyM p "cholesky needs a symmetric matrix" rows)
        d2 <-
          maybe
            (Left (Internal "cholesky of a dimension that is not a square"))
            Right
            (dimRoot 2 d)
        Right (VTensor [n, n] d2 Nothing (V.fromList (map Right (concat l))))
      _ -> Left (Internal "cholesky of a non-square matrix")
  ("inverse", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        inv <- arith (invertM p n rows)
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
        allocation cfg.limits [n, n]
          >> Right
            ( VTensor
                [n, n]
                (dimMul dim1 dim2)
                (combine (hintMul hp) h1 h2)
                ( V.generate
                    (n * n)
                    ( \k ->
                        let (j, i) = k `divMod` n
                         in (\x y x' y' -> subM p (mulM p x y) (mulM p x' y'))
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
        r <- arith (matrixExpM p n rows)
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
                   in sumM p <$> sequence [buf V.! (base + c * diagonal) | c <- [0 .. dims !! lo - 1]]
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
        Right
          (VTensor [k] dimOne Nothing (V.generate k (Right . literal p . fromIntegral)))
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
            (V.fromList (map (Right . literal p . fromIntegral) (unflatten dims q)))
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
    let shown h =
          (\h' -> h'{pinned = True})
            <$> mkHintAs PreserveExpression hp (mergeAtoms [] h.atoms)
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
    stepI <- maybe (Right (literal p 1, d, Nothing)) scalarFull =<< optional st
    amount <-
      maybe (Right (V.replicate (product lens) (literal p 0))) amountOf =<< optional o
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
      maybe (Right (V.replicate (V.length parentChart.origin) (literal p 0))) amountOf
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
  -- An amount from a chart's origin along its axes (design §7.7): the
  -- coordinates with the step applied are the amount itself.
  ("pointAt", [s, v]) -> do
    sc <- chartOf =<< s
    (_, _, _, vs) <- tensor =<< v
    Right (VPoint sc.dims sc.dim sc vs)
  -- Within a frame, coordinate arithmetic. A difference carries the step
  -- unit of the chart both points were written on.
  ("pointAdd", [pt, v]) -> do
    (dims, d, sc, buf) <- point =<< pt
    (_, _, _, vs) <- tensor =<< v
    Right (VPoint dims d sc (V.zipWith (\m dv -> addM p <$> m <*> dv) buf vs))
  ("pointSub", [pt, q]) -> do
    (dims, d, sc1, m1) <- point =<< pt
    (_, _, sc2, m2) <- point =<< q
    let hint = if sc1.name == sc2.name then sc1.stepHint else Nothing
    Right (VTensor dims d hint (V.zipWith (\x y -> subM p <$> x <*> y) m1 m2))
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
    rm <- fromMaybe (Right (identityMatrix p n)) sc.rotation
    Right (VTensor [n, n] dimOne Nothing (V.map Right rm))
  -- A chart's absolute angular velocity and the velocity of its origin,
  -- along the base axes (design §3.8): exactly zero for a chart that does
  -- not move.
  ("spinOf", [s]) -> do
    sc <- chartOf =<< s
    let n = V.length sc.origin
    ws <- fromMaybe (Right (V.replicate n (literal p 0))) sc.spinAbs
    Right (VTensor [n] (dimInv (dimBase T)) Nothing (V.map Right ws))
  ("originVelocityOf", [s]) -> do
    sc <- chartOf =<< s
    let n = V.length sc.origin
    vs <- fromMaybe (Right (V.replicate n (literal p 0))) sc.originVelocity
    Right (VTensor [n] (dimDiv sc.dim (dimBase T)) Nothing (V.map Right vs))
  -- Its origin, an amount from the space's base origin along the base
  -- axes (design §3.10, F5).
  ("originOf", [s]) -> do
    sc <- chartOf =<< s
    Right (VTensor [V.length sc.origin] sc.dim Nothing (V.map Right sc.origin))
  -- Not a primitive of the language: the evaluator's own, for the fields
  -- of data compared, every one evaluated. Last, so that the primitives'
  -- names are matched in one run.
  _ | prim == conjunctionName -> conjunction args
  -- The backend's own built-ins (design §8.2): the shapes are shared, the
  -- numbers the backend's.
  _ | Just o <- own @s prim -> runOwn o
  -- Another backend's: refused before running (design §8.2), so reached
  -- only by an evaluation that skipped the check.
  _
    | Just _ <- ownerOf prim ->
        Left (Metron.Eval.Domain (lacks (backendOf @s) prim))
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
  p = settingsOf cfg
  hp = precisionOf cfg
  wrongArity = Left (Internal (prim <> " applied to the wrong number of arguments"))
  runOwn :: Own s -> ThunkOf s
  runOwn = \case
    Each shape checked f -> case args of
      [a] -> do
        (dims, d, hint, buf) <- tensor =<< a
        let each x = arith (f p x) >>= if checked then sized cfg.limits else Right
        Right $ case shape of
          Scalar.Keep -> VTensor dims d hint (V.map (>>= each) buf)
          Scalar.Bare -> VTensor dims dimOne Nothing (V.map (>>= each) buf)
      _ -> wrongArity
    -- Σ cᵢ cᵢᵀ over the statistical nudges (design §3.5). The covariance is
    -- the cross-covariance of a vector with itself, with no display unit
    -- of its own; of two vectors, in the product of their dimensions and
    -- display units, as for outer.
    Covariance f -> case args of
      [a] -> do
        (_, d, _, buf) <- tensor =<< a
        xs <- sequence (V.toList buf)
        Right (matrixValue (dimPow 2 d) Nothing (length xs) (length xs) (f p xs xs))
      [a, b] -> do
        (_, d1, h1, xs) <- tensor =<< a
        (_, d2, h2, ys) <- tensor =<< b
        as <- sequence (V.toList xs)
        bs <- sequence (V.toList ys)
        Right
          ( matrixValue
              (dimMul d1 d2)
              (hintProduct hp h1 h2)
              (length as)
              (length bs)
              (f p as bs)
          )
      _ -> wrongArity
    Test f -> case args of
      [a] -> VBool . f <$> (scalar =<< a)
      _ -> wrongArity
    Constant f -> case args of
      [] -> Right (num dimOne Nothing (f p))
      _ -> wrongArity
    Combine dimF f -> do
      parts <- mapM (scalarFull =<<) args
      Right
        (num (dimF [d | (_, d, _) <- parts]) Nothing (f p [x | (x, _, _) <- parts]))
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
    let originM = maybe along (\pc -> V.zipWith (addM p) pc.origin along) parentChart
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
            ascend x c = V.zipWith (addM p) c.localOrigin <$> turn n c.relativeRotation x
            descend x c = turn n c.relativeRotationInverse (V.zipWith (subM p) x c.localOrigin)
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
    Right (VTensor dims d hint (V.map (>>= sized cfg.limits . op) buf))
  elementwise2 op dimOp hintOp a b = do
    (dims, d1, h1, xs) <- tensor =<< a
    (_, d2, h2, ys) <- tensor =<< b
    Right
      ( VTensor
          dims
          (dimOp d1 d2)
          (hintOp h1 h2)
          (V.zipWith (\x y -> do x' <- x; y' <- y; op x' y' >>= sized cfg.limits) xs ys)
      )
  -- A scalar function whose result is a bare dimensionless number.
  dimensionless f a = do
    x <- scalar =<< a
    num dimOne Nothing <$> f x
  -- e^x has about x·log₁₀ e digits: known before the series is summed
  -- (design §8.1), which for a large x would run for minutes. The
  -- exponent is the midpoint's, measured by the given sign rule.
  exponential sign x = case sizeOf x of
    Nothing -> Right ()
    Just m ->
      let e = sign (fromRational m) * logBase 10 (exp 1) :: Double
       in maybe
            (Right ())
            (Left . Exceeded Digits . ("the exponential " <>))
            (beyond cfg.limits e)
  -- A scalar function whose result is an angle in radians.
  angle f a = do
    x <- scalar =<< a
    num (dimBase Ang) Nothing <$> f x
  -- A condition as a value in this evaluation (design §8.2).
  condition = conditionIn rt.context
  compareWith rel a b = do
    x <- ordered =<< a
    y <- ordered =<< b
    (\d -> condition d.holds d.copies) <$> arith (relate p rel x y)
  equalAll xs ys =
    uncurry condition . foldl' (combined (&&)) (True, Nothing)
      <$> mapM
        (\(u, v) -> (\d -> (d.holds, d.copies)) <$> arith (equalM p u v))
        (zip xs ys)
  negated (h, o) = (not h, (\x -> x{each = VU.map not x.each}) <$> o)
  conditionOf v = (,outcomesOf v) <$> bool v
  -- An operation on a mixture (design §8.2): this primitive again, for
  -- each option, its other operands narrowed to the option's copies.
  again name m before after =
    perOption cfg rt m $ \cfg' rt' r v ->
      runPrim
        cfg'
        rt'
        name
        ty
        (map (fmap (narrow r)) before ++ Right v : map (fmap (narrow r)) after)
  {- @a && b@ and @a || b@ (design §8.2): when the first decides, the
  second is not evaluated, and a copy whose own first operand would have
  gone on to it leaves the evaluated path here; its result is taken to
  be the nominal one. Samples, whose first operands differ, split. -}
  shortCircuit isAnd a b =
    a >>= \case
      VMixture m -> again prim m [] [b]
      xv -> do
        (x, ox) <- conditionOf xv
        if x == isAnd
          then
            b >>= \case
              VMixture m -> again prim m [Right xv] []
              yv -> do
                (y, oy) <- conditionOf yv
                Right
                  (uncurry condition (combined (if isAnd then (&&) else (||)) (x, ox) (y, oy)))
          else case ox of
            Just o
              | VU.any (== isAnd) o.each ->
                  let leaving =
                        IntSet.fromList
                          [ memberAt p.copies i
                          | (i, goesOn) <- zip [0 ..] (VU.toList o.each)
                          , goesOn == isAnd
                          ]
                   in Right
                        ( condition
                            x
                            (Just o{left = IntSet.union o.left leaving, each = VU.map (const x) o.each})
                        )
            _ -> Right (condition x ox)
  negation a =
    a >>= \case
      VMixture m -> again "not" m [] []
      v -> uncurry condition . negated <$> conditionOf v
  -- Every condition, all of them evaluated, copy by copy; a mixture among
  -- them splits.
  conjunction ts = do
    vs <- sequence ts
    case break isMixture vs of
      (before, VMixture m : after) -> again conjunctionName m (map Right before) (map Right after)
      _ ->
        uncurry condition . foldl' (combined (&&)) (True, Nothing)
          <$> mapM conditionOf vs
  isMixture = \case
    VMixture _ -> True
    _ -> False
  -- Tensors of one shape (lint agrees), data or points: the equality
  -- instances of design §4.2. Tensors are equal when every component is
  -- decided equal (design §3.2.9). Copy by copy, so are their copies; a
  -- mixture splits.
  equal a b = do
    x <- a
    y <- b
    case (x, y) of
      (VMixture m, _) -> again "eq" m [] [Right y]
      (_, VMixture m) -> again "eq" m [Right x] []
      (VTensor _ _ _ xs, VTensor _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        equalAll xs' ys'
      (VCon c xs cx, VCon c' ys cy)
        | c == c' && length xs == length ys ->
            conjunction
              ( Right (uncurry condition (sameCon c c' cx cy))
                  : zipWith (\u v -> runPrim cfg rt "eq" ty [u, v]) xs ys
              )
        | otherwise -> Right (uncurry condition (sameCon c c' cx cy))
      (VPoint _ _ _ xs, VPoint _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        equalAll xs' ys'
      _ ->
        Left
          (Internal "==: operands are not both tensors, both data or both points")
  -- Whether two constructors are the same, copy by copy when either's
  -- copies choose their own.
  sameCon c c' cx cy =
    let mine = \case
          NoCopies -> Nothing
          Copied cause left alts -> Just (cause, left, alts)
        alike = VU.replicate (memberCount p.copies)
        causeOf = maybe Rounding (\(cause, _, _) -> cause)
        leftOf = maybe IntSet.empty (\(_, left, _) -> left)
        altsOr k = maybe (alike k) (\(_, _, alts) -> alts)
     in ( c == c'
        , case (mine cx, mine cy) of
            (Nothing, Nothing) -> Nothing
            (l, r) ->
              Just
                ( Outcomes
                    (causeOf l <> causeOf r)
                    (IntSet.union (leftOf l) (leftOf r))
                    (VU.zipWith (==) (altsOr (conIndex c) l) (altsOr (conIndex c') r))
                )
        )
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
           in sumM p
                <$> sequence
                  [ mulM p <$> (rbuf V.! (i * n + j)) <*> (buf V.! (base + j * st))
                  | j <- [0 .. n - 1]
                  ]
     in V.generate (product dims) element

sumM :: (Scalar s) => Settings -> [s] -> s
sumM p = foldl' (addM p) (literal p 0)

{- | Whether a tensor of these lengths may be built: at most the session's
@components@ (design §8.1), counted without overflow. A product whose
operands are each within the limit can exceed it.
-}
allocation :: Limits -> [Int] -> Either EvalError ()
allocation l dims
  | n > toInteger l.components =
      Left
        ( Exceeded
            Components
            ( "the result would have "
                <> tshow n
                <> " components, more than "
                <> tshow l.components
            )
        )
  | otherwise = Right ()
 where
  n = product (map toInteger dims)

{- | A number, unless it is further from 1 than the session's @digits@
allows (design §8.1). Only a magnitude is measured: an exact result's
length is the precision's concern (design §3.2.8).
-}
sized :: (Scalar s) => Limits -> s -> Either EvalError s
sized l x = case sizeOf x >>= beyond l . log10Abs of
  Nothing -> Right x
  Just err -> Left (Exceeded Digits ("the result " <> err))

-- Index arithmetic ----------------------------------------------------------------------

{- | The literal index positions of @contract@, @permute@ or @slice@: a number or a
vector of exact naturals (the desugarer admits nothing else).
-}
positions :: (Scalar s) => ThunkOf s -> Either EvalError [Int]
positions t = do
  (_, _, _, buf) <- tensor =<< t
  xs <- sequence (V.toList buf)
  mapM natural xs
 where
  natural = \case
    (exactly -> Just r)
      | denominator r == 1
      , r >= 0
      , numerator r < lengthLimit ->
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
chartRoute :: (Scalar s) => ChartOf s -> ChartOf s -> ([ChartOf s], [ChartOf s])
chartRoute source target = shared (reverse (path source)) (reverse (path target))
 where
  path c = case c.parent of
    Just parent
      | c.frame == parent.frame
      , null c.generators
      , V.all ((== Just 0) . exactly) c.localOrigin ->
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
  (Scalar s) =>
  Settings ->
  Int ->
  Maybe (ChartOf s) ->
  [Vector s] ->
  ( Maybe (Either EvalError (Vector s))
  , Maybe (Either EvalError (Vector s))
  )
chartFrame p n parentChart gens =
  ( compose (parentChart >>= (.rotation)) (local id gens)
  , compose (local (V.map negM) (reverse gens)) (parentChart >>= (.rotationInverse))
  )
 where
  local _ [] = Nothing
  local sign gs = Just (foldr1 (\a b -> matrixProduct p n <$> a <*> b) (map (expOf . sign) gs))
  expOf g = do
    rows <- arith (matrixExpM p n (chunk (V.toList g)))
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
  (Scalar s) =>
  Settings ->
  Int ->
  Maybe (ChartOf s) ->
  Maybe (Either EvalError (Vector s)) ->
  Vector s ->
  Maybe (Vector s) ->
  ( Maybe (Either EvalError (Vector s))
  , Maybe (Either EvalError (Vector s))
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
            Right (V.zipWith (addM p) v transport)
  )
 where
  zeros = V.replicate n (literal p 0)
  turn w = case rotationAbs of
    Nothing -> Right w
    Just r -> (\rm -> rotateVector p n rm w) <$> r
  plus Nothing b = b
  plus a Nothing = a
  plus (Just a) (Just b) = Just (V.zipWith (addM p) <$> a <*> b)

-- | The cross product of two three-vectors of magnitudes.
cross3 ::
  (Scalar s) =>
  Settings ->
  Vector s ->
  Vector s ->
  Either EvalError (Vector s)
cross3 p a b
  | V.length a == 3 && V.length b == 3 =
      let x i j = subM p (mulM p (a V.! i) (b V.! j)) (mulM p (a V.! j) (b V.! i))
       in Right (V.fromList [x 1 2, x 2 0, x 0 1])
  | otherwise = Left (Internal "a spin is a three-vector")

{- | A chart's coordinates are its amounts divided by its step (design
§3.10, F6), so the step must be invertible: its enclosure must exclude
zero. A negative step reverses the chart's direction and is allowed.
-}
invertibleStep :: (Scalar s) => s -> Either EvalError ()
invertibleStep step = maybe (Right ()) (Left . ChartStep Nothing) (stepProblem step)

-- | Name a chart whose step may be zero after the reference that reached it.
namedChart :: Maybe Text -> EvalError -> EvalError
namedChart name = \case
  ChartStep Nothing why | Just _ <- name -> ChartStep name why
  err -> err

{- | The coordinates of a point on the chart it was written on (design
§3.10, F6): its coordinates on its frame, the step divided out.
-}
coordinatesOn ::
  (Scalar s) =>
  Settings -> ChartOf s -> [s] -> Either EvalError [s]
coordinatesOn p c = arith . mapM (\x -> divM p x c.step)

-- | The elements of a list value, as thunks.
listElems :: ValueOf s -> Either EvalError [ThunkOf s]
listElems = \case
  VData NilC [] -> Right []
  VData ConsC [x, xs] -> (x :) <$> (listElems =<< xs)
  VMixture _ -> Left mixed
  _ -> Left (Internal "expected a list")

-- | The @n × n@ identity, row-major and exact.
identityMatrix :: (Scalar s) => Settings -> Int -> Vector s
identityMatrix p n =
  V.generate
    (n * n)
    (\k -> if k `div` n == k `mod` n then literal p 1 else literal p 0)

-- | The product of two row-major @n × n@ matrices.
matrixProduct ::
  (Scalar s) =>
  Settings -> Int -> Vector s -> Vector s -> Vector s
matrixProduct p n a b =
  V.generate
    (n * n)
    ( \k ->
        let (i, j) = k `divMod` n
         in sumM p [mulM p (a V.! (i * n + l)) (b V.! (l * n + j)) | l <- [0 .. n - 1]]
    )

-- | A row-major @n × n@ matrix applied to a vector.
rotateVector ::
  (Scalar s) =>
  Settings -> Int -> Vector s -> Vector s -> Vector s
rotateVector p n r v =
  V.generate
    n
    (\i -> sumM p [mulM p (r V.! (i * n + j)) (v V.! j) | j <- [0 .. n - 1]])

chunksOf :: Int -> [a] -> [[a]]
chunksOf n xs
  | null xs = []
  | otherwise = let (r, rest) = splitAt n xs in r : chunksOf n rest

{- | The @m × n@ matrix of exact cross-covariances of two lists of
magnitudes (design §3.5), in the given dimension and display unit. Shared
by @covariance@, @crossCovariance@ and the REPL's @:covariance@.
-}
covarianceMatrix ::
  Config -> Dim -> Maybe UnitHint -> [Magnitude] -> [Magnitude] -> Value
covarianceMatrix cfg d hint as bs =
  matrixValue
    d
    hint
    (length as)
    (length bs)
    (affineCovariance cfg.nonlinear as bs)

-- | An @m × n@ matrix from its rows, each entry evaluated on its own.
matrixValue ::
  Dim -> Maybe UnitHint -> Int -> Int -> [[Either ArithError s]] -> ValueOf s
matrixValue d hint m n rows =
  VTensor [m, n] d hint (V.fromList (map arith (concat rows)))

{- | Pair the fields of a constructor with an alternative's binders; the
counts agree by lint.
-}
attach :: Vec k a -> [ThunkOf s] -> Vec k (ThunkOf s)
attach bs fields = case bs of
  VNil -> VNil
  VCons _ rest -> case fields of
    f : fs -> VCons f (attach rest fs)
    [] -> VCons (Left (Internal "case: missing field")) (attach rest [])

{- | A point converted from a frame whose chart takes parameters with no
@from@, when no type said so (design §3.10, F7): refused, never read off
the chart it was written on.
-}
takesArguments :: ChartOf s -> Text
takesArguments c =
  n <> " takes arguments: write p from (" <> n <> " …) to c"
 where
  n = case c.name of
    Just (UnitNamed t) -> t
    Just (UnitBase t) -> t
    Nothing -> "its frame"
