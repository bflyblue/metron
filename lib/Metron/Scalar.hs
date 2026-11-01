{-# LANGUAGE AllowAmbiguousTypes #-}

{- | The scalar domain the evaluator is generic over (design §8.2): what a
backend plugs in. Everything else the evaluator does, tensors, units and
dimensions, charts, data, closures and the resource limits, is shared and
never looks inside a scalar.

A backend is a type with an instance of 'Scalar': its arithmetic, its
linear-algebra kernels, the few facts the shared code asks of a number
(its exact value, if it has one; its size, for the @digits@ limit; a
display unit's factor), and a table of its own built-ins. The instance for
'Magnitude' is the affine backend of design §3.2, each method the
function the evaluator called before it became generic; "Metron.Double"
is the other.

A class and not a record of functions: the scalar type determines the
backend, so a value of one backend can never meet an operation of
another, and the evaluator, the printer and the tests name a backend by a
type. What a method needs from the session (the working precision, the
comparison policy, the number of samples) comes in a 'Settings', built
once per evaluation.
-}
module Metron.Scalar (
  Scalar (..),
  Backend (..),
  backendName,
  backendNamed,
  ownerOf,
  Refusal,
  refusalOf,
  refusal,
  refusalClause,
  needsSamples,
  lacks,
  Settings (..),
  Rounding (..),
  Batch (..),
  Members (..),
  memberCount,
  memberAt,
  globalOf,
  memberVector,
  wholeBatch,
  roundingName,
  roundingNamed,
  settingsAt,
  Decision (..),
  Outcomes (..),
  Rel (..),
  Own (..),
  Shape (..),
  affineCovariance,
) where

import Data.IntSet (IntSet)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Vector.Unboxed qualified as VU
import Metron.Affine (
  ArithError (..),
  Collapsed (bound, variance),
  Decide (..),
  Magnitude (Exact),
  Origin,
  Precision,
  Skew (operation),
  boundRadius,
  collapse,
  crossCovarianceRows,
  midpoint,
  nonLinearAt,
 )
import Metron.Affine qualified as A
import Metron.Core (NudgeKind)
import Metron.Dimension (Dim)
import Metron.Numerical.Linear qualified as L
import Metron.Remark (Cause)

-- | The evaluators of the scalars a session can choose (@:backend@).
data Backend
  = -- | rationals with affine error forms (design §3.2), the default
    AffineBackend
  | -- | IEEE 754 doubles with an error estimate (design §8.2)
    DoubleBackend
  deriving stock (Eq, Show, Enum, Bounded)

-- | A backend's name, as @:backend@ and @--backend@ take it.
backendName :: Backend -> Text
backendName = \case
  AffineBackend -> "affine"
  DoubleBackend -> "double"

backendNamed :: Text -> Maybe Backend
backendNamed t = lookup t [(backendName b, b) | b <- [minBound .. maxBound]]

{- | The built-ins only one backend has (design §8.2), as a program names
them: the affine backend's read or make uncertainty, the double
backend's describe the format and its error estimate. Each is in its
backend's 'own' table, or, for @±@, @±σ@, @noise@ and @gauss@, a form of
Core.
-}
backendOwn :: Backend -> [Text]
backendOwn = \case
  AffineBackend ->
    [ "±"
    , "±σ"
    , "noise"
    , "gauss"
    , "mid"
    , "sd"
    , "bound"
    , "covariance"
    , "crossCovariance"
    ]
  DoubleBackend ->
    ["errorOf", "digitsOf", "ulps", "eps", "nextUp", "fma", "isNaN", "isInfinite"]

-- | The backend a built-in belongs to, when only one has it.
ownerOf :: Text -> Maybe Backend
ownerOf name = case [b | b <- [minBound .. maxBound], name `elem` backendOwn b] of
  b : _ -> Just b
  [] -> Nothing

{- | The affine backend's built-ins the double backend has too when it
carries copies (design §8.2): a declared σ is drawn in each copy, and
@mid@ and @sd@ are the copies' mean and deviation. With no copies, under
@samples 0@, it has none of them. @noise@ is not among them: it makes a
bound unknown, which has no distribution to draw, so it is refused at
every setting, as @±@ is.
-}
sampledOwn :: [Text]
sampledOwn = ["±σ", "gauss", "mid", "sd"]

-- | Why a backend, at a setting, cannot run a built-in.
data Refusal
  = -- | the backend does not have it at all
    Lacks
  | -- | the double backend has it only with copies
    NeedsSamples
  deriving stock (Eq, Show)

{- | Whether a backend, at a number of samples, can run a built-in a program
names; the reason if not. The check before running asks it of every
backend-specific built-in an input reaches.
-}
refusalOf :: Backend -> Int -> Text -> Maybe Refusal
refusalOf b n name = case ownerOf name of
  Just o
    | o /= b ->
        if b == DoubleBackend && name `elem` sampledOwn
          then if n > 0 then Nothing else Just NeedsSamples
          else Just Lacks
  _ -> Nothing

-- | The refusal of a built-in used directly.
refusal :: Backend -> Text -> Refusal -> Text
refusal b name = \case
  Lacks -> lacks b name
  NeedsSamples -> needsSamples name

-- | The refusal's end, for a built-in reached through definitions.
refusalClause :: Backend -> Refusal -> Text
refusalClause b = \case
  Lacks -> "which the " <> backendName b <> " backend does not have"
  NeedsSamples -> "which needs `:set samples N` under the double backend"

-- | Why the double backend refuses a built-in that needs its copies.
needsSamples :: Text -> Text
needsSamples name = "`" <> name <> "` needs `:set samples N` under the double backend"

-- | Why a backend refuses another's built-in.
lacks :: Backend -> Text -> Text
lacks b name =
  "`"
    <> name
    <> "` is the "
    <> maybe "other" backendName (ownerOf name)
    <> " backend's; the "
    <> backendName b
    <> " backend does not have it"

{- | What a backend's arithmetic needs from the session, fixed for one
evaluation.
-}
data Settings = Settings
  { precision :: Precision
  -- ^ working precision: significant digits plus guard digits (design §3.2.8)
  , decide :: Decide
  -- ^ how a comparison is decided (design §3.2.9)
  , samples :: Int
  -- ^ the double backend's copies under random rounding; 0 is the running bound (design §8.2)
  , seed :: Int
  -- ^ the seed of those copies' random choices (@:set seed@)
  , rounding :: Rounding
  -- ^ how each copy rounds (@:set rounding@)
  , copies :: !Members
  -- ^ which of the copies this evaluation carries
  }
  deriving stock (Eq, Show)

{- | The copies one evaluation carries (design §8.2, @:set cores@): when the
samples run in parallel batches, each evaluation carries copies @first@
to @first + count − 1@ of the @samples@, as one of @batches@. A copy's
random choices are keyed by its number among all the samples, so a
result does not depend on how the copies are batched.
-}
data Batch = Batch {first :: Int, count :: Int, batches :: Int}
  deriving stock (Eq, Show)

-- | All the copies in one evaluation.
wholeBatch :: Int -> Batch
wholeBatch n = Batch{first = 0, count = n, batches = 1}

{- | The copies an evaluation carries, by their global numbers, ascending
(design §8.2): a batch's run of them, or the group of them a branch
point sent down one alternative. A number's copies are in this order.
-}
data Members
  = -- | the copies from the first, so many
    Range !Int !Int
  | -- | the copies listed
    Listed !(VU.Vector Int)
  deriving stock (Eq, Show)

memberCount :: Members -> Int
memberCount = \case
  Range _ n -> n
  Listed v -> VU.length v

-- | The global number of the copy at a place.
memberAt :: Members -> Int -> Int
memberAt m i = case m of
  Range first _ -> first + i
  Listed v -> VU.unsafeIndex v i
{-# INLINE memberAt #-}

{- | The global number of the copy at each place, the kind of members found
once, for a loop over the copies.
-}
globalOf :: Members -> Int -> Int
globalOf = \case
  Range first _ -> (first +)
  Listed v -> VU.unsafeIndex v
{-# INLINE globalOf #-}

memberVector :: Members -> VU.Vector Int
memberVector = \case
  Range first n -> VU.enumFromN first n
  Listed v -> v

{- | How the double backend's copies round (design §8.2, @:set
rounding@): each to nearest, so that they differ only in their draws of
the declared uncertainty, or each randomly up or down (CESTAC), so that
their spread is rounding and the draws together.
-}
data Rounding = RoundNearest | RoundRandom
  deriving stock (Eq, Show, Enum, Bounded)

-- | A rounding's name, as @:set rounding@ takes it.
roundingName :: Rounding -> Text
roundingName = \case
  RoundNearest -> "nearest"
  RoundRandom -> "random"

roundingNamed :: Text -> Maybe Rounding
roundingNamed t = lookup t [(roundingName r, r) | r <- [minBound .. maxBound]]

{- | Settings at a working precision with the default comparison policy and
no samples: for the printer, which converts to a display unit.
-}
settingsAt :: Precision -> Settings
settingsAt p =
  Settings
    { precision = p
    , decide = Decide{sigma = 3, nonlinear = 1 / 100}
    , samples = 0
    , seed = 0
    , rounding = RoundRandom
    , copies = Range 0 0
    }

-- | An order relation, as the comparisons ask it.
data Rel = Lt | Le | Gt | Ge
  deriving stock (Eq, Show)

{- | A decided comparison, and, when the operands have copies, what each
copy's own operands say (design §8.2). The result is the nominal one; a
branch point on it counts the copies by their own.
-}
data Decision = Decision {holds :: Bool, copies :: Maybe Outcomes}
  deriving stock (Eq, Show)

{- | A condition copy by copy, in the order of the evaluation's copies,
what the copies spread by, and the copies, by global number, already off
their own path where the condition was decided: a short circuit the
nominal value took, where a copy's own operand would have gone on (design
§8.2). A comparison's are none.
-}
data Outcomes = Outcomes {cause :: Cause, left :: IntSet, each :: VU.Vector Bool}
  deriving stock (Eq, Show)

-- | Where an elementwise built-in's result lives.
data Shape
  = -- | the operand's dimension and display unit
    Keep
  | -- | a bare dimensionless number
    Bare
  deriving stock (Eq, Show)

{- | A backend's own built-in (design §8.2), by its shape; the evaluator
supplies the tensors, the dimensions and the display units.
-}
data Own s
  = {- | componentwise, each component's result measured against @digits@
    when the flag is set
    -}
    Each Shape Bool (Settings -> s -> Either ArithError s)
  | {- | the matrix of a vector against itself (one argument) or against
    another (two), in the square or the product of their dimensions
    -}
    Covariance (Settings -> [s] -> [s] -> [[Either ArithError s]])
  | -- | a question about one number
    Test (s -> Bool)
  | -- | a dimensionless constant
    Constant (Settings -> s)
  | -- | numbers in, a number out, whose dimension the operands' give
    Combine ([Dim] -> Dim) (Settings -> [s] -> s)

{- | A backend's scalars. Every arithmetic method has the name and the
shape of the "Metron.Affine" function it generalises, with 'Settings'
where that takes the precision.
-}
class (Eq s) => Scalar s where
  -- | Which backend this is.
  backendOf :: Backend

  -- | A literal, an exact rational, at the boundary into the backend.
  literal :: Settings -> Rational -> s

  -- | The exact value, when the number is one: index positions, a route's zero offsets.
  exactly :: s -> Maybe Rational

  addM, subM, mulM :: Settings -> s -> s -> s
  negM :: s -> s
  absM :: Settings -> s -> s
  divM :: Settings -> s -> s -> Either ArithError s
  powM :: Settings -> s -> Integer -> Either ArithError s
  sqrtM, logM, tanM, asinM, acosM :: Settings -> s -> Either ArithError s
  expM, sinM, cosM, atanM, sinhM, coshM, tanhM :: Settings -> s -> s
  atan2M :: Settings -> s -> s -> Either ArithError s
  piM :: Settings -> s
  floorM, ceilM, roundM :: Settings -> s -> Either ArithError s

  -- | @a rel b@, decided as the backend decides (design §3.2.9, §8.2).
  relate :: Settings -> Rel -> s -> s -> Either ArithError Decision

  equalM :: Settings -> s -> s -> Either ArithError Decision

  {- | The number the @digits@ limit measures (design §8.1), when one
  applies: under IEEE a number too large is infinite, not an error.
  -}
  sizeOf :: s -> Maybe Rational

  {- | Why a chart's step cannot be divided by, if it cannot (design §3.10,
  F6).
  -}
  stepProblem :: s -> Maybe Text

  -- | The number as a display unit's factor, which is exact (design §3.2.12).
  hintFactor :: s -> Magnitude

  -- | A component of @noise n@ or @gauss n@ (design §3.2.5).
  noiseM :: Settings -> NudgeKind -> Origin -> Either ArithError s

  -- | @x ± e@, @x ±σ e@.
  uncertainM :: Settings -> NudgeKind -> Origin -> s -> s -> Either ArithError s

  determinantM :: Settings -> Int -> [[s]] -> Either ArithError s
  invertM :: Settings -> Int -> [[s]] -> Either ArithError [[s]]
  matrixExpM :: Settings -> Int -> [[s]] -> Either ArithError [[s]]

  -- | A lower factor, the text naming what must be symmetric.
  choleskyM :: Settings -> Text -> [[s]] -> Either ArithError [[s]]

  -- | The backend's own built-ins by name (design §8.2).
  own :: Text -> Maybe (Own s)

  {- | A number for a group of its copies (design §8.2): the copies at
  these places, in this order. A number without copies is itself.
  -}
  restrictM :: VU.Vector Int -> s -> s
  restrictM _ = id

  {- | The numbers the groups of a split computed, put back together copy
  by copy (design §8.2): so many copies in all, the nominal group's
  number, if the evaluation has one, and each group's number with the
  places of its copies among all of them.
  -}
  scatterM :: Int -> Maybe s -> [(VU.Vector Int, s)] -> s
  scatterM _ nominal parts = case (nominal, parts) of
    (Just x, _) -> x
    (Nothing, (_, x) : _) -> x
    (Nothing, []) -> literal (settingsAt 0) 0

-- The affine backend -----------------------------------------------------------------

instance Scalar Magnitude where
  backendOf = AffineBackend
  literal _ = Exact
  exactly = \case
    Exact r -> Just r
    _ -> Nothing
  addM s = A.addM s.precision
  subM s = A.subM s.precision
  mulM s = A.mulM s.precision
  negM = A.negM
  absM s = A.absM s.precision
  divM s = A.divM s.precision
  powM s = A.powM s.precision
  sqrtM s = A.sqrtM s.precision
  logM s = A.logM s.precision
  tanM s = A.tanM s.precision
  asinM s = A.asinM s.precision
  acosM s = A.acosM s.precision
  expM s = A.expM s.precision
  sinM s = A.sinM s.precision
  cosM s = A.cosM s.precision
  atanM s = A.atanM s.precision
  sinhM s = A.sinhM s.precision
  coshM s = A.coshM s.precision
  tanhM s = A.tanhM s.precision
  atan2M s = A.atan2M s.precision
  piM s = A.piM s.precision
  floorM s = A.floorM s.decide s.precision
  ceilM s = A.ceilM s.decide s.precision
  roundM s = A.roundM s.decide s.precision
  relate s rel x y = decided . holdsFor <$> A.compareM s.decide s.precision x y
   where
    holdsFor o = case rel of
      Lt -> o == LT
      Le -> o /= GT
      Gt -> o == GT
      Ge -> o /= LT
  equalM s x y = decided <$> A.equalM s.decide s.precision x y
  sizeOf = Just . midpoint
  stepProblem step
    | step == Exact 0 = Just "its step is zero"
    | abs (midpoint step) <= boundRadius step =
        Just "its step's enclosure reaches zero"
    | otherwise = Nothing
  hintFactor = id
  noiseM _ k o = Right (A.unitNoise k o)
  uncertainM _ k o x e = Right (A.uncertain k o x e)
  determinantM s = L.determinant s.precision
  invertM s = L.invert s.precision
  matrixExpM s = L.matrixExp s.precision
  choleskyM s what = L.choleskyRows what s.decide s.precision
  own = \case
    -- The parts of an enclosure as the printer collapses it (design
    -- §3.2.9, §3.2.10), each exact but sd: the midpoint, the bound radius
    -- Σ_bound |cᵢ| + slack, and the standard deviation √(Σ_stat cᵢ²), exact
    -- when the variance is a square and otherwise an enclosure of the
    -- root. A value marked non-linear has no mean and σ that describe it
    -- (design §3.2), so mid and sd refuse it; its bound is still rigorous.
    "mid" -> Just (Each Keep False (\s -> described s "mid" (Right . Exact . midpoint)))
    "bound" -> Just (Each Keep True (\_ x -> Right (Exact (collapse x).bound)))
    "sd" ->
      Just
        ( Each
            Keep
            False
            (\s -> described s "sd" (A.sqrtM s.precision . Exact . (.variance) . collapse))
        )
    -- Σ cᵢ cᵢᵀ over the statistical nudges (design §3.5): exact, from the
    -- coefficients.
    "covariance" -> Just (Covariance (\s -> affineCovariance s.decide.nonlinear))
    "crossCovariance" -> Just (Covariance (\s -> affineCovariance s.decide.nonlinear))
    _ -> Nothing

decided :: Bool -> Decision
decided b = Decision{holds = b, copies = Nothing}

-- | An accessor of a mean or a σ, refusing a value marked non-linear.
described ::
  Settings ->
  Text ->
  (Magnitude -> Either ArithError Magnitude) ->
  Magnitude ->
  Either ArithError Magnitude
described s what f x = case nonLinearAt s.decide.nonlinear x of
  Just sk ->
    Left
      ( Domain
          ( what
              <> " of a value marked non-linear by "
              <> sk.operation
              <> ": a mean and a σ do not describe it (design §3.2)"
          )
      )
  Nothing -> f x

{- | The exact cross-covariances of two lists of magnitudes (design §3.5),
row by row; an entry of a value marked non-linear (over the given
threshold) is refused.
-}
affineCovariance ::
  Rational -> [Magnitude] -> [Magnitude] -> [[Either ArithError Magnitude]]
affineCovariance threshold as bs =
  [ [entry a b c | (b, c) <- zip bs row]
  | (a, row) <- zip as (crossCovarianceRows as bs)
  ]
 where
  entry a b c
    | any (isJust . nonLinearAt threshold) [a, b] =
        Left (Domain "covariance of a value marked non-linear is not supported")
    | otherwise = Right (Exact c)
