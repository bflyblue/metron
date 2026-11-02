{-# LANGUAGE AllowAmbiguousTypes #-}

{- | The scalar domain the evaluator is generic over (design §8.2): what a
backend plugs in. Everything else the evaluator does, tensors, units and
dimensions, charts, data, closures and the resource limits, is shared and
never looks inside a scalar.

A backend is a type with an instance of 'Scalar': its arithmetic, its
linear-algebra kernels, the few facts the shared code asks of a number
(its exact value, if it has one; its size, for the @digits@ limit; a
display unit's factor), and a table of its own built-ins. The instance for
"Metron.Rational" uses rational coefficients. "Metron.Double" uses IEEE doubles.

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
  settingsAt,
  atIndex,
  Decision (..),
  Outcomes (..),
  Rel (..),
  Own (..),
  Shape (..),
) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.IntSet (IntSet)
import Data.Text (Text)
import Data.Vector.Unboxed qualified as VU
import Metron.Dimension (Dim)
import Metron.Numerical.Approx (Precision)
import Metron.Numerical.Error (ArithError (..))
import Metron.Numerical.Identity (Origin)
import Metron.Numerical.Sampling (Distribution)
import Metron.Remark (Cause)

-- | The evaluators of the scalars a session can choose (@:set arithmetic@).
data Backend = RationalBackend | DoubleBackend
  deriving stock (Eq, Show, Enum, Bounded)

-- | A backend's name, as @:set arithmetic@ and @--set arithmetic@ take it.
backendName :: Backend -> Text
backendName = \case
  RationalBackend -> "rational"
  DoubleBackend -> "double"

backendNamed :: Text -> Maybe Backend
backendNamed t = lookup t [(backendName b, b) | b <- [minBound .. maxBound]]

-- | IEEE-specific operations available only with double arithmetic.
backendOwn :: Backend -> [Text]
backendOwn = \case
  RationalBackend -> []
  DoubleBackend ->
    ["ulps", "eps", "nextUp", "fma", "isNaN", "isInfinite"]

-- | The backend a built-in belongs to, when only one has it.
ownerOf :: Text -> Maybe Backend
ownerOf name = case [b | b <- [minBound .. maxBound], name `elem` backendOwn b] of
  b : _ -> Just b
  [] -> Nothing

-- | Input sampling and statistics shared by both arithmetic implementations.
sampledOwn :: [Text]
sampledOwn = ["sample", "mid", "sd", "covariance", "crossCovariance"]

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
refusalOf b n name
  | name `elem` sampledOwn && n < 1 = Just NeedsSamples
  | otherwise = case ownerOf name of
      Just o | o /= b -> Just Lacks
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
  , samples :: Int
  -- ^ Total realizations in this execution grid (design §8.2)
  , seed :: Int
  -- ^ the seed of those copies' random choices (@:set seed@)
  , rounding :: Rounding
  -- ^ how each copy rounds (@:set roundingAnalysis@)
  , copies :: !Members
  -- ^ which of the copies this evaluation carries
  , rounds :: Int
  , inputSampling :: Bool
  , occurrence :: ByteString
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

-- | Ordinary nearest rounding, or separate stochastic diagnostic repetitions.
data Rounding = RoundNearest | RoundRandom
  deriving stock (Eq, Show, Enum, Bounded)

{- | The settings a backend reads, at their defaults (design §7.3), at a
working precision, seed 1 and ordinary nearest rounding. It is the one definition of those defaults: the session's
('Metron.Eval.defaultConfig') are taken from it, and the printer uses it
to convert to a display unit.
-}
settingsAt :: Precision -> Settings
settingsAt p =
  Settings
    { precision = p
    , samples = 0
    , seed = 1
    , rounding = RoundNearest
    , copies = Range 0 0
    , rounds = 0
    , inputSampling = False
    , occurrence = ""
    }

-- | A deterministic sub-operation or tensor component, independent of run partition.
atIndex :: Settings -> Int -> Settings
atIndex s i = s{occurrence = s.occurrence <> BS.pack (":" ++ show i)}

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
    Test (s -> Decision)
  | -- | a dimensionless constant
    Constant (Settings -> s)
  | -- | numbers in, a number out, whose dimension the operands' give
    Combine ([Dim] -> Dim) (Settings -> [s] -> s)

{- | A backend's scalars. Every arithmetic method has the name and the
shape of the scalar operation, with 'Settings'
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
  sqrtM, logM, tanM, asinM, acosM, asinhM :: Settings -> s -> Either ArithError s
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
  hintFactor :: s -> Rational

  -- | A deterministic distribution parameter, excluding sampled values.
  distributionParameter :: s -> Maybe Rational
  distributionParameter = exactly

  sampleM :: Settings -> Origin -> Distribution -> Either ArithError s
  sampleM _ _ _ = Left (Domain "input sampling is not supported by this arithmetic")

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
  scatterM :: Settings -> Int -> Maybe s -> [(VU.Vector Int, s)] -> s
  scatterM _ _ nominal parts = case (nominal, parts) of
    (Just x, _) -> x
    (Nothing, (_, x) : _) -> x
    (Nothing, []) -> literal (settingsAt 0) 0
