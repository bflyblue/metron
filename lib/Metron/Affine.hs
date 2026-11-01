{- | Magnitudes (design §3.2): exact rationals, or affine forms
@mid + Σ cᵢ·eᵢ (± slack)@ whose noise symbols ("nudges") have a kind,
bound or statistical, and a content-addressed identity. Linear operations
combine nudges exactly, so @x - x = 0@; every nonlinear operation
linearises at the midpoint and adds one fresh bound nudge covering the
remainder, series truncation and rounding.

All arithmetic is exact rational arithmetic. The working precision @p@
decides how far series are summed and where midpoints are rounded, and
every rounding is accounted for. "@p@ digits" means @p@ significant digits:
an error of at most @10^-p@ relative to the value (design §3.2.8), so
quantities stored in SI base units at the size of Planck's constant keep
as many digits as quantities near one.
-}
module Metron.Affine (
  -- * Magnitudes
  Magnitude (..),
  Skew (..),
  Decide (..),
  skewOf,
  nonLinearAt,
  NudgeId (..),
  Origin (..),
  Nudge (..),
  Precision,
  isExact,
  midpoint,
  radius,
  boundRadius,
  nudges,

  -- * Collapse
  Collapsed (..),
  collapse,
  sigmaOf,
  statCoefficients,
  crossCovarianceRows,

  -- * Arithmetic
  ArithError (..),
  addM,
  subM,
  negM,
  scaleM,
  absM,
  mulM,
  divM,
  recipM,
  powM,
  sqrtM,
  expM,
  logM,
  sinM,
  cosM,
  tanM,
  asinM,
  acosM,
  atanM,
  atan2M,
  sinhM,
  coshM,
  tanhM,
  piM,
  sincSqM,
  coscSqM,
  enclose,
  floorM,
  ceilM,
  roundM,
  compareM,
  equalM,

  -- * Declared uncertainty
  uncertain,
  unitNoise,

  -- * Rounding helpers shared with the printer
  roundAt,
  decimalExponent,
  sqrtApprox,
) where

import Crypto.Hash.SHA256 qualified as SHA256 (hashlazy)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (length)
import Data.ByteString.Builder (
  Builder,
  byteString,
  toLazyByteString,
  word8,
 )
import Data.List (sort, sortOn)
import Data.Map.Merge.Strict qualified as Merge (
  merge,
  preserveMissing,
  zipWithMaybeMatched,
 )
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (
  delete,
  elems,
  empty,
  filter,
  insertWith,
  intersectionWith,
  map,
  mapMaybe,
  null,
  singleton,
  size,
  toList,
  unionWith,
 )
import Data.Maybe (catMaybes)
import Data.Ord (Down (..))
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T (pack)
import GHC.Num (integerLog2)
import Metron.Core (Hash (..), NudgeKind (..))
import Metron.Encode (sint, text, varint)
import Metron.Numerical.Approx (
  Approx,
  Precision,
  atanApprox,
  coshApprox,
  decimalExponent,
  expApprox,
  isqrt,
  logApprox,
  piApprox,
  precisionExponent,
  roundAt,
  roundUpAt,
  scaleA,
  sinCosApprox,
  sinhApprox,
  sqrtApprox,
  tolerance,
 )

-- Types -----------------------------------------------------------------------------

-- | Working precision in digits.
newtype NudgeId = NudgeId ByteString
  deriving stock (Eq, Ord, Show)

-- | Where a nudge came from, for the error budget (design §3.2.4).
data Origin
  = -- | a @±@, @±σ@, @noise@ or @gauss@: enclosing definition, path to the node, component
    Declared Hash [Int] Int
  | -- | the same, written with a @#label@: one unknown wherever the label appears
    Tagged Text Int
  | -- | an approximation inside a primitive
    Builtin Text
  deriving stock (Eq, Ord, Show)

data Nudge = Nudge {kind :: NudgeKind, origin :: Origin}
  deriving stock (Eq, Ord, Show)

data Magnitude
  = Exact !Rational
  | Affine
      { mid :: !Rational
      , terms :: !(Map NudgeId (Rational, Nudge))
      , slack :: !Rational
      -- ^ anonymous worst-case radius: rounding and compaction leftovers
      , skew :: !(Maybe Skew)
      -- ^ the most non-linear operation the statistical part went through
      }
  deriving stock (Eq, Show)

{- | How far from linear an operation found a value's statistical part
(design §3.2): the second-order statistical term it neglects over the
first-order σ it keeps, squared, with 'Nothing' for a term over a σ of
zero; and the operation. Statistical nudges propagate to first order
only, so this is measured, never carried as a nudge. A value keeps the
largest it was computed through, so the measure propagates; the
threshold over which it marks the value non-linear is the caller's
('Decide').
-}
data Skew = Skew {ratioSq :: Maybe Rational, operation :: Text}
  deriving stock (Eq, Show)

-- | The larger of two measures; 'Nothing' is unbounded.
worse :: Skew -> Skew -> Skew
worse a b = case (a.ratioSq, b.ratioSq) of
  (Nothing, _) -> a
  (_, Nothing) -> b
  (Just ra, Just rb) -> if rb > ra then b else a

-- | The measure of a value computed from several.
skews :: [Maybe Skew] -> Maybe Skew
skews ms = case catMaybes ms of
  [] -> Nothing
  s : rest -> Just (foldr worse s rest)

-- | The measure a magnitude carries.
skewOf :: Magnitude -> Maybe Skew
skewOf = \case
  Exact _ -> Nothing
  Affine _ _ _ sk -> sk

{- | The measure that marks a magnitude non-linear at a threshold: its
second-order statistical term exceeds that fraction of its first-order σ.
-}
nonLinearAt :: Rational -> Magnitude -> Maybe Skew
nonLinearAt threshold x = case skewOf x of
  Just sk
    | maybe True (> threshold * threshold) sk.ratioSq -> Just sk
  _ -> Nothing

{- | How a comparison or an integer rounding is decided (design §3.2.9): at
@sigma@ standard deviations, refusing a value whose statistical part is
non-linear beyond the threshold, a fraction of its σ.
-}
data Decide = Decide {sigma :: Int, nonlinear :: Rational}
  deriving stock (Eq, Show)

data ArithError
  = DivideByZero
  | -- | a function applied outside its domain, or an enclosure reaching outside it
    Domain Text
  | -- | a comparison or integer rounding the enclosure cannot settle (design §3.2.9)
    Undecided Text
  deriving stock (Eq, Show)

isExact :: Magnitude -> Bool
isExact = \case
  Exact _ -> True
  _ -> False

{- | An affine form with no nudges, no slack and no measure of
non-linearity is exact.
-}
affine ::
  Rational -> Map NudgeId (Rational, Nudge) -> Rational -> Maybe Skew -> Magnitude
affine m ts = affineNonZero m (Map.filter ((/= 0) . fst) ts)

{- | 'affine' over terms already free of zero coefficients, so that a sum
need not filter every term, which made a sum of n forms cost n².
-}
affineNonZero ::
  Rational -> Map NudgeId (Rational, Nudge) -> Rational -> Maybe Skew -> Magnitude
affineNonZero m ts s sk
  | Map.null ts && s == 0 && null sk = Exact m
  | otherwise = Affine m ts s sk

parts :: Magnitude -> (Rational, Map NudgeId (Rational, Nudge), Rational)
parts = \case
  Exact r -> (r, Map.empty, 0)
  Affine m ts s _ -> (m, ts, s)

midpoint :: Magnitude -> Rational
midpoint = \case
  Exact r -> r
  Affine m _ _ _ -> m

{- | The nudges with their coefficients, largest first; ties by origin, so the
budget reads the same every time.
-}
nudges :: Magnitude -> [(Rational, Nudge)]
nudges = \case
  Exact _ -> []
  Affine _ ts _ _ -> sortOn (\(c, n) -> (Down (abs c), n.origin)) (Map.elems ts)

-- | Largest magnitude first; ties keep their order.
sortOnAbs :: (a -> Rational) -> [a] -> [a]
sortOnAbs f = sortOn (Down . abs . f)

{- | The radius of the enclosure around the midpoint with every nudge counted
as a bound: a size, for scaling a rounding grid, never a limit.
-}
radius :: Magnitude -> Rational
radius = \case
  Exact _ -> 0
  Affine _ ts s _ -> s + sum (map (abs . fst) (Map.elems ts))

{- | The rigorous radius: the bound nudges and the slack. A statistical
nudge has no hard limit (design §3.2), so non-linear remainders and
domain checks are computed over this enclosure alone.
-}
boundRadius :: Magnitude -> Rational
boundRadius = \case
  Exact _ -> 0
  Affine _ ts s _ -> s + sum [abs c | (c, Nudge Bound _) <- Map.elems ts]

-- | The ends of the bound enclosure.
lo, hi :: Magnitude -> Rational
lo x = midpoint x - boundRadius x
hi x = midpoint x + boundRadius x

-- | The statistical coefficients, by nudge.
statTerms :: Map NudgeId (Rational, Nudge) -> Map NudgeId Rational
statTerms = Map.mapMaybe (\(c, n) -> if n.kind == Stat then Just c else Nothing)

-- | An upper bound on the first-order standard deviation, at @p@ digits.
statSigma :: Precision -> Magnitude -> Rational
statSigma p x = sigmaOf p (collapse x)

{- | The three numbers printing, comparison and the budget need (design
§3.2.9, §3.2.10): midpoint, rigorous bound radius, and the variance of
the statistical nudges.
-}
data Collapsed = Collapsed {mid :: Rational, bound :: Rational, variance :: Rational}
  deriving stock (Eq, Show)

collapse :: Magnitude -> Collapsed
collapse = \case
  Exact r -> Collapsed r 0 0
  Affine m ts s _ ->
    Collapsed
      m
      (s + sum [abs c | (c, Nudge Bound _) <- Map.elems ts])
      (sum [c * c | (c, Nudge Stat _) <- Map.elems ts])

-- | An upper bound on the standard deviation, @√variance@, at @p@ digits.
sigmaOf :: Precision -> Collapsed -> Rational
sigmaOf p c
  | c.variance == 0 = 0
  | otherwise = let (s, e) = sqrtApprox p c.variance in s + e

-- Exact while small -------------------------------------------------------------------

{- | The exact result of an operation on exact operands, @+@, @*@ or @/@
(design §3.2.8, exact while small): exact while it is short
('exactLength' within 'exactLimit'), and otherwise rounded to
'shortDigits' significant digits, the rounding a fresh bound nudge named
by the operation, its operands and the precision as any other
operation's is (design §3.2.4). The operands of a sum or a product are
named in order, so that @a + b@ and @b + a@ round to one unknown.
-}
exactResult :: Text -> Precision -> [Rational] -> Rational -> Magnitude
exactResult name p operands r
  | exactLength r <= exactLimit p = Exact r
  | otherwise =
      let r' = shorten p r
       in fresh name p (map Exact operands) r' (abs (r - r'))

{- | How long a rational is beyond its size, in bits: the shorter of its
numerator and denominator. A number's size is the @digits@ limit's
concern (design §8.1), so @2^100000@ and @1e-99999@ are short, and
@1/3@ is; a number with many digits both above and below its leading
one, @(1/3)^500 + 1@, is long. The cost of exact arithmetic is bounded by
the size and twice the length together.
-}
exactLength :: Rational -> Int
exactLength r = min (bits (abs (numerator r))) (bits (denominator r))
 where
  bits n = if n == 0 then 0 else fromIntegral (integerLog2 n) + 1

{- | The longest exact result kept exact, in bits: eight times
'shortDigits' decimal digits, 224 digits at the default precision
(design §3.2.8). Measured, the longest exact result of ordinary
arithmetic in the test suite and the tutorial is 122 digits at the
default precision (the products of a spinning chart's exact rotation),
which a finite difference then cancels; the limit is about twice that.
A product of eight values at working precision stays exact, and an
exact operation at the limit costs at most about sixty-four times one
at working precision, microseconds. An exact iteration that doubles its
length each step reaches the limit within @log₂ (8 (p + 4))@ steps of
its start and runs at working precision after.
-}
exactLimit :: Precision -> Int
exactLimit p = (8 * shortDigits p * 3322 + 999) `div` 1000

-- Linear operations ---------------------------------------------------------------

{- | A sum. Two exact operands give an exact result while it is short
('exactResult'); otherwise a sum is linear, collecting the nudges like
terms, and never rounds, which is what keeps @x - x@ exactly @0@.
-}
addM :: Precision -> Magnitude -> Magnitude -> Magnitude
addM p (Exact a) (Exact b) = exactResult "add" p (sort [a, b]) (a + b)
addM _ x y = addLinear x y

{- | A sum that never rounds, an exact one included: for a comparison,
which must see the exact difference.
-}
addLinear :: Magnitude -> Magnitude -> Magnitude
addLinear (Exact a) (Exact b) = Exact (a + b)
addLinear x y =
  let (m1, t1, s1) = parts x
      (m2, t2, s2) = parts y
      -- Only a nudge both share can cancel to zero.
      cancel _ a b = let (c, n) = addCoeff a b in if c == 0 then Nothing else Just (c, n)
   in affineNonZero
        (m1 + m2)
        ( Merge.merge
            Merge.preserveMissing
            Merge.preserveMissing
            (Merge.zipWithMaybeMatched cancel)
            t1
            t2
        )
        (s1 + s2)
        (skews [skewOf x, skewOf y])

addCoeff :: (Rational, Nudge) -> (Rational, Nudge) -> (Rational, Nudge)
addCoeff (c, n) (d, _) = let !s = c + d in (s, n)

-- | Negation, which never lengthens a rational.
negM :: Magnitude -> Magnitude
negM = scaleLinear (-1)

subM :: Precision -> Magnitude -> Magnitude -> Magnitude
subM p x y = addM p x (negM y)

-- | The exact difference, never rounded, for a comparison.
subLinear :: Magnitude -> Magnitude -> Magnitude
subLinear x y = addLinear x (negM y)

{- | Multiplication by an exact constant: an exact product while it is
short ('exactResult'), and on a form, linear and never rounded.
-}
scaleM :: Precision -> Rational -> Magnitude -> Magnitude
scaleM p k = \case
  Exact a -> exactResult "mul" p (sort [k, a]) (k * a)
  x -> scaleLinear k x

scaleLinear :: Rational -> Magnitude -> Magnitude
scaleLinear k = \case
  Exact a -> Exact (k * a)
  Affine m ts s sk
    | k == 0 -> Exact 0
    | otherwise -> affine (k * m) (Map.map (first (k *)) ts) (abs k * s) sk

{- | Absolute value: @x@ or @−x@ when the bound enclosure does not straddle
zero, otherwise that enclosure of @|x|@ as one fresh bound nudge and the
statistical part, whose sign is then unknown, as one fresh statistical
nudge. The kink is the non-linearity: within σ of the bound enclosure,
the statistical part is measured unbounded (design §3.2).
-}
absM :: Precision -> Magnitude -> Magnitude
absM p x = case x of
  Exact r -> Exact (abs r)
  _
    | lo x >= 0 -> kinked x
    | hi x <= 0 -> kinked (negM x)
    | otherwise ->
        let top = max (abs (lo x)) (hi x)
         in opResult
              "abs"
              p
              [x]
              (top / 2)
              sigma
              (skews [skewOf x, unbounded])
              (Exact (top / 2))
 where
  sigma = statSigma p x
  unbounded = if sigma > 0 then Just (Skew Nothing "abs") else Nothing
  kinked y
    | sigma > 0 && min (abs (lo x)) (abs (hi x)) <= sigma = markedBy unbounded y
    | otherwise = y

-- | A magnitude with a further measure of non-linearity.
markedBy :: Maybe Skew -> Magnitude -> Magnitude
markedBy sk x = case sk of
  Nothing -> x
  Just _ ->
    let (m, ts, s) = parts x
     in affine m ts s (skews [skewOf x, sk])

-- Nonlinear operations --------------------------------------------------------------

{- | Product. One exact side is a scaling; two affine sides linearise. The
quadratic leftover splits by kind (design §3.2): bound by bound is a
rigorous bound, as before; bound by statistical is a correction measured
with the bound part at its worst. That correction and statistical by
statistical terms are measured against the first-order σ, not carried
as independent random variables.
-}
mulM :: Precision -> Magnitude -> Magnitude -> Magnitude
mulM p (Exact a) y = scaleM p a y
mulM p x (Exact b) = scaleM p b x
mulM p x y =
  let (m1, t1, s1) = parts x
      (m2, t2, s2) = parts y
      linear =
        Map.unionWith
          addCoeff
          (Map.map (first (m2 *)) t1)
          (Map.map (first (m1 *)) t2)
      bound1 = Map.filter ((== Bound) . (.kind) . snd) t1
      bound2 = Map.filter ((== Bound) . (.kind) . snd) t2
      -- The bound leftover. A nudge both sides share contributes cᵢdᵢ·eᵢ²,
      -- which lies in [0, cᵢdᵢ] (or [cᵢdᵢ, 0]), so it is centred rather than
      -- taken as ±|cᵢdᵢ|; that is what makes x·x tight (design §3.2.2).
      -- Every other pair is bounded by the product of the bound radii.
      shared = Map.elems (Map.intersectionWith (\(c, _) (d, _) -> c * d) bound1 bound2)
      pos = sum (filter (> 0) shared)
      neg = sum (filter (< 0) shared)
      quadratic = (pos - neg) / 2 + (boundRadius x * boundRadius y - sum (map abs shared))
      cross = boundRadius x * statSigma p y + boundRadius y * statSigma p x
      -- The statistical leftover's standard deviation, for independent
      -- unit nudges: √((Σaᵢ²)(Σbᵢ²) + (Σaᵢbᵢ)²), measured over the
      -- first-order σ, squared so that it stays exact.
      a = statTerms t1
      b = statTerms t2
      ab = sum (Map.elems (Map.intersectionWith (*) a b))
      second = sumSq a * sumSq b + ab * ab
      first' = sumSq (statTerms linear)
      mid = m1 * m2 + (pos + neg) / 2
      measured
        | second == 0 || belowFloor p mid second = Nothing
        | first' == 0 = Just (Skew Nothing "mul")
        | otherwise = Just (Skew (Just (roundUpSig 3 (second / first'))) "mul")
      base = affine mid linear (abs m2 * s1 + abs m1 * s2) Nothing
   in opResult
        "mul"
        p
        [x, y]
        quadratic
        cross
        (skews [skewOf x, skewOf y, measured])
        base
 where
  sumSq = sum . map (\c -> c * c) . Map.elems

{- | The result of a non-linear operation (design §3.2): its linear part,
the bound remainder as a fresh bound nudge (the midpoint's rounding
joins it), and measures for discarded statistical corrections. A mixed
correction shares the original randomness and must not be added as an
independent statistical nudge. Its size relative to the retained sigma
is recorded, just like a discarded statistical quadratic term. The
linear part's coefficients are shortened first ('shortenLinear'): the
bound ones' rounding joins the fresh nudge, the statistical ones' the
measure.
-}
opResult ::
  Text ->
  Precision ->
  [Magnitude] ->
  Rational ->
  Rational ->
  Maybe Skew ->
  Magnitude ->
  Magnitude
opResult name p operands boundSize statSize sk base =
  finish
    p
    ( withFresh
        name
        p
        operands
        (boundSize + short.boundError)
        (markedBy (skews [sk, mixed]) short.value)
    )
 where
  short = shortenLinear p base
  statSize' = statSize + short.statError
  firstSigma = statSigma p short.value
  mixed
    | statSize' == 0 || belowFloor p (midpoint base) (statSize' * statSize') =
        Nothing
    | firstSigma == 0 = Just (Skew Nothing name)
    | otherwise =
        Just
          ( Skew
              (Just (roundUpSig 3 ((statSize' / firstSigma) ^ (2 :: Int))))
              (name <> ": uncertain statistical coefficient")
          )

{- | Whether a neglected second-order statistical term, given by its size
squared, is within the precision floor at the value's midpoint: the last
of @p@ significant digits there (design §3.2.8). Such a term is
arithmetic noise, and it never marks the value non-linear, however small
the first-order σ it would be compared with: one that cancelled to the
same noise. At a midpoint of zero there is no floor, so a value that is
second order alone stays marked.
-}
belowFloor :: Precision -> Rational -> Rational -> Bool
belowFloor p mid sizeSq = mid /= 0 && sizeSq <= floorSize * floorSize
 where
  floorSize = tolerance p mid

-- | Round up to @k@ significant digits: an upper bound stays one.
roundUpSig :: Int -> Rational -> Rational
roundUpSig k r = roundUpAt (precisionExponent k r) r

{- | The number of significant digits a non-linear operation keeps in the
rationals it produces (design §3.2.8): the working precision and four
guard digits.
-}
shortDigits :: Precision -> Int
shortDigits p = p + 4

-- | A rational to 'shortDigits' significant digits, rounded to nearest.
shorten :: Precision -> Rational -> Rational
shorten p r = roundAt (precisionExponent (shortDigits p) r) r

{- | An approximation with its value shortened ('shorten') and the rounding
added to its error bound.
-}
shortenApprox :: Precision -> Approx -> Approx
shortenApprox p (v, e) = let v' = shorten p v in (v', e + abs (v - v'))

{- | A form with its coefficients shortened ('shortenLinear'), and the total
rounding of its bound coefficients and of its statistical ones.
-}
data Shortened = Shortened
  { value :: Magnitude
  , boundError :: Rational
  , statError :: Rational
  }

{- | The linear part of a non-linear operation's result with every
coefficient shortened (design §3.2.8). Multiplying coefficients by slopes
and midpoints adds their digits, and an iteration feeds a value back
into several places that are added again, so without this a
coefficient's length multiplies with every step of the iteration.

A bound coefficient is rounded to a grid of 'shortDigits' significant
digits of the value's size (the larger of its midpoint and its radius),
and the slack rounded up onto it; their rounding joins the operation's
fresh nudge. A coefficient below the grid rounds to zero and its nudge
goes: an iteration that converges would otherwise keep every nudge it
ever made, each smaller and longer than the last. A statistical
coefficient is rounded to 'shortDigits' significant digits of its own,
so it never vanishes; its rounding is an error in the coefficient, which
is measured against the retained σ as a slope's error is, never made a
bound.
-}
shortenLinear :: Precision -> Magnitude -> Shortened
shortenLinear p = \case
  x@(Exact _) -> Shortened x 0 0
  x@(Affine m ts s sk) ->
    let e = precisionExponent (shortDigits p) (max (abs m) (radius x))
        grid = 10 ^^ e :: Rational
        short (c, n) = case n.kind of
          Bound -> (roundAt e c, n)
          Stat -> (shorten p c, n)
        ts' = Map.map short ts
        changes =
          Map.elems
            ( Map.intersectionWith
                (\(c, n) (c', _) -> (n.kind, abs (c - c')))
                ts
                ts'
            )
        errorOf k = sum [d | (k', d) <- changes, k' == k]
        s' = fromInteger (ceiling (s / grid)) * grid
     in Shortened (affine m ts' s' sk) (errorOf Bound) (errorOf Stat)

recipM :: Precision -> Magnitude -> Either ArithError Magnitude
recipM p x
  | Exact 0 <- x = Left DivideByZero
  | Exact r <- x = Right (Exact (recip r))
  | lo x <= 0 && hi x >= 0 = Left DivideByZero
  | otherwise =
      Right
        ( liftEndpoints
            "recip"
            p
            (\y -> y /= 0 && signum y == signum (midpoint x))
            (\y -> (recip y, 0))
            (\y -> (negate (recip (y * y)), 0))
            x
        )

divM :: Precision -> Magnitude -> Magnitude -> Either ArithError Magnitude
divM p (Exact a) (Exact b)
  | b == 0 = Left DivideByZero
  | otherwise = Right (exactResult "div" p [a, b] (a / b))
divM p x y
  -- A denominator that may be zero is refused before anything cancels, so
  -- x / x and 0 / x fail as 1 / x does when x's bound enclosure reaches
  -- zero. A statistical nudge is no limit (design §3.2): it makes the
  -- quotient non-linear instead.
  | lo y <= 0 && hi y >= 0 = Left DivideByZero
  -- A quotient of proportional forms is exact: the same named nudges are the
  -- same unknowns, so x / x = 1 and (90·u) / u = 90. Slack is anonymous:
  -- two equal radii are not one unknown, so a form with slack takes the
  -- general path.
  | Affine m _ 0 _ <- y
  , Nothing <- skewOf x
  , Nothing <- skewOf y
  , let k = midpoint x / m
  , x == scaleLinear k y =
      Right (Exact k)
  | otherwise = mulM p x <$> recipM p y

-- | Power with a literal integer exponent.
powM :: Precision -> Magnitude -> Integer -> Either ArithError Magnitude
powM p x n
  | n == 0 = Right (Exact 1)
  | n < 0 = recipM p x >>= \r -> powM p r (negate n)
  | otherwise = Right (go n)
 where
  go 1 = x
  go k
    | even k = let h = go (k `div` 2) in mulM p h h
    | otherwise = mulM p x (go (k - 1))

{- | Replace @x@ by the tangent line @f + slope·(x − mid)@: scale the nudges
by the slope. The caller adds the remainder.
-}
linearise :: Magnitude -> Rational -> Rational -> Magnitude
linearise x f slope = case x of
  Exact _ -> Exact f
  Affine _ ts s sk -> affine f (Map.map (first (slope *)) ts) (abs slope * s) sk

{- | Add a fresh bound nudge named after the operation, its operands and the
precision, so that identical computations share it (design §3.2.4). Its
size is rounded up to 'shortDigits' significant digits: a bound stays
one, and a remainder summed from long series errors stays short.
-}
withFresh ::
  Text -> Precision -> [Magnitude] -> Rational -> Magnitude -> Magnitude
withFresh name p operands size base =
  let (m, ts, s) = parts base
      -- The midpoint is rounded to p digits (design §3.2.8) and the rounding
      -- error joins this operation's nudge rather than the anonymous slack,
      -- so that two evaluations of the same operation still cancel exactly.
      -- A base with no nudges is shortened to p + 4 digits instead: a value
      -- the caller rounded already (π, an exact result, a function's value)
      -- is left as it is, and a product whose every linear coefficient fell
      -- below the grid ('shortenLinear') no longer keeps the full length of
      -- its midpoint, the product of its operands' (115 digits a step of
      -- the logistic map).
      m' =
        if Map.null ts && s == 0
          then shorten p m
          else roundAt (precisionExponent p m) m
      size' = roundUpSig (shortDigits p) (size + abs (m - m'))
   in if size' == 0
        then base
        else
          affine
            m'
            ( Map.insertWith
                addCoeff
                (builtinId Bound name p operands)
                (size', Nudge Bound (Builtin name))
                ts
            )
            s
            (skewOf base)

-- | A value known only as an enclosure @m ± size@ from one operation.
fresh :: Text -> Precision -> [Magnitude] -> Rational -> Rational -> Magnitude
fresh name p operands m size = withFresh name p operands size (Exact m)

{- | The identity of a builtin's remainder: a tagged, length-delimited
encoding of the whole operation (design §3.2.4), its name, the
precision, the operand count, and each operand by kind with every field
length-prefixed, so that no two different operations share bytes (the
operand lists @[1, 12]@ and @[1/11, 2]@ once ran together).
-}
builtinId :: NudgeKind -> Text -> Precision -> [Magnitude] -> NudgeId
builtinId k name p operands =
  nudgeId
    ( word8 3
        <> kindByte k
        <> text name
        <> sint (toInteger p)
        <> varint (toInteger (length operands))
        <> foldMap operand operands
    )
 where
  operand = \case
    Exact r -> word8 0 <> rational r
    Affine m ts s _ ->
      word8 1
        <> rational m
        <> varint (toInteger (Map.size ts))
        <> foldMap (\(i, (c, _)) -> idBytes i <> rational c) (Map.toList ts)
        <> rational s

kindByte :: NudgeKind -> Builder
kindByte = \case
  Bound -> word8 0
  Stat -> word8 1

-- | A nudge id from its encoding.
nudgeId :: Builder -> NudgeId
nudgeId = NudgeId . SHA256.hashlazy . toLazyByteString

rational :: Rational -> Builder
rational r = sint (numerator r) <> sint (denominator r)

idBytes :: NudgeId -> Builder
idBytes (NudgeId b) = varint (toInteger (BS.length b)) <> byteString b

tshow :: (Show a) => a -> Text
tshow = T.pack . show

{- | After a nonlinear step: fold the smallest bound nudges beyond the limit
into slack (design §3.2.7). Statistical nudges are kept: a σ must never
quietly become a bound.
-}
finish :: Precision -> Magnitude -> Magnitude
finish _ = \case
  Affine m ts s sk
    | Map.size ts > nudgeLimit ->
        let bounds = sortOnAbs snd [(i, c) | (i, (c, Nudge Bound _)) <- Map.toList ts]
            excess = drop (nudgeLimit `div` 2) bounds
            ts' = foldr (Map.delete . fst) ts excess
         in Affine m ts' (s + sum (map (abs . snd) excess)) sk
  x -> x

nudgeLimit :: Int
nudgeLimit = 64

{- | The decimal exponent of the leading digit: @decimalExponent 0.0123 = -2@.
Lifting approximations to magnitudes -------------------------------------------------
-}

{- | Apply a function to a magnitude given approximations of @f@ and @f'@
(design §3.2): linearise at the midpoint, which carries every nudge to
first order. The remainder over the bound enclosure and both
approximation errors become one fresh bound nudge. The parts that
involve a statistical nudge, the slope's change across the bound
enclosure and the slope's own error, each times σ, are measured against
the retained σ, never made independent nudges or bounds. The statistical
correction is measured, not carried: the largest change of @f'@ from
the midpoint to @m − σ@ or @m + σ@, relative to @|f'(m)|@, unbounded
when either point leaves the function's domain. The value and the slope
at the midpoint are shortened ('shortenApprox') before they are used,
their rounding joining their errors: a series summed in exact rationals
is far longer than its precision, and the slope multiplies every nudge.
-}
liftWith ::
  Text ->
  Precision ->
  (Rational -> Bool) ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  (Rational -> Rational -> Rational) ->
  Rational ->
  Magnitude ->
  Magnitude
liftWith name p inDomain f f' remainderOver spread x =
  let m = midpoint x
      r = boundRadius x
      sigma = statSigma p x
      (fm, fe) = shortenApprox p (f m)
      (fm', fe') = shortenApprox p (f' m)
      boundSize = fe + fe' * r + (if r == 0 then 0 else remainderOver fm fm')
      statSize = (fe' + spread) * sigma
      measured
        | sigma == 0 = Nothing
        | not (inDomain (m - sigma) && inDomain (m + sigma)) = Just (Skew Nothing name)
        | otherwise =
            let change = maximum [abs (fst (f' z) - fm') | z <- [m - sigma, m + sigma]]
             in if change == 0 || belowFloor p fm (change * change * sigma * sigma)
                  then Nothing
                  else
                    if fm' == 0
                      then Just (Skew Nothing name)
                      else Just (Skew (Just (roundUpSig 3 (change * change / (fm' * fm')))) name)
   in opResult
        name
        p
        [x]
        boundSize
        statSize
        (skews [skewOf x, measured])
        (linearise x fm fm')

{- | For a function that is convex or concave over the bound enclosure: the
tangent line's error is largest at an endpoint, so evaluate it there, and
so is the slope's change, which is monotone.
-}
liftEndpoints ::
  Text ->
  Precision ->
  (Rational -> Bool) ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  Magnitude ->
  Magnitude
liftEndpoints name p inDomain f f' x = liftWith name p inDomain f f' remainder spread x
 where
  m = midpoint x
  remainder fm fm' =
    maximum
      [ abs (fy - fm - fm' * (y - m)) + ey + snd (f m)
      | y <- [lo x, hi x]
      , let (fy, ey) = f y
      ]
  spread
    | boundRadius x == 0 = 0
    | otherwise =
        let (fm', em) = f' m
         in maximum [abs (fy' - fm') + ey' + em | y <- [lo x, hi x], let (fy', ey') = f' y]

{- | For a function with @|f''| ≤ b@ over the bound enclosure: Taylor's
remainder, and the slope changes by at most @b@ times the radius.
-}
liftBounded ::
  Text ->
  Precision ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  Rational ->
  Magnitude ->
  Magnitude
liftBounded name p f f' b x = markedBy (measured (midpoint lifted)) lifted
 where
  lifted =
    liftWith
      name
      p
      (const True)
      f
      f'
      (\_ _ -> b * boundRadius x * boundRadius x / 2)
      (b * boundRadius x)
      x
  sigma = statSigma p x
  slope = abs (fst (f' (midpoint x)))
  measured mid
    | sigma == 0 || b == 0 = Nothing
    | belowFloor p mid ((b * sigma * sigma) ^ (2 :: Int)) = Nothing
    | slope == 0 = Just (Skew Nothing name)
    | otherwise =
        Just (Skew (Just (roundUpSig 3 ((b * sigma / slope) ^ (2 :: Int)))) name)

-- | Square root. Exact for perfect squares of exact inputs.
sqrtM :: Precision -> Magnitude -> Either ArithError Magnitude
sqrtM p x
  | lo x < 0 = Left (Domain "sqrt of a value that may be negative")
  | Exact r <- x, Just q <- exactSqrt r = Right (Exact q)
  | lo x == 0 = Left (Domain "sqrt of an enclosure that reaches zero")
  | otherwise =
      Right
        ( liftEndpoints
            "sqrt"
            p
            (> 0)
            (sqrtApprox (p + 2))
            (\m -> let (s, e) = sqrtApprox (p + 4) m in (recip (2 * s), e / (2 * s * s)))
            x
        )
 where
  exactSqrt r =
    let n = numerator r
        d = denominator r
        sn = isqrt n
        sd = isqrt d
     in if sn * sn == n && sd * sd == d then Just (sn % sd) else Nothing

expM :: Precision -> Magnitude -> Magnitude
expM p = \case
  Exact 0 -> Exact 1
  x -> liftEndpoints "exp" p (const True) (expApprox (p + 2)) (expApprox (p + 2)) x

logM :: Precision -> Magnitude -> Either ArithError Magnitude
logM p x
  | lo x <= 0 = Left (Domain "log of a value that may be zero or negative")
  | Exact 1 <- x = Right (Exact 0)
  | otherwise =
      Right (liftEndpoints "log" p (> 0) (logApprox (p + 2)) (\m -> (recip m, 0)) x)

sinM :: Precision -> Magnitude -> Magnitude
sinM p = \case
  Exact 0 -> Exact 0
  x ->
    liftBounded
      "sin"
      p
      (fst . sinCosApprox (p + 2))
      (snd . sinCosApprox (p + 2))
      1
      x

cosM :: Precision -> Magnitude -> Magnitude
cosM p = \case
  Exact 0 -> Exact 1
  x ->
    liftBounded
      "cos"
      p
      (snd . sinCosApprox (p + 2))
      (scaleA (-1) . fst . sinCosApprox (p + 2))
      1
      x

tanM :: Precision -> Magnitude -> Either ArithError Magnitude
tanM p x = divM p (sinM p x) (cosM p x)

-- | @|atan''| = 2|y|/(1+y²)² ≤ 0.65@.
atanM :: Precision -> Magnitude -> Magnitude
atanM p = \case
  Exact 0 -> Exact 0
  x -> liftBounded "atan" p (atanApprox (p + 2)) (\m -> (recip (1 + m * m), 0)) 1 x

-- | @asin x = atan (x / √(1 − x²))@.
asinM :: Precision -> Magnitude -> Either ArithError Magnitude
asinM p x
  | lo x < -1 || hi x > 1 =
      Left (Domain "asin of a value that may lie outside [-1, 1]")
  | Exact 0 <- x = Right (Exact 0)
  | Exact 1 <- x = Right (scaleM p (1 % 2) (piM p))
  | Exact (-1) <- x = Right (scaleM p (-(1 % 2)) (piM p))
  | lo x <= -1 || hi x >= 1 =
      Left
        ( Domain
            "asin of an enclosure that reaches the edge of its domain, where the slope is infinite"
        )
  | otherwise = do
      inner <- sqrtM p (subM p (Exact 1) (mulM p x x))
      atanM p <$> divM p x inner

acosM :: Precision -> Magnitude -> Either ArithError Magnitude
acosM p x = subM p (scaleM p (1 % 2) (piM p)) <$> asinM p x

atan2M :: Precision -> Magnitude -> Magnitude -> Either ArithError Magnitude
atan2M p y x
  | Exact 0 <- x, Exact 0 <- y = Left (Domain "atan2 0 0")
  | lo x > 0 = atanM p <$> divM p y x
  | hi x < 0 && lo y >= 0 = (\a -> addM p a (piM p)) . atanM p <$> divM p y x
  | hi x < 0 && hi y < 0 = (\a -> subM p a (piM p)) . atanM p <$> divM p y x
  | lo y > 0 = subM p (scaleM p (1 % 2) (piM p)) . atanM p <$> divM p x y
  | hi y < 0 = subM p (scaleM p (-(1 % 2)) (piM p)) . atanM p <$> divM p x y
  | otherwise = Left (Domain "atan2 of an enclosure that contains the origin")

sinhM, coshM :: Precision -> Magnitude -> Magnitude
sinhM p = \case
  Exact 0 -> Exact 0
  x ->
    -- \|sinh''| = |sinh| ≤ cosh at the far end of the bound enclosure.
    let far = max (abs (lo x)) (abs (hi x))
        (c, ce) = coshApprox p far
        r = boundRadius x
     in liftWith
          "sinh"
          p
          (const True)
          (sinhApprox (p + 2))
          (coshApprox (p + 2))
          (\_ _ -> (c + ce) * r * r / 2)
          ((c + ce) * r)
          x
coshM p = \case
  Exact 0 -> Exact 1
  x ->
    liftEndpoints "cosh" p (const True) (coshApprox (p + 2)) (sinhApprox (p + 2)) x

tanhM :: Precision -> Magnitude -> Either ArithError Magnitude
tanhM p x = divM p (sinhM p x) (coshM p x)

-- | π at the working precision.
piM :: Precision -> Magnitude
piM p =
  let (v, e) = piApprox p
      v' = roundAt (negate p) v
   in fresh "pi" p [] v' (e + abs (v - v'))

-- Rodrigues' coefficients ---------------------------------------------------------------

{- | @sin θ / θ@ and @(1 − cos θ) / θ²@ as functions of the squared angle
@t = θ²@: the coefficients of Rodrigues' formula (design §3.3, @expm@).
Both are entire in @t@, the series @Σ (−t)ᵏ/(2k+1)!@ and
@Σ (−t)ᵏ/(2k+2)!@, so an enclosure of @t@ that reaches zero, or dips
below it, is harmless: nothing takes the root of @t@ or divides by the
angle. Near zero (@t@'s enclosure reaching below 1) the series is summed
on the enclosure ('rodriguesSeries'); away from it, by @sqrt@, @sin@ and
@cos@ and a division by an enclosure that excludes zero.
-}
sincSqM, coscSqM :: Precision -> Magnitude -> Either ArithError Magnitude
sincSqM p t
  | Exact 0 <- t = Right (Exact 1)
  | lo t >= 1 = do
      theta <- sqrtM p t
      divM p (sinM p theta) theta
  | otherwise = Right (rodriguesSeries "sinc" p 1 t)
coscSqM p t
  | Exact 0 <- t = Right (Exact (1 % 2))
  | lo t >= 1 = do
      theta <- sqrtM p t
      divM p (subM p (Exact 1) (cosM p theta)) t
  | otherwise = Right (rodriguesSeries "cosc" p 2 t)

{- | @Σₖ (−t)ᵏ / (2k + j)!@ on an enclosure of @t@, by Horner's rule in
affine arithmetic up to the first term @K@ that is below the tolerance
at @T = max |t|@ over the enclosure and from which the terms at least
halve (@2T ≤ (2K+j+1)(2K+j+2)@, the ratio of one term to the last being
@T / ((2k+j+1)(2k+j+2))@). The tail is then at most twice that term
for every @t@ in the enclosure, and it is one fresh nudge.
-}
rodriguesSeries :: Text -> Precision -> Integer -> Magnitude -> Magnitude
rodriguesSeries name p j t =
  let big = max (abs (lo t)) (abs (hi t))
      coeff k = (if even k then 1 else -1) % product [1 .. 2 * k + j]
      size k = abs (coeff k) * big ^ k
      stops k =
        size k < tolerance (p + 4) 1
          && 2 * big <= fromInteger ((2 * k + j + 1) * (2 * k + j + 2))
      top = case filter stops [0 ..] of
        k : _ -> k
        [] -> 0
      poly =
        foldr
          (\k acc -> addM p (Exact (coeff k)) (mulM p t acc))
          (Exact 0)
          [0 .. top - 1]
   in enclose name p [t] (2 * size top) poly

{- | Add one fresh bound nudge of the given size to a value, named after
the operation, its operands and the precision (design §3.2.4), and
compact. For a remainder bounded outside this module, such as a matrix
series' (@expm@): the operands must tell apart every value that is to
get an unknown of its own, so two entries of one matrix pass their
positions.
-}
enclose ::
  Text -> Precision -> [Magnitude] -> Rational -> Magnitude -> Magnitude
enclose name p operands size base = finish p (withFresh name p operands size base)

-- Rounding to integers --------------------------------------------------------------------

{- | Integer rounding is exact on exact inputs and on enclosures that do not
straddle a rounding boundary; otherwise it cannot be decided. It is a
comparison with the boundaries, so it is decided as one is (design
§3.2.9): the bound radius plus @k@ standard deviations, and never for a
value marked non-linear.
-}
floorM
  , ceilM
  , roundM ::
    Decide -> Precision -> Magnitude -> Either ArithError Magnitude
floorM = roundingWith "floor" (fromInteger . floor)
ceilM = roundingWith "ceil" (fromInteger . ceiling)
roundM = roundingWith "round" (fromInteger . round)

roundingWith ::
  Text ->
  (Rational -> Rational) ->
  Decide ->
  Precision ->
  Magnitude ->
  Either ArithError Magnitude
roundingWith name f decide p x
  | Just sk <- nonLinearAt decide.nonlinear x =
      Left (Undecided (name <> " of a value " <> markedText sk))
  | f low == f high = Right (Exact (f low))
  | otherwise =
      Left (Undecided (name <> " of an enclosure that straddles a rounding boundary"))
 where
  c = collapse x
  w = c.bound + fromIntegral decide.sigma * sigmaOf p c
  low = c.mid - w
  high = c.mid + w

-- | How a refusal names a mark: the operation that set it.
markedText :: Skew -> Text
markedText sk =
  "marked non-linear by "
    <> sk.operation
    <> ": a mean and a σ do not describe it (design §3.2)"

-- Comparison -------------------------------------------------------------------------------

{- | Design §3.2.9: @a < b@ is decided when @|mid (a − b)| > bound + k·σ@,
and never when the difference is marked non-linear. A zero linear model
does not prove equality when any statistical remainder was discarded,
even below the warning threshold.
-}
compareM ::
  Decide -> Precision -> Magnitude -> Magnitude -> Either ArithError Ordering
compareM decide p a b =
  let d = subLinear a b
      c = collapse d
      k = decide.sigma
      sigma = sigmaOf p c
      approx r = tshow (fromRational r :: Double)
      zeroModel = c.mid == 0 && c.bound == 0 && c.variance == 0
      marked = if zeroModel then skewOf d else nonLinearAt decide.nonlinear d
   in if zeroModel && null (skewOf d)
        then Right EQ
        else case marked of
          Just sk ->
            Left
              ( Undecided
                  ("comparison at sigma " <> tshow k <> ": the difference is " <> markedText sk)
              )
          Nothing
            | abs c.mid > c.bound + fromIntegral k * sigma -> Right (compare c.mid 0)
            | otherwise ->
                Left
                  ( Undecided
                      ( "comparison at sigma "
                          <> tshow k
                          <> ": the difference is "
                          <> approx c.mid
                          <> " ± "
                          <> approx c.bound
                          <> (if c.variance > 0 then " ±σ " <> approx sigma else "")
                      )
                  )

{- | Equality: true if the difference is exactly zero after cancellation,
false if decided non-zero, undecided otherwise.
-}
equalM ::
  Decide -> Precision -> Magnitude -> Magnitude -> Either ArithError Bool
equalM decide p a b = (== EQ) <$> compareM decide p a b

-- Declared uncertainty --------------------------------------------------------------------

{- | @x ± e@ / @x ±σ e@ (design §3.2.5). The nudge's identity is its origin
and the midpoint; its size is the error's midpoint, and any bound radius
the error itself carries goes to slack. The error's own statistical part
is second order (a σ of a σ) and, like any, never becomes a bound.
-}
uncertain :: NudgeKind -> Origin -> Magnitude -> Magnitude -> Magnitude
uncertain k origin x e =
  let (m, ts, s) = parts x
      size = abs (midpoint e)
   in affine
        m
        (Map.insertWith addCoeff (originId k origin m) (size, Nudge k origin) ts)
        (s + boundRadius e)
        (skews [skewOf x, skewOf e])

-- | One component of @noise n@ / @gauss n@: a unit nudge.
unitNoise :: NudgeKind -> Origin -> Magnitude
unitNoise k origin =
  affine 0 (Map.singleton (originId k origin 0) (1, Nudge k origin)) 0 Nothing

{- | Design §3.2.4: an unlabelled nudge is named by its definition, path,
component and midpoint, so  2@ and  3@ from  f x = x ± 0.01@ are
independent while two evaluations of  2@ share. A tag names the unknown
itself, nothing else:  ± r #s7@ is  + r·e_s7@ whatever @ and @ are,
which is how a systematic error shared by several readings is written.
-}
originId :: NudgeKind -> Origin -> Rational -> NudgeId
originId k origin m = nudgeId $ case origin of
  Declared (Hash h) path i ->
    word8 0
      <> kindTag
      <> idBytes (NudgeId h)
      <> varint (toInteger (length path))
      <> foldMap (sint . toInteger) path
      <> sint (toInteger i)
      <> rational m
  Tagged l i -> word8 1 <> kindTag <> text l <> sint (toInteger i)
  Builtin name -> word8 2 <> kindTag <> text name
 where
  kindTag = kindByte k

{- | The coefficients of the statistical nudges: one column of the
square-root factor of the covariance (design §3.5).
-}
statCoefficients :: Magnitude -> Map NudgeId Rational
statCoefficients = \case
  Exact _ -> Map.empty
  Affine _ ts _ _ -> statTerms ts

{- | The cross-covariance of two lists of magnitudes over their shared
statistical nudges (design §3.5): entry @(i, j)@ is
@Σ_k coeff(aᵢ, k) · coeff(bⱼ, k)@, exact. With @a = b@ it is the covariance
@Σ cᵢcᵢᵀ@ of one vector.
-}
crossCovarianceRows :: [Magnitude] -> [Magnitude] -> [[Rational]]
crossCovarianceRows as bs =
  [ [sum (Map.elems (Map.intersectionWith (*) ca cb)) | cb <- colsB]
  | ca <- map statCoefficients as
  ]
 where
  colsB = map statCoefficients bs
