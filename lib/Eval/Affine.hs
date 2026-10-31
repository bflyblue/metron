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
module Eval.Affine (
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
  tidyM,
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

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (Builder, byteString, toLazyByteString, word8)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Ord (Down (..))
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core (Hash (..), NudgeKind (..))
import Eval.Encode (sint, text, varint)
import GHC.Num (integerLog2)

-- Types -----------------------------------------------------------------------------

-- | Working precision in digits.
type Precision = Int

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
  = Exact Rational
  | Affine
      { mid :: Rational
      , terms :: Map NudgeId (Rational, Nudge)
      , slack :: Rational
      -- ^ anonymous worst-case radius: rounding and compaction leftovers
      , skew :: Maybe Skew
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
affine m ts s sk
  | Map.null ts' && s == 0 && null sk = Exact m
  | otherwise = Affine m ts' s sk
 where
  ts' = Map.filter ((/= 0) . fst) ts

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

sortOnAbs :: (a -> Rational) -> [a] -> [a]
sortOnAbs f = foldr ins []
 where
  ins x [] = [x]
  ins x (y : ys)
    | abs (f x) >= abs (f y) = x : y : ys
    | otherwise = y : ins x ys

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

-- Linear operations ---------------------------------------------------------------

addM :: Magnitude -> Magnitude -> Magnitude
addM (Exact a) (Exact b) = Exact (a + b)
addM x y =
  let (m1, t1, s1) = parts x
      (m2, t2, s2) = parts y
   in affine
        (m1 + m2)
        (Map.unionWith addCoeff t1 t2)
        (s1 + s2)
        (skews [skewOf x, skewOf y])

addCoeff :: (Rational, Nudge) -> (Rational, Nudge) -> (Rational, Nudge)
addCoeff (c, n) (d, _) = (c + d, n)

negM :: Magnitude -> Magnitude
negM = scaleM (-1)

subM :: Magnitude -> Magnitude -> Magnitude
subM x y = addM x (negM y)

-- | Multiplication by an exact constant.
scaleM :: Rational -> Magnitude -> Magnitude
scaleM k = \case
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
rigorous bound, as before; bound by statistical is statistical, the
bound part at its worst, a fresh statistical nudge; statistical by
statistical is second order, measured against the first-order σ and not
carried.
-}
mulM :: Precision -> Magnitude -> Magnitude -> Magnitude
mulM _ (Exact a) y = scaleM a y
mulM _ x (Exact b) = scaleM b x
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
      measured
        | second == 0 = Nothing
        | first' == 0 = Just (Skew Nothing "mul")
        | otherwise = Just (Skew (Just (roundUpSig 3 (second / first'))) "mul")
      base = affine (m1 * m2 + (pos + neg) / 2) linear (abs m2 * s1 + abs m1 * s2) Nothing
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
joins it), the statistical remainder as a fresh statistical nudge, and
the measure of non-linearity it carries, compacted.
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
    ( withFreshOf
        Stat
        name
        p
        operands
        statSize
        (withFresh name p operands boundSize (markedBy sk base))
    )

-- | Round up to @k@ significant digits: an upper bound stays one.
roundUpSig :: Int -> Rational -> Rational
roundUpSig k r = roundUpAt (precisionExponent k r) r

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
divM _ (Exact a) (Exact b)
  | b == 0 = Left DivideByZero
  | otherwise = Right (Exact (a / b))
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
  , let k = midpoint x / m
  , x == scaleM k y =
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
precision, so that identical computations share it (design §3.2.4).
-}
withFresh ::
  Text -> Precision -> [Magnitude] -> Rational -> Magnitude -> Magnitude
withFresh name p operands size base =
  let (m, ts, s) = parts base
      -- The midpoint is rounded to p digits (design §3.2.8) and the rounding
      -- error joins this operation's nudge rather than the anonymous slack,
      -- so that two evaluations of the same operation still cancel exactly.
      m' = if Map.null ts && s == 0 then m else roundAt (precisionExponent p m) m
      size' = size + abs (m - m')
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

{- | Add a fresh nudge of a kind, named after the operation, its operands
and the precision. A statistical one is a remainder that involves a
statistical nudge (design §3.2), which a bound must never hold.
-}
withFreshOf ::
  NudgeKind ->
  Text ->
  Precision ->
  [Magnitude] ->
  Rational ->
  Magnitude ->
  Magnitude
withFreshOf k name p operands size base
  | k == Bound = withFresh name p operands size base
  | size == 0 = base
  | otherwise =
      let (m, ts, s) = parts base
       in affine
            m
            ( Map.insertWith
                addCoeff
                (builtinId Stat name p operands)
                (size, Nudge Stat (Builtin name))
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

-- | The decimal exponent of the leading digit: @decimalExponent 0.0123 = -2@.
decimalExponent :: Rational -> Int
decimalExponent r
  | r == 0 = 0
  | a >= 1 = length (takeWhile (<= a) (iterate (* 10) 1)) - 1
  | otherwise = negate (length (takeWhile (> a) (iterate (/ 10) 1)))
 where
  a = abs r

{- | The exponent of the last of @p@ significant digits of a value:
@precisionExponent 3 123.4 = 0@, @precisionExponent 3 0.01234 = -4@.
-}
precisionExponent :: Precision -> Rational -> Int
precisionExponent p r = decimalExponent r - p + 1

-- | Round to a multiple of @10^e@.
roundAt :: Int -> Rational -> Rational
roundAt e r
  | e >= 0 = fromInteger (round (r / unit) * (10 ^ e))
  | otherwise = round (r * recip unit) % (10 ^ negate e)
 where
  unit = 10 ^^ e :: Rational

-- | Round up to a multiple of @10^e@: an upper bound stays one.
roundUpAt :: Int -> Rational -> Rational
roundUpAt e r = fromInteger (ceiling (r / unit)) * unit
 where
  unit = 10 ^^ e :: Rational

-- Rigorous elementary functions on rationals -------------------------------------------
--
-- Each returns an approximation and a bound on its absolute error, good to
-- @p@ digits in the sense of the module header.

type Approx = (Rational, Rational)

-- | The absolute error allowed at @p@ digits for a result of size @v@.
tolerance :: Precision -> Rational -> Rational
tolerance p v = 10 ^^ precisionExponent p v

-- | Floor of the square root of a non-negative integer.
isqrt :: Integer -> Integer
isqrt 0 = 0
-- Newton's method from a power of two above the root: starting from n
-- itself took one step per halving, thousands of big divisions for the
-- long rationals an uncertain value's endpoints become.
isqrt n = go (2 ^ (integerLog2 n `div` 2 + 1))
 where
  go x =
    let y = (x + n `div` x) `div` 2
     in if y >= x then x else go y

{- | @√r@ for @r ≥ 0@, from below, with its error. The error is at most
@1/(d·10^p)@ and relative to the result at most @10^-p@.
-}
sqrtApprox :: Precision -> Rational -> Approx
sqrtApprox p r
  | r == 0 = (0, 0)
  | otherwise =
      let d = denominator r
          n = numerator r
          s = 10 ^ p :: Integer
       in (isqrt (n * d * s * s) % (d * s), 1 % (d * s))

{- | Sum a series whose terms shrink by at least half from one to the next
once below the target, until a term drops below it; the remainder is
bounded by twice the first omitted term.
-}
sumSeries :: Rational -> [Rational] -> Approx
sumSeries target = go 0
 where
  go acc (t : rest)
    | abs t < target = (acc, 2 * abs t)
    | otherwise = go (acc + t) rest
  go acc [] = (acc, 0)

scaleA :: Rational -> Approx -> Approx
scaleA k (v, e) = (k * v, abs k * e)

addA :: Approx -> Approx -> Approx
addA (a, e) (b, f) = (a + b, e + f)

{- | @e^x@. Halve the argument until it is small, sum the series, square back.
Squaring doubles the relative error each time, so the series is summed
with two guard digits per halving.
-}
expApprox :: Precision -> Rational -> Approx
expApprox p x
  | x == 0 = (1, 0)
  | otherwise =
      let k = length (takeWhile (> 1 % 4) (iterate (/ 2) (abs x)))
          q = p + 2 * k + 4
          r = x / (2 ^ k)
          terms = scanl (\t n -> t * r / fromInteger n) 1 [1 :: Integer ..]
          -- The square is rounded at its own last digit, and its error
          -- bound rounded up there: rounded at the last digit of the value
          -- squared, a small result lost every digit (e^-200 came out as
          -- 0), and only a working precision of hundreds of digits found
          -- it, which took seconds for e^-10000.
          square (s, e) =
            let ss = s * s
                at = precisionExponent q ss
                s' = roundAt at ss
             in (s', roundUpAt at (2 * abs s * e + e * e + abs (ss - s')))
       in iterate square (sumSeries (tolerance q 1) terms) !! k

-- | @atanh z@ for @|z| < 1@, relative to its size.
atanhApprox :: Precision -> Rational -> Approx
atanhApprox p z
  | z == 0 = (0, 0)
  | otherwise =
      let terms = [z ^ (2 * n + 1) / fromInteger (2 * n + 1) | n <- [0 :: Integer ..]]
          (s, e) = sumSeries (tolerance (p + 4) z) terms
       in (s, e / (1 - z * z))

ln2Approx :: Precision -> Approx
ln2Approx p = scaleA 2 (atanhApprox p (1 % 3))

-- | @ln x@ for @x > 0@: reduce by powers of two, then @2·atanh((y−1)/(y+1))@.
logApprox :: Precision -> Rational -> Approx
logApprox p x
  | x == 1 = (0, 0)
  | otherwise =
      let (k, y) = reduce (0 :: Integer) x
          z = (y - 1) / (y + 1)
       in addA (scaleA (fromInteger k) (ln2Approx (p + 4))) (scaleA 2 (atanhApprox p z))
 where
  reduce k y
    | y >= 2 = reduce (k + 1) (y / 2)
    | y < 1 = reduce (k - 1) (y * 2)
    | otherwise = (k, y)

-- | @π@ by Machin's formula.
piApprox :: Precision -> Approx
piApprox p =
  addA
    (scaleA 16 (atanSmall (p + 4) (1 % 5)))
    (scaleA (-4) (atanSmall (p + 4) (1 % 239)))

-- | @atan x@ for @|x| ≤ 1/4@ by the alternating series, relative to its size.
atanSmall :: Precision -> Rational -> Approx
atanSmall p x
  | x == 0 = (0, 0)
  | otherwise =
      sumSeries
        (tolerance (p + 2) x)
        [ (if even n then 1 else -1) * x ^ (2 * n + 1) / fromInteger (2 * n + 1)
        | n <- [0 :: Integer ..]
        ]

-- | @atan x@ for any @x@.
atanApprox :: Precision -> Rational -> Approx
atanApprox p x
  | x < 0 = scaleA (-1) (atanApprox p (negate x))
  | x > 1 =
      addA
        (scaleA (1 % 2) (piApprox (p + 2)))
        (scaleA (-1) (atanApprox (p + 2) (recip x)))
  | x > 1 % 4 =
      -- atan x = 2·atan (x / (1 + √(1 + x²))); the map y ↦ x/(1+y) has slope
      -- of size at most one on this range, so the root's error passes through.
      let (sq, se) = sqrtApprox (p + 6) (1 + x * x)
          (a, ae) = atanApprox (p + 2) (x / (1 + sq))
       in (2 * a, 2 * (ae + se))
  | otherwise = atanSmall p x

{- | @sin x@ and @cos x@: reduce modulo @2π@, then Taylor series. The sine is
summed relative to the reduced argument's size, so tiny angles keep their
digits.
-}
sinCosApprox :: Precision -> Rational -> (Approx, Approx)
sinCosApprox p x =
  let (piV, piE) = piApprox (p + 8)
      k = round (x / (2 * piV)) :: Integer
      r = x - 2 * fromInteger k * piV
      reductionErr = 2 * abs (fromInteger k) * piE
      sinTerms =
        scanl
          (\t n -> negate t * r * r / fromInteger ((2 * n) * (2 * n + 1)))
          r
          [1 :: Integer ..]
      cosTerms =
        scanl
          (\t n -> negate t * r * r / fromInteger ((2 * n - 1) * (2 * n)))
          1
          [1 :: Integer ..]
      (s, se) =
        if r == 0
          then (0, 0)
          else sumSeries (tolerance (p + 6) (min 1 (abs r))) sinTerms
      (c, ce) = sumSeries (tolerance (p + 6) 1) cosTerms
   in ((s, se + reductionErr), (c, ce + reductionErr))

{- | @sinh x@ by its series for @|x| ≤ 1@ (the exponential difference would
cancel), and by exponentials beyond.
-}
sinhApprox :: Precision -> Rational -> Approx
sinhApprox p x
  | x == 0 = (0, 0)
  | abs x <= 1 =
      sumSeries
        (tolerance (p + 2) x)
        ( scanl
            (\t n -> t * x * x / fromInteger ((2 * n) * (2 * n + 1)))
            x
            [1 :: Integer ..]
        )
  | otherwise =
      scaleA
        (1 % 2)
        (addA (expApprox (p + 2) x) (scaleA (-1) (expApprox (p + 2) (negate x))))

coshApprox :: Precision -> Rational -> Approx
coshApprox p x = scaleA (1 % 2) (addA (expApprox (p + 2) x) (expApprox (p + 2) (negate x)))

-- Lifting approximations to magnitudes -------------------------------------------------

{- | Apply a function to a magnitude given approximations of @f@ and @f'@
(design §3.2): linearise at the midpoint, which carries every nudge to
first order. The remainder over the bound enclosure and both
approximation errors become one fresh bound nudge. The parts that
involve a statistical nudge, the slope's change across the bound
enclosure and the slope's own error, each times σ, become one fresh
statistical nudge, never a bound. The second-order statistical term is
measured, not carried: @|f''(m)|·σ²@ against the first-order @|f'(m)|·σ@,
with @f''(m)·σ@ read as the change of @f'@ from @m − σ@ to @m + σ@,
halved, and unbounded when either point leaves the function's domain.
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
      (fm, fe) = f m
      (fm', fe') = f' m
      boundSize = fe + fe' * r + (if r == 0 then 0 else remainderOver fm fm')
      statSize = (fe' + spread) * sigma
      measured
        | sigma == 0 = Nothing
        | not (inDomain (m - sigma) && inDomain (m + sigma)) = Just (Skew Nothing name)
        | otherwise =
            let change = abs (fst (f' (m + sigma)) - fst (f' (m - sigma))) / 2
             in if change == 0
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
liftBounded name p f f' b x =
  liftWith
    name
    p
    (const True)
    f
    f'
    (\_ _ -> b * boundRadius x * boundRadius x / 2)
    (b * boundRadius x)
    x

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
  | Exact 1 <- x = Right (scaleM (1 % 2) (piM p))
  | Exact (-1) <- x = Right (scaleM (-(1 % 2)) (piM p))
  | lo x <= -1 || hi x >= 1 =
      Left
        ( Domain
            "asin of an enclosure that reaches the edge of its domain, where the slope is infinite"
        )
  | otherwise = do
      inner <- sqrtM p (subM (Exact 1) (mulM p x x))
      atanM p <$> divM p x inner

acosM :: Precision -> Magnitude -> Either ArithError Magnitude
acosM p x = subM (scaleM (1 % 2) (piM p)) <$> asinM p x

atan2M :: Precision -> Magnitude -> Magnitude -> Either ArithError Magnitude
atan2M p y x
  | Exact 0 <- x, Exact 0 <- y = Left (Domain "atan2 0 0")
  | lo x > 0 = atanM p <$> divM p y x
  | hi x < 0 && lo y >= 0 = (`addM` piM p) . atanM p <$> divM p y x
  | hi x < 0 && hi y < 0 = (`subM` piM p) . atanM p <$> divM p y x
  | lo y > 0 = subM (scaleM (1 % 2) (piM p)) . atanM p <$> divM p x y
  | hi y < 0 = subM (scaleM (-(1 % 2)) (piM p)) . atanM p <$> divM p x y
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
      divM p (subM (Exact 1) (cosM p theta)) t
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
        foldr (\k acc -> addM (Exact (coeff k)) (mulM p t acc)) (Exact 0) [0 .. top - 1]
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

{- | Round the bound coefficients and the slack of an affine form to
@p + 4@ significant digits of its size, the error joining one fresh
nudge, as a midpoint's rounding does (design §3.2.7, §3.2.8). 'mulM'
rounds the midpoint it forms but not the coefficients it multiplies, so
a long chain of products, a matrix series, would otherwise carry
coefficients whose digits grow with every step. Statistical coefficients
are kept as they are: their error would not be a bound.
-}
tidyM :: Precision -> Magnitude -> Magnitude
tidyM p x = case x of
  Exact _ -> x
  Affine m ts s sk ->
    let e = precisionExponent (p + 4) (max (abs m) (radius x))
        grid = 10 ^^ e :: Rational
        roundBound (c, nd)
          | nd.kind == Bound = (roundAt e c, nd)
          | otherwise = (c, nd)
        ts' = Map.map roundBound ts
        s' = fromInteger (ceiling (s / grid)) * grid
        err =
          sum (zipWith (\(c, _) (c', _) -> abs (c - c')) (Map.elems ts) (Map.elems ts'))
     in finish p (withFresh "round" p [x] err (affine m ts' s' sk))

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
and never when the difference is marked non-linear, since a mean and a σ
do not describe a skewed result; a difference exactly zero is equal
whatever it went through.
-}
compareM ::
  Decide -> Precision -> Magnitude -> Magnitude -> Either ArithError Ordering
compareM decide p a b =
  let d = subM a b
      c = collapse d
      k = decide.sigma
      sigma = sigmaOf p c
      approx r = tshow (fromRational r :: Double)
   in if c.mid == 0 && c.bound == 0 && c.variance == 0
        then Right EQ
        else case nonLinearAt decide.nonlinear d of
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
