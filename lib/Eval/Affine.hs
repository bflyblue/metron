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
  NudgeId (..),
  Origin (..),
  Nudge (..),
  Precision,
  isExact,
  midpoint,
  radius,
  nudges,

  -- * Collapse
  Collapsed (..),
  collapse,
  sigmaOf,
  statCoefficients,

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
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Ord (Down (..))
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Eval.Core (Hash (..), NudgeKind (..))

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
      }
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

-- | An affine form with no nudges and no slack is exact.
affine :: Rational -> Map NudgeId (Rational, Nudge) -> Rational -> Magnitude
affine m ts s
  | Map.null ts' && s == 0 = Exact m
  | otherwise = Affine m ts' s
 where
  ts' = Map.filter ((/= 0) . fst) ts

parts :: Magnitude -> (Rational, Map NudgeId (Rational, Nudge), Rational)
parts = \case
  Exact r -> (r, Map.empty, 0)
  Affine m ts s -> (m, ts, s)

midpoint :: Magnitude -> Rational
midpoint = \case
  Exact r -> r
  Affine m _ _ -> m

{- | The nudges with their coefficients, largest first; ties by origin, so the
budget reads the same every time.
-}
nudges :: Magnitude -> [(Rational, Nudge)]
nudges = \case
  Exact _ -> []
  Affine _ ts _ -> sortOn (\(c, n) -> (Down (abs c), n.origin)) (Map.elems ts)

sortOnAbs :: (a -> Rational) -> [a] -> [a]
sortOnAbs f = foldr ins []
 where
  ins x [] = [x]
  ins x (y : ys)
    | abs (f x) >= abs (f y) = x : y : ys
    | otherwise = y : ins x ys

{- | The radius of the enclosure around the midpoint with every nudge counted
as a bound: what nonlinear remainders are computed from.
-}
radius :: Magnitude -> Rational
radius = \case
  Exact _ -> 0
  Affine _ ts s -> s + sum (map (abs . fst) (Map.elems ts))

lo, hi :: Magnitude -> Rational
lo x = midpoint x - radius x
hi x = midpoint x + radius x

{- | The three numbers printing, comparison and the budget need (design
§3.2.9, §3.2.10): midpoint, rigorous bound radius, and the variance of
the statistical nudges.
-}
data Collapsed = Collapsed {mid :: Rational, bound :: Rational, variance :: Rational}
  deriving stock (Eq, Show)

collapse :: Magnitude -> Collapsed
collapse = \case
  Exact r -> Collapsed r 0 0
  Affine m ts s ->
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
   in affine (m1 + m2) (Map.unionWith addCoeff t1 t2) (s1 + s2)

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
  Affine m ts s -> affine (k * m) (Map.map (first (k *)) ts) (abs k * s)

{- | Absolute value: exact when the enclosure does not straddle zero,
otherwise the enclosure of @|x|@ with one fresh nudge.
-}
absM :: Precision -> Magnitude -> Magnitude
absM p x = case x of
  Exact r -> Exact (abs r)
  _
    | lo x >= 0 -> x
    | hi x <= 0 -> negM x
    | otherwise ->
        let top = max (abs (lo x)) (hi x)
         in fresh "abs" p [x] (top / 2) (top / 2)

-- Nonlinear operations --------------------------------------------------------------

{- | Product. One exact side is a scaling; two affine sides linearise, with
the quadratic leftover bounded by the product of the radii.
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
      -- The quadratic leftover. A nudge both sides share contributes
      -- cᵢdᵢ·eᵢ², which lies in [0, cᵢdᵢ] (or [cᵢdᵢ, 0]), so it is centred
      -- rather than taken as ±|cᵢdᵢ|; that is what makes x·x tight (design
      -- §3.2.2). Every other pair is bounded by the product of the radii.
      shared = Map.elems (Map.intersectionWith (\(c, _) (d, _) -> c * d) t1 t2)
      pos = sum (filter (> 0) shared)
      neg = sum (filter (< 0) shared)
      quadratic = (pos - neg) / 2 + (radius x * radius y - sum (map abs shared))
      base = affine (m1 * m2 + (pos + neg) / 2) linear (abs m2 * s1 + abs m1 * s2)
   in finish p (withFresh "mul" p [x, y] quadratic base)

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
            (\y -> (recip y, 0))
            (\y -> (negate (recip (y * y)), 0))
            x
        )

divM :: Precision -> Magnitude -> Magnitude -> Either ArithError Magnitude
divM _ (Exact a) (Exact b)
  | b == 0 = Left DivideByZero
  | otherwise = Right (Exact (a / b))
divM p x y
  -- A quotient of proportional forms is exact: the same nudges with the same
  -- identities are the same unknowns, so x / x = 1 and (90·u) / u = 90.
  | midpoint y /= 0
  , let k = midpoint x / midpoint y
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
  Affine _ ts s -> affine f (Map.map (first (slope *)) ts) (abs slope * s)

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
                (builtinId name p operands)
                (size', Nudge Bound (Builtin name))
                ts
            )
            s

-- | A value known only as an enclosure @m ± size@ from one operation.
fresh :: Text -> Precision -> [Magnitude] -> Rational -> Rational -> Magnitude
fresh name p operands m size = withFresh name p operands size (Exact m)

builtinId :: Text -> Precision -> [Magnitude] -> NudgeId
builtinId name p operands =
  NudgeId
    (SHA256.hash (bytes name <> bytes (tshow p) <> foldMap fingerprint operands))
 where
  bytes = TE.encodeUtf8
  fingerprint = \case
    Exact r -> bytes (tshow r)
    Affine m ts s ->
      bytes (tshow m)
        <> foldMap (\(NudgeId i, (c, _)) -> i <> bytes (tshow c)) (Map.toList ts)
        <> bytes (tshow s)

tshow :: (Show a) => a -> Text
tshow = T.pack . show

{- | After a nonlinear step: fold the smallest bound nudges beyond the limit
into slack (design §3.2.7). Statistical nudges are kept: a σ must never
quietly become a bound.
-}
finish :: Precision -> Magnitude -> Magnitude
finish _ = \case
  Affine m ts s
    | Map.size ts > nudgeLimit ->
        let bounds = sortOnAbs snd [(i, c) | (i, (c, Nudge Bound _)) <- Map.toList ts]
            excess = drop (nudgeLimit `div` 2) bounds
            ts' = foldr (Map.delete . fst) ts excess
         in Affine m ts' (s + sum (map (abs . snd) excess))
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
isqrt n = go n
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
          square (s, e) =
            let s' = roundAt (precisionExponent q s) (s * s)
             in (s', 2 * abs s * e + e * e + abs (s * s - s'))
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

{- | Apply a function to a magnitude given approximations of @f@ and @f'@ and
a bound on the linearisation remainder over the enclosure: linearise at
the midpoint and fold the remainder and both approximation errors into
one fresh bound nudge.
-}
liftWith ::
  Text ->
  Precision ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  (Rational -> Rational -> Rational) ->
  Magnitude ->
  Magnitude
liftWith name p f f' remainderOver x =
  let m = midpoint x
      r = radius x
      (fm, fe) = f m
      (fm', fe') = f' m
      size = fe + fe' * r + (if r == 0 then 0 else remainderOver fm fm')
   in finish p (withFresh name p [x] size (linearise x fm fm'))

{- | For a function that is convex or concave over the enclosure: the tangent
line's error is largest at an endpoint, so evaluate it there.
-}
liftEndpoints ::
  Text ->
  Precision ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  Magnitude ->
  Magnitude
liftEndpoints name p f f' x = liftWith name p f f' remainder x
 where
  m = midpoint x
  remainder fm fm' =
    maximum
      [ abs (fy - fm - fm' * (y - m)) + ey + snd (f m)
      | y <- [lo x, hi x]
      , let (fy, ey) = f y
      ]

-- | For a function with @|f''| ≤ b@ over the enclosure: Taylor's remainder.
liftBounded ::
  Text ->
  Precision ->
  (Rational -> Approx) ->
  (Rational -> Approx) ->
  Rational ->
  Magnitude ->
  Magnitude
liftBounded name p f f' b x = liftWith name p f f' (\_ _ -> b * radius x * radius x / 2) x

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
  x -> liftEndpoints "exp" p (expApprox (p + 2)) (expApprox (p + 2)) x

logM :: Precision -> Magnitude -> Either ArithError Magnitude
logM p x
  | lo x <= 0 = Left (Domain "log of a value that may be zero or negative")
  | Exact 1 <- x = Right (Exact 0)
  | otherwise =
      Right (liftEndpoints "log" p (logApprox (p + 2)) (\m -> (recip m, 0)) x)

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
    -- \|sinh''| = |sinh| ≤ cosh at the far end of the enclosure.
    let far = max (abs (lo x)) (abs (hi x))
        (c, ce) = coshApprox p far
     in liftWith
          "sinh"
          p
          (sinhApprox (p + 2))
          (coshApprox (p + 2))
          (\_ _ -> (c + ce) * radius x * radius x / 2)
          x
coshM p = \case
  Exact 0 -> Exact 1
  x -> liftEndpoints "cosh" p (coshApprox (p + 2)) (sinhApprox (p + 2)) x

tanhM :: Precision -> Magnitude -> Either ArithError Magnitude
tanhM p x = divM p (sinhM p x) (coshM p x)

-- | π at the working precision.
piM :: Precision -> Magnitude
piM p =
  let (v, e) = piApprox p
      v' = roundAt (negate p) v
   in fresh "pi" p [] v' (e + abs (v - v'))

-- Rounding to integers --------------------------------------------------------------------

{- | Integer rounding is exact on exact inputs and on enclosures that do not
straddle a rounding boundary; otherwise it cannot be decided.
-}
floorM, ceilM, roundM :: Magnitude -> Either ArithError Magnitude
floorM = roundingWith "floor" (fromInteger . floor)
ceilM = roundingWith "ceil" (fromInteger . ceiling)
roundM = roundingWith "round" (fromInteger . round)

roundingWith ::
  Text -> (Rational -> Rational) -> Magnitude -> Either ArithError Magnitude
roundingWith name f x
  | f (lo x) == f (hi x) = Right (Exact (f (lo x)))
  | otherwise =
      Left (Undecided (name <> " of an enclosure that straddles a rounding boundary"))

-- Comparison -------------------------------------------------------------------------------

-- | Design §3.2.9: @a < b@ is decided when @|mid (a − b)| > bound + k·σ@.
compareM ::
  Int -> Precision -> Magnitude -> Magnitude -> Either ArithError Ordering
compareM k p a b =
  let c = collapse (subM a b)
      sigma = sigmaOf p c
      approx r = tshow (fromRational r :: Double)
   in if c.mid == 0 && c.bound == 0 && c.variance == 0
        then Right EQ
        else
          if abs c.mid > c.bound + fromIntegral k * sigma
            then Right (compare c.mid 0)
            else
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
equalM :: Int -> Precision -> Magnitude -> Magnitude -> Either ArithError Bool
equalM k p a b = (== EQ) <$> compareM k p a b

-- Declared uncertainty --------------------------------------------------------------------

{- | @x ± e@ / @x ±σ e@ (design §3.2.5). The nudge's identity is its origin
and the midpoint; its size is the error's midpoint, and any radius the error
itself carries goes to slack.
-}
uncertain :: NudgeKind -> Origin -> Magnitude -> Magnitude -> Magnitude
uncertain k origin x e =
  let (m, ts, s) = parts x
      size = abs (midpoint e)
   in affine
        m
        (Map.insertWith addCoeff (originId k origin m) (size, Nudge k origin) ts)
        (s + radius e)

-- | One component of @noise n@ / @gauss n@: a unit nudge.
unitNoise :: NudgeKind -> Origin -> Magnitude
unitNoise k origin = affine 0 (Map.singleton (originId k origin 0) (1, Nudge k origin)) 0

{- | Design §3.2.4: an unlabelled nudge is named by its definition, path,
component and midpoint, so  2@ and  3@ from  f x = x ± 0.01@ are
independent while two evaluations of  2@ share. A tag names the unknown
itself, nothing else:  ± r #s7@ is  + r·e_s7@ whatever @ and @ are,
which is how a systematic error shared by several readings is written.
-}
originId :: NudgeKind -> Origin -> Rational -> NudgeId
originId k origin m = NudgeId . SHA256.hash $ case origin of
  Declared (Hash h) path i -> h <> TE.encodeUtf8 (tshow (k, path, i, m))
  Tagged l i -> TE.encodeUtf8 ("#" <> l) <> TE.encodeUtf8 (tshow (k, i))
  Builtin name -> TE.encodeUtf8 name

{- | The coefficients of the statistical nudges: one column of the
square-root factor of the covariance (design §3.5).
-}
statCoefficients :: Magnitude -> Map NudgeId Rational
statCoefficients = \case
  Exact _ -> Map.empty
  Affine _ ts _ -> Map.mapMaybe (\(c, n) -> if n.kind == Stat then Just c else Nothing) ts
