{- | Rational elementary-function approximations with explicit absolute
error bounds, computed at working precision (design §3.2.8).

Every series is summed in fixed point: an integer counting units of
@2^-b@, with @b@ bits enough for the precision asked and guard bits for
the roundings. Each step of a series rounds once, by at most a unit or
two, and the bound returned counts every such rounding, the series'
tail and the rounding of the argument itself. Summing in exact
rationals instead made every term longer than the last (the terms of
@log 1e-99999@ had hundreds of thousands of digits), so that a series'
cost grew with the square of its length rather than with the precision.
π and @ln 2@ are computed once per precision bucket and kept.
-}
module Metron.Numerical.Approx (
  Precision,
  Approx,
  decimalExponent,
  precisionExponent,
  roundAt,
  roundUpAt,
  tolerance,
  isqrt,
  sqrtApprox,
  expApprox,
  logApprox,
  piApprox,
  atanApprox,
  sinCosApprox,
  sinhApprox,
  coshApprox,
  tanApprox,
  sec2Approx,
  tanhApprox,
  sech2Approx,
  scaleA,
) where

import Data.Bits (bit, shiftL, shiftR)
import Data.Ratio (denominator, numerator, (%))
import GHC.Num (integerLog2)

type Precision = Int

{- | The exponent of the leading decimal digit: @decimalExponent 0.0123 =
-2@. Estimated from the bit lengths of numerator and denominator, then
corrected by exact comparison with powers of ten, so that it costs a few
operations on the value's integers whatever its exponent (counting by
tens took a step per digit, and a value near @1e-99999@ has 99999).
-}
decimalExponent :: Rational -> Int
decimalExponent r
  | r == 0 = 0
  | otherwise = settle estimate
 where
  n = abs (numerator r)
  d = denominator r
  estimate =
    floor
      ( fromIntegral (toInteger (integerLog2 n) - toInteger (integerLog2 d))
          * logBase 10 2 ::
          Double
      )
  -- \|r| ≥ 10^e, compared on integers.
  atLeast e
    | e >= 0 = n >= d * 10 ^ e
    | otherwise = n * 10 ^ negate e >= d
  settle e
    | not (atLeast e) = settle (e - 1)
    | atLeast (e + 1) = settle (e + 1)
    | otherwise = e

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

-- | An approximation and a bound on its absolute error.
type Approx = (Rational, Rational)

-- | The absolute error allowed at @p@ digits for a result of size @v@.
tolerance :: Precision -> Rational -> Rational
tolerance p v = 10 ^^ precisionExponent p v

scaleA :: Rational -> Approx -> Approx
scaleA k (v, e) = (k * v, abs k * e)

addA :: Approx -> Approx -> Approx
addA (a, e) (b, f) = (a + b, e + f)

-- Fixed point ---------------------------------------------------------------------------

-- | Bits for @p@ decimal digits: at least @p · log₂ 10@.
bitsFor :: Int -> Int
bitsFor p = max 8 ((p * 3322 + 999) `div` 1000)

{- | Bits for @p@ digits and the roundings of a series of about as many
terms as bits, each of a few units: their count squared, and a margin.
-}
workingBits :: Int -> Int
workingBits p = let b = bitsFor p in b + 2 * (log2 (toInteger b) + 1) + 8

-- | @⌊log₂ n⌋@ for @n > 0@, as an 'Int'.
log2 :: Integer -> Int
log2 = fromIntegral . integerLog2

-- | The floor of @x · 2^b@: @x@ in fixed point, within one unit below.
fixed :: Int -> Rational -> Integer
fixed b x = (numerator x `shiftL` b) `div` denominator x

-- | A fixed-point value and its error, both in units of @2^-b@, as an approximation.
unfixed :: Int -> (Integer, Integer) -> Approx
unfixed b (v, e) = (v % bit b, e % bit b)

{- | @Σ tⱼ@ in fixed point, from @t₀@ and a step @(j, tⱼ) ↦ tⱼ₊₁@. Each
step rounds once and adds at most @c@ units to a term's error, never
enlarging an earlier error (the ratio of one term to the last is at most
one); and from the first term on, terms at least halve, so the tail from
a term is at most twice it. Stops at the first term of at most one unit.
The sum and its error, in units.
-}
fixedSum ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> (Integer, Integer)
fixedSum c step = go 0 0 0 0
 where
  go j e acc accErr t
    | abs t <= 1 = (acc, accErr + 2 * (abs t + e))
    | otherwise = go (j + 1) (e + c) (acc + t) (accErr + e) (step j t)

{- | @Σ (±1)ʲ x^(2j+1) / (2j+1)@, the series of @atan@ (alternating) and of
@atanh@, in fixed point at @b@ bits for @|x| ≤ 1/4@ given exactly as @X /
2^b@. Its powers and its terms each round once: a power's error grows by
at most two units a step (its square's rounding, and its own), a term's
is the power's and one more. Terms fall by @x² ≤ 1/16@, so the tail from
a term is at most twice it.
-}
oddPowerSeries :: Bool -> Int -> Integer -> (Integer, Integer)
oddPowerSeries alternating b x = go 0 0 0 0 x
 where
  x2 = (x * x) `shiftR` b
  go j e acc accErr power
    | abs power <= 1 = (acc, accErr + 2 * (abs power + e + 1))
    | otherwise =
        let term = power `quot` (2 * j + 1)
            signed = if alternating && odd j then negate term else term
         in go (j + 1) (e + 2) (acc + signed) (accErr + e + 1) ((power * x2) `shiftR` b)

-- Square root ---------------------------------------------------------------------------

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

{- | @√r@ for @r ≥ 0@, from below, with its error, at most @10^-p@ relative
to the result. The root is taken of @r · 4ᵏ@'s integer part, @k@ chosen
from @r@'s bit lengths so that it has about @2p@ digits whatever @r@'s
size: scaling by @10^p@ instead took the root of a number as long as
@r@'s numerator and denominator together, 100000 digits for @1e-99999@.
-}
sqrtApprox :: Precision -> Rational -> Approx
sqrtApprox p r
  | r <= 0 = (0, 0)
  | otherwise =
      let n = numerator r
          d = denominator r
          wanted = bitsFor p + 4
          log2r = toInteger (log2 n - log2 d)
          k = toInteger wanted - log2r `div` 2
          m
            | k >= 0 = (n `shiftL` fromInteger (2 * k)) `div` d
            | otherwise = n `div` (d `shiftL` fromInteger (negate (2 * k)))
          s = isqrt m
          -- √(r·4ᵏ) − s < √(m + 1) − √m + 1 ≤ 2.
          scaleDown v
            | k >= 0 = v % bit (fromInteger k)
            | otherwise = fromInteger (v `shiftL` fromInteger (negate k))
       in (scaleDown s, scaleDown 2)

-- Constants -----------------------------------------------------------------------------

{- | A constant computed once for each precision bucket (64, 128, 256, …
digits) and kept, rounded to the precision asked with the rounding added
to its error. A value is a pure function of the precision, as every
value is (design §3.2.8).
-}
cached :: [Approx] -> Precision -> Approx
cached table p = case dropWhile ((< p) . fst) (zip buckets table) of
  (_, (v, e)) : _ ->
    let v' = roundAt (negate (p + 2)) v
     in (v', e + abs (v - v'))
  [] -> (0, 0)
 where
  buckets = iterate (* 2) 64

-- | π by Machin's formula, @16 atan (1/5) − 4 atan (1/239)@.
piApprox :: Precision -> Approx
piApprox = cached piTable

piTable :: [Approx]
piTable = map machin (iterate (* 2) 64)
 where
  machin digits =
    let b = workingBits (digits + 4)
        -- 1/n within a unit below; atan's slope is at most one.
        atanInverse n =
          let (s, e) = oddPowerSeries True b (bit b `div` n) in (s, e + 1)
        (a, ae) = atanInverse 5
        (c, ce) = atanInverse 239
     in unfixed b (16 * a - 4 * c, 16 * ae + 4 * ce)

-- | @ln 2 = 2 atanh (1/3)@.
ln2Approx :: Precision -> Approx
ln2Approx = cached ln2Table

ln2Table :: [Approx]
ln2Table = map ln2 (iterate (* 2) 64)
 where
  ln2 digits =
    let b = workingBits (digits + 4)
        -- 1/3 within a unit below; atanh's slope there is 9/8.
        (s, e) = oddPowerSeries False b (bit b `div` 3)
     in unfixed b (2 * s, 2 * (e + 2))

-- Elementary functions ------------------------------------------------------------------

{- | @e^x@. Halve the argument until it is at most a quarter, sum the series
in fixed point, square back. Squaring doubles the relative error each
time, so the series is summed with two guard digits per halving.
-}
expApprox :: Precision -> Rational -> Approx
expApprox p x
  | x == 0 = (1, 0)
  | otherwise =
      let log2x = log2 (abs (numerator x)) - log2 (denominator x)
          -- \|x| < 2^(log2x + 1), so |x| / 2^(log2x + 3) < 1/4.
          k = max 0 (log2x + 3)
          q = p + 2 * k + 4
          b = workingBits q
          one = bit b :: Integer
          -- x / 2^k within a unit below; e^r's slope is below 1.3.
          r = fixed b (x / 2 ^ k)
          (s, e) = fixedSum 1 (\j t -> (t * r) `div` (one * (j + 1))) one
          -- The square is rounded at its own last digit, and its error
          -- bound rounded up there: rounded at the last digit of the value
          -- squared, a small result lost every digit (e^-200 came out as
          -- 0), and only a working precision of hundreds of digits found
          -- it, which took seconds for e^-10000.
          square (v, ve) =
            let vv = v * v
                at = precisionExponent q vv
                v' = roundAt at vv
             in (v', roundUpAt at (2 * abs v * ve + ve * ve + abs (vv - v')))
       in foldl' (\a _ -> square a) (unfixed b (s, e + 2)) [1 .. k]

{- | @ln x@ for @x > 0@: @x = 2ᵏ y@ with @y@ in @[1/√2, √2)@, @k@ found from
the sizes of @x@'s parts, then @k ln 2 + 2 atanh ((y − 1)/(y + 1))@ with
@|(y − 1)/(y + 1)| < 0.18@. @y@ is put in fixed point at once, so a long
argument costs one division: @1e-99999@'s reduced argument kept all its
100000 digits through the series. Near one, where @ln x@ is about @x −
1@, the precision is relative to that.
-}
logApprox :: Precision -> Rational -> Approx
logApprox p x
  | x == 1 = (0, 0)
  | otherwise =
      let n = numerator x
          d = denominator x
          k0 = log2 n - log2 d
          nearOne
            | k0 == 0 || k0 == -1 = max 0 (negate (decimalExponent (x - 1)))
            | otherwise = 0
          b = workingBits (p + 4 + nearOne)
          one = bit b :: Integer
          -- y · 2^b = n · 2^(b − k) / d, within a unit below.
          fixedY k
            | b - k >= 0 = (n `shiftL` (b - k)) `div` d
            | otherwise = n `div` (d `shiftL` (k - b))
          settle k
            | y * y >= 2 * one * one = settle (k + 1)
            | 2 * y * y < one * one = settle (k - 1)
            | otherwise = (toInteger k, y)
           where
            y = fixedY k
          (kk, yy) = settle k0
          -- z's error: the division's unit and y's, scaled by
          -- dz/dy = 2/(y + 1)² < 0.7; atanh's slope is below 1.04.
          z = ((yy - one) * one) `div` (yy + one)
          (s, e) = oddPowerSeries False b z
          lnY = unfixed b (2 * s, 2 * (e + 3))
          (l2, l2e) = ln2Approx (p + 4 + length (show (abs kk)))
       in addA (fromInteger kk * l2, abs (fromInteger kk) * l2e) lnY

-- | @atan x@ for any @x@: @π/2 − atan (1/x)@ beyond one.
atanApprox :: Precision -> Rational -> Approx
atanApprox p x
  | x < 0 = scaleA (-1) (atanApprox p (negate x))
  | x == 0 = (0, 0)
  | x > 1 =
      let (pv, pe) = piApprox (p + 4)
          (a, ae) = atanUnit p (recip x)
       in (pv / 2 - a, pe / 2 + ae)
  | otherwise = atanUnit p x

{- | @atan x@ for @0 < x ≤ 1@, relative to its size: halve the angle with
@atan x = 2 atan (x / (1 + √(1 + x²)))@ until @x ≤ 1/8@, at most three
times, in fixed point, then the series. The halving map's slope is at
most a half and each step rounds twice, so the argument's error stays
within four units however many steps; each halving doubles both errors
on the way back.
-}
atanUnit :: Precision -> Rational -> Approx
atanUnit p x =
  let b = workingBits (p + 4 + max 0 (negate (decimalExponent x)))
      one = bit b :: Integer
      halve (h, v)
        | v <= one `shiftR` 3 = (h, v)
        | otherwise = halve (h + 1, (v * one) `div` (one + isqrt (one * one + v * v)))
      (halvings, reduced) = halve (0 :: Int, fixed b x)
      (s, e) = oddPowerSeries True b reduced
      double = 2 ^ halvings :: Integer
   in unfixed b (double * s, double * (e + 4))

{- | @sin x@ and @cos x@: @x = k π/2 + r@ with @|r| ≤ π/4@, Taylor series in
fixed point for @r@, and the quadrant from @k@. π comes to as many more
digits as @x@ has before the point, and, when @r@ is small, as many again
as @r@ has zeros after it, so that the sine of an angle near a multiple
of π keeps its digits relative to itself, up to a limit. The sine is
summed relative to @r@'s size.
-}
sinCosApprox :: Precision -> Rational -> (Approx, Approx)
sinCosApprox p x
  | x == 0 = ((0, 0), (1, 0))
  | otherwise =
      let whole = max 0 (decimalExponent x + 1)
          reduce extra =
            let (pv, pe) = piApprox (p + 8 + whole + extra)
                quarter = round (x / (pv / 2)) :: Integer
             in ( quarter
                , x - fromInteger quarter * pv / 2
                , abs (fromInteger quarter) * pe / 2
                )
          first = reduce 0
          zeros (_, v, _) = if v == 0 then 0 else max 0 (negate (decimalExponent v))
          (k, r, re) =
            if zeros first == 0 then first else reduce (min (2 * p + 16) (zeros first + 2))
          b = workingBits (p + 6 + zeros (k, r, re))
          one = bit b :: Integer
          -- r within a unit below; both functions' slopes are at most one.
          rr = fixed b r
          r2 = (rr * rr) `shiftR` b
          (s, se) =
            fixedSum
              2
              (\j t -> negate ((t * r2) `div` (one * (2 * j + 2) * (2 * j + 3))))
              rr
          (c, ce) =
            fixedSum
              2
              (\j t -> negate ((t * r2) `div` (one * (2 * j + 1) * (2 * j + 2))))
              one
          sinR = addA (unfixed b (s, se + 1)) (0, re)
          cosR = addA (unfixed b (c, ce + 1)) (0, re)
       in case k `mod` 4 of
            0 -> (sinR, cosR)
            1 -> (cosR, scaleA (-1) sinR)
            2 -> (scaleA (-1) sinR, scaleA (-1) cosR)
            _ -> (scaleA (-1) cosR, sinR)

{- | @sinh x@ by its series for @|x| ≤ 1@ (the exponential difference would
cancel), relative to @x@'s size, and by exponentials beyond.
-}
sinhApprox :: Precision -> Rational -> Approx
sinhApprox p x
  | x == 0 = (0, 0)
  | abs x <= 1 =
      let b = workingBits (p + 4 + max 0 (negate (decimalExponent x)))
          one = bit b :: Integer
          xx = fixed b x
          x2 = (xx * xx) `shiftR` b
          (s, e) = fixedSum 2 (\j t -> (t * x2) `div` (one * (2 * j + 2) * (2 * j + 3))) xx
       in -- x within a unit below; sinh's slope is below 1.6.
          unfixed b (s, e + 2)
  | otherwise =
      scaleA
        (1 % 2)
        (addA (expApprox (p + 2) x) (scaleA (-1) (expApprox (p + 2) (negate x))))

coshApprox :: Precision -> Rational -> Approx
coshApprox p x = scaleA (1 % 2) (addA (expApprox (p + 2) x) (expApprox (p + 2) (negate x)))

{- | @tan x@ as the sine over the cosine, at more digits until the cosine
is known to @p@ digits of itself: near a pole the cosine is small and the
tangent large. The cosine of a rational other than zero is never zero,
so the digits needed are finite.
-}
tanApprox :: Precision -> Rational -> Approx
tanApprox p x = go (p + 4)
 where
  go q =
    let ((s, se), (c, ce)) = sinCosApprox q x
        t = s / c
     in if ce * 10 ^ (p + 2) > abs c
          then go (2 * q)
          else (t, (se + abs t * ce) / (abs c - ce))

-- | @tan′ x = 1 + tan² x@.
sec2Approx :: Precision -> Rational -> Approx
sec2Approx p x = let (t, te) = tanApprox (p + 4) x in (1 + t * t, (2 * abs t + te) * te)

{- | @tanh x@: the sine over the cosine for @|x| < 1@, where the
exponentials would cancel, and @(1 − q)/(1 + q)@ with @q = e^(−2|x|)@
beyond, which never overflows. Far out, @q@ is below the precision and
only bounded ('expTail').
-}
tanhApprox :: Precision -> Rational -> Approx
tanhApprox p x
  | x == 0 = (0, 0)
  | abs x < 1 =
      let (s, se) = sinhApprox (p + 4) x
          (c, ce) = coshApprox (p + 4) x
          t = s / c
       in (t, (se + abs t * ce) / (c - ce))
  | otherwise =
      -- (1 − q)/(1 + q) has slope of size at most two in q.
      let (q, qe) = expTail p x
       in (signum x * (1 - q) / (1 + q), 2 * qe)

-- | @tanh′ x = 1 − tanh² x@, as @4q/(1 + q)²@ beyond @|x| = 1@, without cancelling.
sech2Approx :: Precision -> Rational -> Approx
sech2Approx p x
  | abs x < 1 =
      let (t, te) = tanhApprox (p + 4) x in (1 - t * t, (2 * abs t + te) * te)
  | otherwise =
      -- 4q/(1 + q)² has slope at most four in q.
      let (q, qe) = expTail p x in (4 * q / ((1 + q) * (1 + q)), 4 * qe)

{- | @e^(−2|x|)@, or only a bound on it when it is below @10^-(p+10)@:
@2|x| ≥ 2.4 (p + 10) > (p + 10) ln 10@ there, so nothing is summed
whose digits are all zeros.
-}
expTail :: Precision -> Rational -> Approx
expTail p x
  | abs x * 5 > 6 * fromIntegral (p + 10) = (0, 10 ^^ negate (p + 10))
  | otherwise = expApprox (p + 4) (negate (2 * abs x))
