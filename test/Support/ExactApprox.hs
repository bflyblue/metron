{- | The elementary-function approximations as they were before working
precision reached their series (design §3.2.8, "Series run in fixed
point"): every series summed in exact rationals. Slow but rigorous, so a
test oracle: a fixed-point result and this one must lie within their two
error bounds of each other.
-}
module Support.ExactApprox (
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
  scaleA,
) where

import Data.Ratio (denominator, numerator, (%))
import GHC.Num (integerLog2)

type Precision = Int

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
      let (k, y) = reduce k0 (x / 2 ^^ k0)
          z = (y - 1) / (y + 1)
       in addA (scaleA (fromInteger k) (ln2Approx (p + 4))) (scaleA 2 (atanhApprox p z))
 where
  -- The power of two, to within one, from the sizes of x's parts: halving
  -- one step at a time took 330000 steps of a 100000-digit rational for
  -- @log 1e-99999@.
  k0 =
    toInteger (integerLog2 (numerator x)) - toInteger (integerLog2 (denominator x))
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
