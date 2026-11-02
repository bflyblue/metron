{- | Rational arithmetic and precision-controlled elementary functions.
Approximation kernels use internal enclosures, but this API returns values,
not a propagated enclosure or a certification of a complete calculation.
-}
module Metron.Numerical.Rational (
  divide,
  power,
  squareRoot,
  logarithm,
  exponential,
  sine,
  cosine,
  tangent,
  arcSine,
  arcCosine,
  arcTangent,
  arcTangent2,
  hyperbolicSine,
  hyperbolicCosine,
  hyperbolicTangent,
  inverseHyperbolicSine,
  piAt,
) where

import Data.Ratio (denominator, numerator, (%))
import Metron.Numerical.Approx qualified as A
import Metron.Numerical.Error (ArithError (..))

divide :: Rational -> Rational -> Either ArithError Rational
divide _ 0 = Left DivideByZero
divide x y = Right (x / y)

power :: Rational -> Integer -> Either ArithError Rational
power 0 n | n < 0 = Left DivideByZero
power x n = Right (x ^^ n)

squareRoot :: A.Precision -> Rational -> Either ArithError Rational
squareRoot p x
  | x < 0 = Left (Domain "sqrt needs a nonnegative argument")
  | n * n == numerator x && d * d == denominator x = Right (n % d)
  | otherwise = Right (fst (A.sqrtApprox p x))
 where
  n = A.isqrt (numerator x)
  d = A.isqrt (denominator x)

logarithm :: A.Precision -> Rational -> Either ArithError Rational
logarithm p x
  | x <= 0 = Left (Domain "log needs a positive argument")
  | otherwise = Right (fst (A.logApprox p x))

exponential, sine, cosine, arcTangent :: A.Precision -> Rational -> Rational
exponential p = fst . A.expApprox p
sine p = fst . fst . A.sinCosApprox p
cosine p = fst . snd . A.sinCosApprox p
arcTangent p = fst . A.atanApprox p

-- Near a pole, the approximation must resolve a nonzero denominator.
-- Failure is explicit rather than silently falling back to doubles.
tangent :: A.Precision -> Rational -> Either ArithError Rational
tangent p x =
  let ((s, _), (c, e)) = A.sinCosApprox p x
   in if abs c <= e
        then Left (Domain "tan denominator is unresolved at this precision")
        else Right (s / c)

arcSine, arcCosine :: A.Precision -> Rational -> Either ArithError Rational
arcSine p x
  | abs x > 1 = Left (Domain "asin needs an argument between -1 and 1")
  | abs x == 1 = Right (signum x * piAt p / 2)
  | otherwise = do
      root <- squareRoot p (1 - x * x)
      Right (arcTangent p (x / root))
arcCosine p x
  | abs x > 1 = Left (Domain "acos needs an argument between -1 and 1")
  | otherwise = do
      root <- squareRoot p (1 - x * x)
      arcTangent2 p root x

arcTangent2 :: A.Precision -> Rational -> Rational -> Either ArithError Rational
arcTangent2 p y x
  | x > 0 = Right (arcTangent p (y / x))
  | x < 0 = Right (arcTangent p (y / x) + (if y < 0 then -1 else 1) * piAt p)
  | y /= 0 = Right (signum y * piAt p / 2)
  | otherwise = Left (Domain "atan2 is undefined at the origin")

hyperbolicSine
  , hyperbolicCosine
  , hyperbolicTangent ::
    A.Precision -> Rational -> Rational
hyperbolicSine p = fst . A.sinhApprox p
hyperbolicCosine p = fst . A.coshApprox p
hyperbolicTangent p = fst . A.tanhApprox p

inverseHyperbolicSine :: A.Precision -> Rational -> Either ArithError Rational
inverseHyperbolicSine p x = do
  root <- squareRoot p (1 + x * x)
  result <- logarithm p (abs x + root)
  Right (signum x * result)

piAt :: A.Precision -> Rational
piAt = fst . A.piApprox
