{- | Separate summaries for input outcomes and within-input rounding runs.
All accumulations are rational, so intermediate squares cannot overflow.
Square roots are approximated at the requested working precision.
-}
module Metron.Numerical.Statistics (
  InputSummary (..),
  RoundingSummary (..),
  summariseInputs,
  summariseRounding,
  covariance,
) where

import Data.List (sort)
import Data.Ratio ((%))
import Metron.Numerical.Approx (Precision)
import Metron.Numerical.Error (ArithError (Domain))
import Metron.Numerical.Rational (squareRoot)

data InputSummary = InputSummary
  { count :: !Int
  , mean :: !Rational
  , deviation :: !(Maybe Rational)
  , lower95 :: !Rational
  , upper95 :: !Rational
  }
  deriving stock (Eq, Show)

data RoundingSummary = RoundingSummary
  { inputs :: !Int
  , repetitions :: !Int
  , typicalSpread :: !Rational
  , baselineDisplacement :: !Rational
  , variationObserved :: !Bool
  }
  deriving stock (Eq, Show)

summariseInputs :: Precision -> [Rational] -> Either ArithError InputSummary
summariseInputs _ [] = Left (Domain "input statistics need at least one result")
summariseInputs p xs = do
  deviation <- traverse (squareRoot p) (variance xs)
  let ordered = sort xs
  Right
    ( InputSummary
        (length xs)
        (meanOf xs)
        deviation
        (quantile (1 % 40) ordered)
        (quantile (39 % 40) ordered)
    )

{- | Each row is one baseline together with its rounding repetitions.
Never pool the repetitions to estimate input variation.
-}
summariseRounding ::
  Precision -> [(Rational, [Rational])] -> Either ArithError RoundingSummary
summariseRounding _ [] = Left (Domain "rounding statistics need at least one input")
summariseRounding p rows@((_, first) : _)
  | r < 2 = Left (Domain "rounding statistics need at least two repetitions")
  | any ((/= r) . length . snd) rows =
      Left (Domain "rounding groups have different repetition counts")
  | otherwise = do
      spread <-
        squareRoot
          p
          (meanOf [sumSquaresFrom (meanOf xs) xs / fromIntegral (r - 1) | (_, xs) <- rows])
      displacement <-
        squareRoot
          p
          ( sum [sumSquaresFrom base xs | (base, xs) <- rows]
              / (fromIntegral (length rows) * fromIntegral r)
          )
      let varies (_, x : xs) = any (/= x) xs
          varies (_, []) = False
          observed = any varies rows
      Right (RoundingSummary (length rows) r spread displacement observed)
 where
  r = length first

meanOf :: [Rational] -> Rational
meanOf xs = sum xs / fromIntegral (length xs)

variance :: [Rational] -> Maybe Rational
variance xs
  | length xs < 2 = Nothing
  | otherwise =
      Just (sumSquaresFrom (meanOf xs) xs / fromIntegral (length xs - 1))

sumSquaresFrom :: Rational -> [Rational] -> Rational
sumSquaresFrom centre = foldl' (\acc x -> let d = x - centre in acc + d * d) 0

-- | Sample covariance of paired ordinary input outcomes, with Bessel correction.
covariance :: [Rational] -> [Rational] -> Either ArithError Rational
covariance xs ys
  | length xs /= length ys = Left (Domain "covariance needs paired input samples")
  | length xs < 2 = Left (Domain "covariance needs at least two input samples")
  | otherwise =
      Right
        ( sum (zipWith (\x y -> (x - meanOf xs) * (y - meanOf ys)) xs ys)
            / fromIntegral (length xs - 1)
        )

-- Linear interpolation at (n-1)*p, also called the type-7 quantile.
-- Called only for nonempty sorted data and p in [0,1].
quantile :: Rational -> [Rational] -> Rational
quantile p xs =
  let position = fromIntegral (length xs - 1) * p
      i = floor position
      fraction = position - fromIntegral i
      lower = xs !! i
   in if fraction == 0 then lower else lower + fraction * (xs !! (i + 1) - lower)
