{- | Coordinates for independent input samples and their rounding analyses.
Each input group starts with its ordinary result, followed by R diagnostics.
-}
module Metron.Numerical.SamplePlan (
  SamplePlan (runCount, inputCount, roundingCount),
  Coordinate (..),
  makePlan,
  coordinate,
  baselineIndices,
  roundingIndices,
) where

import Data.Text (Text)

data SamplePlan = SamplePlan
  { inputCount :: !Int
  , roundingCount :: !Int
  , runCount :: !Int
  }
  deriving stock (Eq, Show)

data Coordinate = Baseline !Int | Rounding !Int !Int
  deriving stock (Eq, Show)

{- | Construct the plan before allocating. An input-free computation has one
baseline regardless of the configured input count. Zero R disables analysis.
-}
makePlan :: Integer -> Bool -> Int -> Int -> Either Text SamplePlan
makePlan limit sampled n r
  | n < 1 = Left "samples must be positive"
  | r < 0 || r == 1 = Left "roundingSamples must be zero or at least two"
  | work > limit || work > toInteger (maxBound :: Int) =
      Left "combined input and rounding runs exceed the limit"
  | otherwise = Right (SamplePlan inputs r (fromInteger work))
 where
  inputs = if sampled then n else 1
  work = toInteger inputs * (1 + toInteger r)

coordinate :: SamplePlan -> Int -> Maybe Coordinate
coordinate plan run
  | run < 0 || run >= plan.runCount = Nothing
  | otherwise =
      let (i, j) = run `divMod` (plan.roundingCount + 1)
       in Just (if j == 0 then Baseline i else Rounding i (j - 1))

baselineIndices :: SamplePlan -> [Int]
baselineIndices plan = [i * (plan.roundingCount + 1) | i <- [0 .. plan.inputCount - 1]]

roundingIndices :: SamplePlan -> Int -> Maybe [Int]
roundingIndices plan i
  | i < 0 || i >= plan.inputCount = Nothing
  | otherwise =
      Just [i * (plan.roundingCount + 1) + j | j <- [1 .. plan.roundingCount]]
