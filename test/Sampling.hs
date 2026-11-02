module Sampling (samplingTests) where

import Backend (doubleConfig, doubleOf, numberAs, runWith)
import Data.Either (isLeft)
import Data.Ratio ((%))
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Metron.Double (Dbl (..), Estimate (..))
import Metron.Eval (Config (..))
import Metron.Numerical.Rational qualified as R
import Metron.Numerical.SamplePlan qualified as Plan
import Metron.Numerical.Sampling qualified as S
import Metron.Numerical.Statistics qualified as Stats
import Metron.Rational (Rat (..))
import Metron.Scalar (Rounding (RoundNearest))
import Metron.Scalar qualified as Scalar
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

samplingTests :: TestTree
samplingTests =
  localOption (mkTimeout 30_000_000)
    $ testGroup
      "separate sampling foundation"
      [ testCase "a chart step is checked in every realization" $ do
          let r = Rat 1 (Just (V.fromList [1, 0]))
              d = Dbl 1 (Copies mempty (VU.fromList [1, 0])) Nothing
          Scalar.stepProblem r @?= Just "its step is zero"
          Scalar.stepProblem d @?= Just "its step is zero"
      , testCase "rational kernels preserve exact matrix arithmetic" $ do
          let s = Scalar.settingsAt 24
              plain x = Rat x Nothing
              matrix = map (map plain)
          Scalar.determinantM s 2 (matrix [[1, 2], [3, 4]]) @?= Right (plain (-2))
          Scalar.invertM s 2 (matrix [[1, 2], [3, 4]])
            @?= Right (matrix [[-2, 1], [3 / 2, -(1 / 2)]])
          isLeft (Scalar.invertM s 2 (matrix [[1, 2], [2, 4]])) @? "singular matrix"
          Scalar.matrixExpM s 2 (matrix [[0, 1], [0, 0]])
            @?= Right (matrix [[1, 1], [0, 1]])
          Scalar.choleskyM s "symmetric" (matrix [[4, 2], [2, 2]])
            @?= Right (matrix [[2, 0], [1, 1]])
          Scalar.determinantM s 0 [] @?= Right (plain 1)
          Scalar.invertM @Rat s 0 [] @?= Right []
      , testCase "rational input samples survive branching and preserve sharing" $ do
          let cfg =
                doubleConfig
                  { backend = Scalar.RationalBackend
                  , samples = 20
                  , rounding = RoundNearest
                  }
              number = numberAs @Rat cfg
          number "3 * (1/3)" @?= Right (Rat 1 Nothing)
          case number "let x = sample (normal 10 0.1) in x-x" of
            Left err -> assertFailure (T.unpack err)
            Right x -> x.samples @?= Just (V.replicate 20 0)
          case number "let x = sample (uniform (-1) 1) in if x < 0 then -1 else 1" of
            Left err -> assertFailure (T.unpack err)
            Right x -> case x.samples of
              Just values -> do
                V.length values @?= 20
                V.all (\v -> v == -1 || v == 1) values @? show values
                V.any (== -1) values && V.any (== 1) values @? "both branches sampled"
              Nothing -> assertFailure "input samples lost at branch"
          isLeft (number "sample (normal (sample (normal 0 1)) 1)")
            @? "rational sampled parameters refused"
      , testCase "explicit sampled inputs share their draws through the language" $ do
          let config = doubleConfig{samples = 20, rounding = RoundNearest}
          case doubleOf config "let x = sample (normal (10 m) (0.1 m)) in x-x" of
            Left err -> assertFailure (T.unpack err)
            Right value -> case value.estimate of
              Copies _ values -> VU.toList values @?= replicate 20 0
              _ -> assertFailure (show value)
          case doubleOf config "sample (uniform (1 m) (2 m))" of
            Left err -> assertFailure (T.unpack err)
            Right value -> case value.estimate of
              Copies _ values -> VU.all (\x -> x >= 1 && x <= 2) values @? show value
              _ -> assertFailure (show value)
          isLeft (runWith config ["sample (normal (1 m) (1 s))"])
            @? "distribution dimensions differ"
          isLeft (runWith config ["sample (normal 0 (-1))"]) @? "negative deviation"
          isLeft (runWith config ["sample (normal (sample (normal 0 1)) 1)"])
            @? "sampled parameters refused"
      , testCase "run grid keeps baselines separate from rounding repetitions" $ do
          case Plan.makePlan 100 True 2 3 of
            Left err -> assertFailure (show err)
            Right plan -> do
              plan.runCount @?= 8
              Plan.baselineIndices plan @?= [0, 4]
              Plan.roundingIndices plan 1 @?= Just [5, 6, 7]
              map (Plan.coordinate plan) [0 .. 7]
                @?= map
                  Just
                  [ Plan.Baseline 0
                  , Plan.Rounding 0 0
                  , Plan.Rounding 0 1
                  , Plan.Rounding 0 2
                  , Plan.Baseline 1
                  , Plan.Rounding 1 0
                  , Plan.Rounding 1 1
                  , Plan.Rounding 1 2
                  ]
          case Plan.makePlan 100 False 10000 8 of
            Left err -> assertFailure (show err)
            Right plan -> plan.runCount @?= 9
          isLeft (Plan.makePlan 100 True maxBound maxBound)
            @? "overflow refused before allocation"
          isLeft (Plan.makePlan 100 True 10 1) @? "one rounding repetition refused"
      , testCase "input statistics use only ordinary outcomes" $ do
          case Stats.summariseInputs 24 [0, 10] of
            Left e -> assertFailure (show e)
            Right result -> do
              result.mean @?= 5
              result.lower95 @?= 1 / 4
              result.upper95 @?= 39 / 4
          case Stats.summariseRounding 24 [(0, [-1, 1]), (10, [9, 11])] of
            Left e -> assertFailure (show e)
            Right result -> do
              result.baselineDisplacement @?= 1
              abs (result.typicalSpread * result.typicalSpread - 2) < 1 % 10 ^ (22 :: Int)
                @? show result
      , testCase "agreeing repetitions can still differ from the baseline" $ do
          case Stats.summariseRounding 24 [(0, [2, 2])] of
            Left e -> assertFailure (show e)
            Right result -> do
              result.typicalSpread @?= 0
              result.baselineDisplacement @?= 2
              result.variationObserved @?= False
      , testCase "statistics survive extreme rational scales" $ do
          let x = 10 ^ (400 :: Int)
          case Stats.summariseInputs 24 [-x, 0, x] of
            Left e -> assertFailure (show e)
            Right result -> do
              result.mean @?= 0
              result.deviation @?= Just x
          case Stats.summariseInputs 24 [7] of
            Left e -> assertFailure (show e)
            Right result -> result.deviation @?= Nothing
          isLeft (Stats.summariseRounding 24 [(0, [1])]) @? "one repetition"
          isLeft (Stats.summariseRounding 24 [(0, [1, 2]), (0, [1, 2, 3])])
            @? "unequal groups"
      , testCase "rational division and powers remain exact" $ do
          R.divide 1 10 @?= Right (1 % 10)
          R.power (1 % 3) 100 @?= Right (1 % (3 ^ (100 :: Int)))
          isLeft (R.divide 1 0) @? "zero denominator"
          isLeft (R.power 0 (-1)) @? "negative power of zero"
      , testCase "rational roots retain perfect squares" $ do
          R.squareRoot 24 (49 % 121) @?= Right (7 % 11)
          isLeft (R.squareRoot 24 (-1)) @? "negative root"
          case R.squareRoot 24 2 of
            Right x -> abs (x * x - 2) < 1 % 10 ^ (22 :: Int) @? show x
            Left e -> assertFailure (show e)
      , testCase "rational elementary functions respect domains and identities" $ do
          R.logarithm 24 1 @?= Right 0
          R.exponential 24 0 @?= 1
          R.sine 24 0 @?= 0
          R.cosine 24 0 @?= 1
          isLeft (R.logarithm 24 0) @? "log domain"
          isLeft (R.arcSine 24 2) @? "asin domain"
          R.arcCosine 24 1 @?= Right 0
          R.inverseHyperbolicSine 24 0 @?= Right 0
          case ( R.inverseHyperbolicSine 24 (10 ^ (20 :: Int))
               , R.inverseHyperbolicSine 24 (-(10 ^ (20 :: Int)))
               ) of
            (Right a, Right b) -> a @?= -b
            other -> assertFailure (show other)
      , testCase "distribution parameters are validated" $ do
          isLeft (S.normal 0 (-1)) @? "negative sd"
          isLeft (S.uniform 2 1) @? "reversed endpoints"
      , testCase "deterministic distributions have no spread" $ do
          forSamples (S.normal 7 0) $ \values -> values @?= replicate 100 7
          forSamples (S.uniform 3 3) $ \values -> values @?= replicate 100 3
      , testCase "uniform draws stay inside their input support"
          $ forSamples (S.uniform (-3) 7)
          $ \values ->
            all (\x -> x > -3 && x < 7) values @? show values
      , testCase "normal draws have the expected fixed-seed moments" $ do
          case S.normal 0 1 of
            Left err -> assertFailure (show err)
            Right distribution -> case traverse (\i -> S.draw 12 1 "normal" i distribution) [0 .. 999] of
              Left err -> assertFailure (show err)
              Right values -> do
                let xs = map fromRational values :: [Double]
                    mean = sum xs / 1000
                    variance = sum (map (\x -> (x - mean) ^ (2 :: Int)) xs) / 999
                abs mean < 0.15 @? show mean
                variance > 0.8 && variance < 1.2 @? show variance
      , testProperty "input words agree under worker partition" $ \(NonNegative raw) ->
          let n = 1 + raw `mod` 100
              expected = [S.inputWord 7 "input" i 0 | i <- [0 .. n - 1]]
              partitions k =
                concat
                  [ [S.inputWord 7 "input" i 0 | i <- [start .. min (n - 1) (start + k - 1)]]
                  | start <- [0, k .. n - 1]
                  ]
           in all ((== expected) . partitions) [1, 2, 4]
      , testCase "rounding coins distinguish input, repetition and operation" $ do
          let a = S.roundingWord 1 "a" 0 0 0
          a /= S.inputWord 1 "a" 0 0 @? "stream domains differ"
          a /= S.roundingWord 1 "a" 0 0 1 @? "rounding repetitions differ"
          a /= S.roundingWord 1 "a" 0 1 0 @? "input indices differ"
          a /= S.roundingWord 1 "b" 0 0 0 @? "operation occurrences differ"
          a /= S.roundingWord 1 "a" 1 0 0 @? "invocations differ"
      ]
 where
  forSamples result action = case result of
    Left err -> assertFailure (show err)
    Right distribution -> case traverse (\i -> S.draw 12 1 "input" i distribution) [0 .. 99] of
      Left err -> assertFailure (show err)
      Right values -> action values
