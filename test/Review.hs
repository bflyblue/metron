module Review (reviewTests) where

import Backend (doubleConfig, doubleOf, runWith)
import Control.Monad (forM_)
import Data.List (permutations)
import Data.Maybe (isJust)
import Data.Ratio ((%))
import Data.Text qualified as T
import Data.Vector.Unboxed qualified as VU
import Lang.Common (evalP)
import Metron.Affine qualified as A
import Metron.Core (NudgeKind (Bound, Stat))
import Metron.Double (Dbl (..), Estimate (..), Spread (..), estimateOf)
import Metron.Eval (Config (..))
import Metron.Numerical.Linear qualified as L
import Metron.Scalar qualified as S
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (
  chooseInt,
  counterexample,
  forAll,
  testProperty,
  vectorOf,
  within,
 )

reviewTests :: TestTree
reviewTests =
  localOption (mkTimeout 30_000_000)
    $ testGroup
      "numerical review regressions"
      [ testCase
          "uncertain widths retain statistical corrections without making hard bounds"
          $ do
            let width k m = A.uncertain 24 k (A.Tagged "width" 0) (A.Exact m) (A.Exact 1)
                outer k = A.uncertain 24 k (A.Tagged "outer" 0) (A.Exact 0)
            forM_ [Bound, Stat] $ \k -> do
              let x = outer k (width Stat 0)
              isJust (A.nonLinearAt 0 x) @? show x
            let x = outer Stat (width Bound 1)
            A.boundRadius x @?= 0
            isJust (A.nonLinearAt 0 x) @? show x
      , testCase "extreme arithmetic contains the exact rational result" $ do
          let s = S.settingsAt 24
              exponents =
                [ -1074
                , -1073
                , -1023
                , -1022
                , -1000
                , -700
                , -600
                , -538
                , -537
                , -500
                , -100
                , -1
                , 0
                , 1
                , 100
                , 500
                , 537
                , 538
                , 600
                , 700
                , 1000
                , 1023
                ] ::
                  [Int]
              inputs = [m * 2 ^^ e | e <- exponents, m <- [1, 3 % 2, 7 % 5]]
          forM_ [(a, b) | a <- inputs, b <- inputs] $ \(a, b) -> do
            let x = S.literal s a :: Dbl
                y = S.literal s b :: Dbl
            encloses (a + b) (S.addM s x y)
            encloses (a * b) (S.mulM s x y)
            either (assertFailure . show) (encloses (a / b)) (S.divM s x y)
      , testCase "range-safe double bounds and gradual underflow" $ do
          check "((1e100 + 1) - 1e100) / 1e200" (1 / 10 ^ (200 :: Int))
          check "fma (2^-537) (2^-538) 0" (2 ^^ (-1075 :: Int))
          check "nextUp 0 / nextUp (nextUp (nextUp 0))" (1 % 3)
          withDouble doubleConfig "atan2 ((1e200 + 1) - 1e200) 1e200" $ \x ->
            estimateOf x >= 1e-200 @? show x
      , testCase "stochastic subnormal products choose both enclosing neighbours"
          $ withDouble doubleConfig{samples = 100} "1e-200 * 1e-200"
          $ \x -> case x.estimate of
            Copies _ cs -> do
              VU.any (== 0) cs @? show cs
              VU.any (> 0) cs @? show cs
            _ -> assertFailure (show x)
      , testCase "determinants preserve bounds, NaN, and each sample" $ do
          check "det [[(1e20 + 1) - 1e20]]" 1
          withDouble doubleConfig "det [[0/0]]" $ \x -> isNaN x.value @? show x
          forM_ [1, 2, 4] $ \k -> do
            let cfg = doubleConfig{samples = 100, cores = k, rounding = S.RoundNearest}
            withDouble cfg "let x = 0 +-s 1 in det [[x]] - x" $ \x -> case x.estimate of
              Copies _ cs -> VU.all (== 0) cs @? show cs
              _ -> assertFailure (show x)
            withDouble cfg "let x = 0 +-s 1 in det [[x,1],[1,0]]" $ \x -> case x.estimate of
              Copies _ cs -> VU.all (== (-1)) cs @? show cs
              _ -> assertFailure (show x)
      , testCase "inverse chooses a usable pivot separately in each copy" $ do
          let s =
                (S.settingsAt 24)
                  { S.samples = 2
                  , S.copies = S.Range 0 2
                  , S.rounding = S.RoundNearest
                  }
              x = Dbl 1 (Copies Drawn (VU.fromList [0, 1])) Nothing
              one = Dbl 1 (ErrorBound 0) Nothing
              zero = Dbl 0 (ErrorBound 0) Nothing
          case S.invertM s 2 [[x, one], [one, zero]] of
            Left err -> assertFailure (show err)
            Right rows -> case (rows !! 1 !! 1).estimate of
              Copies _ cs -> VU.toList cs @?= [0, -1]
              _ -> assertFailure (show rows)
      , testProperty "Berkowitz agrees with the independent permutation formula"
          $ forAll (chooseInt (1, 4))
          $ \n ->
            forAll (vectorOf (n * n) (chooseInt (-3, 3))) $ \entries ->
              within 1_000_000
                $ let rows = [take n (drop (i * n) entries) | i <- [0 .. n - 1]]
                      term permutation =
                        let inversions =
                              length
                                [ ()
                                | (i, a) <- zip [0 :: Int ..] permutation
                                , b <- drop (i + 1) permutation
                                , a > b
                                ]
                         in (if even inversions then 1 else -1)
                              * product [toInteger (rows !! i !! j) | (i, j) <- zip [0 ..] permutation]
                      expected = sum (map term (permutations [0 .. n - 1]))
                      inputs = map (map (\v -> Dbl (fromIntegral v) (ErrorBound 0) Nothing)) rows
                   in case S.determinantM (S.settingsAt 24) n inputs of
                        Left err -> counterexample (show err) False
                        Right x ->
                          counterexample
                            (show (rows, x, expected))
                            (x.value == fromInteger expected && estimateOf x == 0)
      , testCase "sample summaries survive very large and very small finite scales"
          $ forM_ ["1e200", "1e-200"]
          $ \scale ->
            withDouble
              doubleConfig{samples = 100, rounding = S.RoundNearest}
              ("sd (0 +-s " <> scale <> ")")
              $ \x ->
                finite x.value && x.value > 0 @? show x
      , testCase "affine inverse contains independent corner inverses" $ do
          let x =
                A.uncertain 24 Bound (A.Tagged "diagonal" 0) (A.Exact (5 / 2)) (A.Exact (1 / 2))
              matrix = [[x, A.Exact 1], [A.Exact 0, A.Exact 2]]
          case L.invert 24 2 matrix of
            Left err -> assertFailure (show err)
            Right rows -> forM_ [2, 3] $ \a ->
              forM_ (zip (concat rows) [1 / a, -(1 / (2 * a)), 0, 1 / 2]) $ \(value, exact) ->
                abs (A.midpoint value - exact) <= A.radius value @? show value
      , testCase "mean confidence does not replace nominal accuracy" $ do
          withDouble doubleConfig{samples = 10000} "1 + 1e-16" $ \x ->
            estimateOf x >= 5e-17 @? show x
          case runWith doubleConfig{samples = 100} ["1/10"] of
            Right [out] -> "stochastic: mean" `T.isInfixOf` out @? T.unpack out
            other -> assertFailure (show other)
      , testCase "star requires alternation and wedge is alternating" $ do
          case evalP "star [[0,1,0],[0,0,0],[0,0,0]]" of
            Left err -> "alternating" `T.isInfixOf` err @? T.unpack err
            Right value -> assertFailure (show value)
          evalP "let a = [1 +- 0.1,2 +- 0.1,3 +- 0.1] in wedge a a == 0 * wedge a a"
            @?= Right ["true"]
          evalP "star (wedge [1,0,0] [0,1,0])" @?= Right ["[0, 0, 1]"]
      , testCase "Cholesky rejects zero pivots in every position"
          $ forM_ ["[[1,0],[0,0]]", "[[0,0],[0,1]]", "[[0,0],[0,0]]"]
          $ \m -> do
            case evalP ("cholesky " <> m) of
              Left err -> "positive-definite" `T.isInfixOf` err @? T.unpack err
              Right value -> assertFailure (show value)
            case runWith doubleConfig ["cholesky " <> m] of
              Left err -> "positive-definite" `T.isInfixOf` err @? T.unpack err
              Right value -> assertFailure (show value)
      , testCase "asinh is odd and finite at extreme double magnitudes"
          $ forM_ ["1e-200", "1e-10", "1", "1e20", "1e200", "1e308"]
          $ \literal ->
            withDouble doubleConfig ("asinh (-" <> literal <> ")") $ \x -> do
              let expected = asinh (negate (read (T.unpack literal)))
              finite x.value @? show x
              x.value @?= expected
      ]
 where
  check expression exact = withDouble doubleConfig expression (encloses exact)

finite :: Double -> Bool
finite x = not (isNaN x || isInfinite x)

encloses :: Rational -> Dbl -> Assertion
encloses expected x
  | finite x.value && finite (estimateOf x) =
      abs (toRational x.value - expected) <= toRational (estimateOf x) @? show x
  | otherwise = pure ()

withDouble :: Config -> T.Text -> (Dbl -> Assertion) -> Assertion
withDouble cfg expression action = either (assertFailure . T.unpack) action (doubleOf cfg expression)
