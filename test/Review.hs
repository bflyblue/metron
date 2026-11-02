module Review (reviewTests) where

import Backend (doubleConfig, doubleOf, runWith)
import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.Text qualified as T
import Data.Vector.Unboxed qualified as VU
import Metron.Double (Dbl (..), Estimate (..))
import Metron.Eval (Config (..))
import Metron.Scalar (Rounding (..))
import Test.Tasty
import Test.Tasty.HUnit

reviewTests :: TestTree
reviewTests =
  localOption (mkTimeout 30_000_000)
    $ testGroup
      "numerical review regressions"
      [ testCase "stochastic residuals retain underflow when FMA residual is zero" $ do
          forM_ ["(2^-537)*(2^-538)", "(0.5^1074)/2", "fma (2^-537) (2^-538) 0"] $ \src ->
            case doubleOf cfg src of
              Left err -> assertFailure (T.unpack err)
              Right x -> case x.estimate of
                Copies _ cs -> do
                  x.value @?= 0
                  VU.all (\v -> v == 0 || v == 5e-324) cs @? show cs
                  VU.any (== 5e-324) cs @? T.unpack ("lost subnormal rounding neighbour: " <> src)
                _ -> assertFailure "missing rounding runs"
      , testCase "negative subnormal products choose negative neighbours"
          $ case doubleOf cfg "(-2^-537)*(2^-538)" of
            Left err -> assertFailure (T.unpack err)
            Right x -> case x.estimate of
              Copies _ cs -> do
                VU.all (\v -> v == 0 || v == (-5e-324)) cs @? show cs
                VU.any (== (-5e-324)) cs @? "lost negative subnormal neighbour"
              _ -> assertFailure "missing runs"
      , testCase "determinants retain sampled zero-nominal entries"
          $ case doubleOf
            doubleConfig{samples = 20}
            "let x = sample (normal 0 1) in det [[x,0],[0,x]]" of
            Left err -> assertFailure (T.unpack err)
            Right x -> case x.estimate of
              Copies _ cs -> VU.all (> 0) cs @? show cs
              _ -> assertFailure "lost determinant samples"
      , testCase "Hodge star rejects a non-alternating matrix"
          $ isLeft (runWith doubleConfig ["star [[1,2],[3,4]]"]) @? "non-alternating input"
      , testCase "Cholesky rejects nonpositive pivots"
          $ isLeft (runWith doubleConfig ["cholesky [[0,0],[0,1]]"]) @? "zero pivot"
      , testCase "large sample statistics do not overflow in intermediate sums"
          $ case runWith doubleConfig{samples = 20} ["sd (sample (uniform (-1e300) 1e300))"] of
            Left err -> assertFailure (T.unpack err)
            Right out -> not (any (T.isInfixOf "Infinity") out) @? show out
      ]
 where
  cfg = doubleConfig{rounding = RoundRandom, roundingSamples = 64}
