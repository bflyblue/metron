module Precision (precisionTests) where

import Data.Ratio ((%))
import Metron.Numerical.Approx qualified as A
import Support.ExactApprox qualified as E
import Test.Tasty
import Test.Tasty.QuickCheck

precisionTests :: TestTree
precisionTests =
  localOption (mkTimeout 30_000_000)
    $ testGroup
      "rational approximation kernels"
      [ check "sqrt" A.sqrtApprox E.sqrtApprox (\x -> abs x + 1 / 100)
      , check "log" A.logApprox E.logApprox (\x -> abs x + 1 / 100)
      , check "exp" A.expApprox E.expApprox id
      , check "atan" A.atanApprox E.atanApprox id
      , check "sin" (\p -> fst . A.sinCosApprox p) (\p -> fst . E.sinCosApprox p) id
      , check "cos" (\p -> snd . A.sinCosApprox p) (\p -> snd . E.sinCosApprox p) id
      , testProperty "integer square root brackets the integer" $ \(NonNegative n) ->
          let x = toInteger (n :: Int); k = A.isqrt x
           in k * k <= x && (k + 1) * (k + 1) > x
      ]
 where
  check name actual reference domain = testProperty name $ forAll (chooseInteger (-50, 50)) $ \n ->
    let x = domain (n % 10)
        (a, ea) = actual 16 x
        (b, eb) = reference 20 x
     in counterexample (show (x, a, ea, b, eb)) (abs (a - b) <= ea + eb)
