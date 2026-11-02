import qualified Data.Vector.Unboxed as V
import Math.NumberTheory.Roots (integerSquareRoot)
import qualified Numeric.Floating.IEEE as IEEE
import Statistics.Distribution (quantile)
import Statistics.Distribution.StudentT (studentT)
import qualified Statistics.Sample as S

main :: IO ()
main = do
  print (IEEE.nextUp (-0.0 :: Double), IEEE.nextDown (0.0 :: Double))
  print (IEEE.fusedMultiplyAdd 0.5 4 1 :: Double)
  print (integerSquareRoot (10 ^ 1000 + 3) == 10 ^ 500)
  print (quantile (studentT 31) 0.975)
  print (S.stdDev (V.fromList [-1e200, 1e200]))
  print (S.stdDev (V.fromList [-1e-200, 1e-200]))
