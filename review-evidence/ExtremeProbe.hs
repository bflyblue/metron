{-# LANGUAGE OverloadedRecordDot #-}

import Control.Monad
import Data.Ratio
import Metron.Double
import Metron.Scalar

main :: IO ()
main = do
  let s = settingsAt 24
      exps =
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
      rs = [m * 2 ^^ e | e <- exps, m <- [1, 3 % 2, 7 % 5]] :: [Rational]
      finite d = not (isNaN d || isInfinite d)
      check label expected got =
        let z = got.value; b = estimateOf got
         in if finite z && finite b && abs (toRational z - expected) > toRational b
              then Just (label, z, b, fromRational (abs (toRational z - expected)) :: Double)
              else Nothing
      results =
        [ r
        | a <- rs
        , b <- rs
        , (name, wanted, got) <-
            [ ("+", a + b, Right (addM s (literal s a) (literal s b)))
            , ("*", a * b, Right (mulM s (literal s a) (literal s b)))
            , ("/", a / b, divM s (literal s a) (literal s b))
            ]
        , Right x <- [got]
        , Just r <- [check (name, show a, show b) wanted (x :: Dbl)]
        ]
  putStrLn ("Violations: " ++ show (length results))
  mapM_ print (take 12 results)
