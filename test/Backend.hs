{- | Backends (design §8.2): the double backend's arithmetic against GHC's
own, its IEEE cases and literal rounding, its running bound against the
affine backend as the reference, its stochastic estimate, and how a
session chooses a backend.
-}
module Backend (backendTests) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Metron.Affine (Magnitude, midpoint, radius)
import Metron.Codebase (emptyCodebase)
import Metron.Compile (evalValueAs)
import Metron.Double (Dbl (..), digitsOfDbl, estimateOf)
import Metron.Driver (feed)
import Metron.Eval (Config (..), ValueOf (..), defaultConfig)
import Metron.Parser (parseExpr)
import Metron.Scalar (Backend (..), Scalar)
import Metron.Session.Types (Session (..), emptySession)
import Metron.Syntax qualified as S (rootScope)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

backendTests :: TestTree
backendTests =
  testGroup
    "backends (design §8.2)"
    [ ghcTests
    , ieeeTests
    , literalTests
    , printingTests
    , boundTests
    , samplesTests
    ]

-- Running --------------------------------------------------------------------------------

doubleConfig :: Config
doubleConfig = defaultConfig{backend = DoubleBackend}

-- | Lines fed to a fresh session under a configuration.
runWith :: Config -> [Text] -> Either Text [Text]
runWith cfg = go emptySession{config = cfg} []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

runDouble :: [Text] -> Either Text [Text]
runDouble = runWith doubleConfig

-- | One number, evaluated under a backend.
numberAs :: forall s. (Scalar s) => Config -> Text -> Either Text s
numberAs cfg src = do
  e <- parseExpr src
  (_, v) <- evalValueAs @s cfg S.rootScope emptyCodebase src e
  case v of
    VTensor [] _ _ buf | [x] <- V.toList buf -> either (Left . T.pack . show) Right x
    VUnit (VTensor [] _ _ buf) | [x] <- V.toList buf -> either (Left . T.pack . show) Right x
    _ -> Left ("not a number: " <> src)

doubleOf :: Config -> Text -> Either Text Dbl
doubleOf = numberAs @Dbl

-- | The same double: equal bits but for the sign of a NaN.
sameDouble :: Double -> Double -> Bool
sameDouble a b = (isNaN a && isNaN b) || (a == b && isNegativeZero a == isNegativeZero b)

-- GHC's own arithmetic -------------------------------------------------------------------

{- | Each expression, under double, gives exactly the double GHC computes for
the same formula in the same order. The exponents are variables, so that
no rewrite rule for a literal power changes Haskell's order.
-}
ghcTests :: TestTree
ghcTests =
  testGroup
    "results equal GHC's Double"
    [ testCase (T.unpack src) $ case doubleOf doubleConfig src of
        Left err -> assertFailure (T.unpack err)
        Right x ->
          sameDouble x.value expected
            @? (T.unpack src <> ": " <> show x.value <> ", GHC gives " <> show expected)
    | (src, expected) <- cases
    ]
 where
  seven = 7 :: Integer
  three = 3 :: Integer
  ten = 10 :: Integer
  cases :: [(Text, Double)]
  cases =
    [ ("0.1 + 0.2", 0.1 + 0.2)
    , ("(0.1 + 0.2) + 0.3", (0.1 + 0.2) + 0.3)
    , ("0.1 + (0.2 + 0.3)", 0.1 + (0.2 + 0.3))
    , ("1 / 3", 1 / 3)
    , ("2 / 3 * 3 - 2", 2 / 3 * 3 - 2)
    , ("1 - 0.9", 1 - 0.9)
    , ("sqrt 2", sqrt 2)
    , ("sqrt 2 * sqrt 2 - 2", sqrt 2 * sqrt 2 - 2)
    , ("exp 1", exp 1)
    , ("exp 1 - 1", exp 1 - 1)
    , ("log 10", log 10)
    , ("sin (1 rad)", sin 1)
    , ("cos (0.5 rad)", cos 0.5)
    , ("tan (1.2 rad)", tan 1.2)
    , ("asin 0.3", asin 0.3)
    , ("acos 0.3", acos 0.3)
    , ("atan 3", atan 3)
    , ("sinh 1.5", sinh 1.5)
    , ("cosh 1.5", cosh 1.5)
    , ("tanh 0.5", tanh 0.5)
    , ("atan2 1 2", atan2 1 2)
    , ("1.1^7", 1.1 ^ seven)
    , ("1.1^10 - 1", 1.1 ^ ten - 1)
    , ("1.1^-3", 1.1 ^^ negate three)
    , ("(1 + 1e-15) - 1", (1 + 1e-15) - 1)
    , ("1e16 + 1 - 1e16", 1e16 + 1 - 1e16)
    , ("abs (-0.1)", abs (-0.1))
    , ("floor 2.7", 2)
    , ("ceil (-2.5)", -2)
    , ("round 2.5", fromInteger (round (2.5 :: Double)))
    , ("round 3.5", fromInteger (round (3.5 :: Double)))
    , ("pi", pi)
    , ("pi * 2 / 3", pi * 2 / 3)
    ]

-- IEEE 754 ---------------------------------------------------------------------------------

ieeeTests :: TestTree
ieeeTests =
  testGroup
    "IEEE 754: infinities, NaN and overflow are values"
    [ testCase "division by zero is infinite, of either sign" $ do
        (.value) <$> doubleOf doubleConfig "1 / 0" @?= Right (1 / 0)
        (.value) <$> doubleOf doubleConfig "-1 / 0" @?= Right (-(1 / 0))
    , testCase "0/0 and the square root of a negative number are NaN" $ do
        fmap (isNaN . (.value)) (doubleOf doubleConfig "0 / 0") @?= Right True
        fmap (isNaN . (.value)) (doubleOf doubleConfig "sqrt (-1)") @?= Right True
    , testCase "overflow is infinite, not an error" $ do
        (.value) <$> doubleOf doubleConfig "1e300 * 1e10" @?= Right (1 / 0)
        (.value) <$> doubleOf doubleConfig "exp 1000" @?= Right (1 / 0)
    , testCase "underflow is gradual"
        $ (.value) <$> doubleOf doubleConfig "1e-320 / 10" @?= Right (1e-320 / 10)
    , testCase "printing says where the first NaN or infinity appeared" $ do
        runDouble ["1 / 0"] @?= Right ["Infinity (the first infinity came from 1 / 0)"]
        runDouble ["sqrt (-1) + 1"]
          @?= Right ["NaN (the first NaN came from sqrt (-1))"]
        runDouble ["let big = 1e300 * 1e10", "big - big"]
          @?= Right ["NaN (the first NaN came from 1e300 * 10000000000)"]
    , testCase "a comparison with NaN is false, and NaN is not itself" $ do
        runDouble ["0 / 0 < 1", "0 / 0 >= 1", "0 / 0 == 0 / 0", "0 / 0 /= 0 / 0"]
          @?= Right ["false", "false", "false", "true"]
    , testCase "isNaN and isInfinite"
        $ runDouble ["isNaN (0 / 0)", "isNaN 1", "isInfinite (1 / 0)", "isInfinite 1e308"]
          @?= Right ["true", "false", "true", "false"]
    , testCase "eps, nextUp, ulps and fma describe the format" $ do
        runDouble ["eps", "nextUp 1 - 1", "ulps 1 (nextUp (nextUp 1))"]
          @?= Right ["2.220446049250313e-16", "2.220446049250313e-16", "2"]
        -- 0.1·10 − 1 in one rounding is the representation error of 0.1, times 10.
        (.value) <$> doubleOf doubleConfig "fma 0.1 10 (-1)"
          @?= Right 5.551115123125783e-17
    ]

-- Literals ---------------------------------------------------------------------------------

literalTests :: TestTree
literalTests =
  testGroup
    "a literal is rounded to the nearest double where it enters"
    [ testCase "0.1 is the nearest double, its rounding its error" $ case doubleOf doubleConfig "0.1" of
        Left err -> assertFailure (T.unpack err)
        Right x -> do
          x.value @?= 0.1
          let exact = fromRational (abs (toRational (0.1 :: Double) - 1 / 10)) :: Double
          (estimateOf x >= exact && estimateOf x <= exact * (1 + 1e-14) + 1e-300)
            @? ("bound " <> show (estimateOf x) <> " for an error of " <> show exact)
    , testCase "a literal a double holds exactly has no error"
        $ estimateOf <$> doubleOf doubleConfig "0.5" @?= Right 0
    , testCase "the nearest double of a long literal, rounded once"
        $ (.value)
          <$> doubleOf
            doubleConfig
            "0.1000000000000000055511151231257827021181583404541015625"
          @?= Right 0.1
    , testCase "a literal beyond the largest double is infinite"
        $ runDouble ["1e400"]
          @?= Right
            ["Infinity (the first infinity came from a literal beyond the largest double)"]
    ]

-- Printing ---------------------------------------------------------------------------------

printingTests :: TestTree
printingTests =
  testGroup
    "printing labels the kind of estimate"
    [ testCase "an exact result prints alone"
        $ runDouble ["0.5 * 4", "2^10", "1 / 4"] @?= Right ["2", "1024", "0.25"]
    , testCase "a rounded one prints its bound"
        $ expecting (runDouble ["0.1 + 0.2"])
        $ \case
          [out] ->
            ("0.30000000000000004 ± " `T.isPrefixOf` out && " (bound)" `T.isSuffixOf` out)
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase "under samples, the estimate and its count"
        $ expecting (runWith doubleConfig{samples = 3} ["0.1 + 0.2"])
        $ \case
          [out] ->
            ( "0.30000000000000004" `T.isPrefixOf` out
                && " (estimate, 3 samples)" `T.isSuffixOf` out
            )
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase "errorOf and digitsOf, the same under either setting" $ do
        expecting (runDouble ["errorOf 0.5", "digitsOf 0.5"]) $ \outs ->
          outs @?= ["0", "15.954589770191003"]
        expecting (runWith doubleConfig{samples = 3} ["errorOf 0.5", "digitsOf 0.5"]) $ \outs ->
          outs @?= ["0", "15.954589770191003"]
    , testCase "a quantity prints in its unit, an exact one exactly" $ do
        expecting (runDouble ["2 m * 3"]) (@?= ["6 m"])
        expecting (runDouble ["[1, 2] m / 4"]) (@?= ["[0.25, 0.5] m"])
    ]
 where
  expecting r k = either (assertFailure . T.unpack) k r

-- The running bound ------------------------------------------------------------------------

-- | A small arithmetic expression: decimal literals, the four operations, square roots, exponentials.
data Expr
  = Lit Integer Int
  | Op Char Expr Expr
  | Sqrt Expr
  | Exp Integer
  deriving stock (Show)

genExpr :: Int -> Gen Expr
genExpr depth
  | depth <= 0 = leaf
  | otherwise =
      frequency
        [ (2, leaf)
        , (6, Op <$> elements "+-*/" <*> genExpr (depth - 1) <*> genExpr (depth - 1))
        , (1, Sqrt <$> genExpr (depth - 1))
        ]
 where
  leaf =
    frequency
      [ (6, Lit <$> (choose (-9999, 9999) `suchThat` (/= 0)) <*> choose (0, 4))
      , (1, Exp <$> choose (-30, 30))
      ]

renderExpr :: Expr -> Text
renderExpr = \case
  Lit m k -> "(" <> T.pack (show m) <> "e-" <> T.pack (show k) <> ")"
  Op o a b -> "(" <> renderExpr a <> " " <> T.singleton o <> " " <> renderExpr b <> ")"
  Sqrt a -> "sqrt (abs " <> renderExpr a <> ")"
  Exp m -> "exp (" <> T.pack (show m) <> "e-1)"

{- | The bound the double backend carries contains the true error: the
distance from the double to the exact value, which the affine backend
encloses at 24 working digits.
-}
boundTests :: TestTree
boundTests =
  testGroup
    "the running bound contains the true error"
    [ testProperty "against the affine enclosure, over generated arithmetic"
        $ forAll (sized (\n -> genExpr (min 5 (1 + n `div` 20))))
        $ \e ->
          let src = renderExpr e
           in case (numberAs @Magnitude defaultConfig src, doubleOf doubleConfig src) of
                (Left _, _) -> label "the affine backend refuses it" True
                (_, Left err) -> counterexample (T.unpack err) False
                (Right m, Right x)
                  | isNaN x.value || isInfinite x.value -> label "not finite" True
                  | isInfinite (estimateOf x) -> label "unbounded" True
                  | otherwise ->
                      let err = abs (toRational x.value - midpoint m)
                       in counterexample
                            ( T.unpack src
                                <> "\n double "
                                <> show x.value
                                <> " ± "
                                <> show (estimateOf x)
                                <> "\n affine "
                                <> show (fromRational (midpoint m) :: Double)
                                <> " ± "
                                <> show (fromRational (radius m) :: Double)
                            )
                            (err <= toRational (estimateOf x) + radius m)
    , testCase "a cancellation's bound is as large as its result" $ case doubleOf doubleConfig "(1 + 1e-15) - 1" of
        Left err -> assertFailure (T.unpack err)
        Right x -> (estimateOf x > 1e-16 && digitsOfDbl x < 2) @? show (x.value, estimateOf x)
    ]

-- Stochastic arithmetic --------------------------------------------------------------------

samplesTests :: TestTree
samplesTests =
  testGroup
    "samples N: copies under random rounding"
    [ testCase "a cancellation keeps about one digit, at every seed tried"
        $ mapM_
          ( \sd -> case doubleOf doubleConfig{samples = 3, seed = sd} "(1 + 1e-15) - 1" of
              Left err -> assertFailure (T.unpack err)
              Right x ->
                (digitsOfDbl x < 3)
                  @? ("seed " <> show sd <> ": " <> show (digitsOfDbl x) <> " digits")
          )
          [1 .. 8]
    , testCase "a stable sum keeps nearly all its digits" $ case doubleOf doubleConfig{samples = 3} "0.1 + 0.2 + 0.3" of
        Left err -> assertFailure (T.unpack err)
        Right x -> (digitsOfDbl x > 14) @? show (digitsOfDbl x)
    , testCase "the same seed gives the same estimate; the value never changes" $ do
        let run sd =
              runWith
                doubleConfig{samples = 3, seed = sd}
                ["(1 + 1e-15) - 1", "digitsOf ((1 + 1e-15) - 1)"]
        run 7 @?= run 7
        fmap (map (T.takeWhile (/= ' '))) (run 7)
          @?= fmap (map (T.takeWhile (/= ' '))) (run 7)
        fmap (take 1 . map (T.takeWhile (/= ' '))) (run 7)
          @?= fmap (take 1 . map (T.takeWhile (/= ' '))) (run 8)
    , testCase
        "a branch the copies disagree on is flagged, and the IEEE result decides"
        $ case runWith doubleConfig{samples = 10} ["if 1 + 1e-16 > 1 then 1 else 2"] of
          Right [out] ->
            ("2\nwarning: the comparison 1 > 1 goes both ways" `T.isPrefixOf` out)
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase "a stable branch is not"
        $ runWith doubleConfig{samples = 10} ["if 1 + 1e-3 > 1 then 1 else 2"]
          @?= Right ["1"]
    , testCase "under the running bound nothing is flagged"
        $ runDouble ["if 1 + 1e-16 > 1 then 1 else 2"] @?= Right ["2"]
    ]
