{- | Backends (design §8.2): the double backend's arithmetic against GHC's
own, its IEEE cases and literal rounding, its running bound against the
affine backend as the reference, its stochastic estimate, and how a
session chooses a backend.
-}
module Backend (backendTests) where

import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Metron.Affine (Magnitude, midpoint, radius)
import Metron.Batch (batchesOf)
import Metron.Codebase (Codebase (..), Reference (..), emptyCodebase)
import Metron.Compile (evalBatchedAs, evalValueAs)
import Metron.Double (Dbl (..), Estimate (..), digitsOfDbl, estimateOf)
import Metron.Driver (feed, seededSession, startBackend, startSettings)
import Metron.Eval (Config (..), ValueOf (..), defaultConfig)
import Metron.Limits (Limits (..))
import Metron.Needs (needsOf)
import Metron.Parser (parseExpr)
import Metron.Scalar (Backend (..), Batch (..), Rounding (..), Scalar)
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
    , switchingTests
    , checkTests
    , settingTests
    , monteCarloTests
    , coresTests
    ]

-- The check before running ----------------------------------------------------------------

checkTests :: TestTree
checkTests =
  testGroup
    "built-ins a backend lacks are refused before running"
    [ testCase "the refusal names the path through the definitions"
        $ expectLeft
          "`orbitError` uses `sd` (through `budgetOf`), which needs `:set samples N` under the double backend"
          ( runDouble
              [ "let budgetOf x = sd x"
              , "let orbitError x = budgetOf x * 2"
              , "orbitError 1"
              ]
          )
    , testCase "and down a longer chain to the definition that uses it"
        $ expectLeft
          "`a` uses `errorOf` (through `b`, `c`), which the affine backend does not have"
          ( runWith
              defaultConfig
              ["let c x = errorOf x", "let b x = c x + 1", "let a x = b x * 2", "a 1"]
          )
    , testCase
        "a definition that uses one is entered under either backend; using it is refused"
        $ expectLeft
          "`g` uses `sd`"
          (runDouble ["let g x = sd x", "let k = 1", "k + 1", "g 1"])
    , testCase "an input whose closure is clean runs"
        $ runDouble ["let budgetOf x = sd x", "let twice x = x * 2", "twice 0.25"]
          @?= Right ["0.5"]
    , testCase "the check is conservative: a branch never taken counts"
        $ do
          expectLeft
            "`sd` needs `:set samples N` under the double backend"
            (runDouble ["if false then sd 1 else 0"])
          expectLeft
            "`bound` is the affine backend's"
            (runWith doubleConfig{samples = 10} ["if false then bound 1 else 0"])
    , testCase "so is a definition the input never calls but refers to"
        $ expectLeft
          "`pick` uses `gauss` (through `unused`), which needs `:set samples N` under the double backend"
          ( runDouble
              ["let unused = gauss 1", "let pick b = if b then 1 else unused.0", "pick true"]
          )
    , testCase "a recursive group is one union"
        $ expectLeft
          "`ev` uses `±`"
          ( runDouble
              [ "let ev n = if n == 0 then 1 else od (n - 1)\nlet od n = if n == 0 then 1 ± 0.1 else ev (n - 1)"
              , "ev 4"
              ]
          )
    , testCase
        "the memo holds names, not backends: the same session switches back and forth"
        $ runWith
          defaultConfig
          [ "let budgetOf x = sd (x ±σ 0.1)"
          , "budgetOf 1"
          , ":backend double"
          , ":backend affine"
          , "budgetOf 2"
          ]
          @?= Right ["0.1", "0.1"]
    , testCase "needs(h) is memoised by hash, and answers without the term"
        $ case sessionAfter
          defaultConfig
          ["let budgetOf x = sd (x ±σ 0.1)", "let twice x = budgetOf x * 2", "twice 1"] of
          Left err -> assertFailure (T.unpack err)
          Right s -> case (Map.lookup "budgetOf" s.staging.names, Map.lookup "twice" s.staging.names) of
            (Just b, Just t) -> do
              fst (needsOf Map.empty b.hash s.needs) @?= Set.fromList ["sd", "±σ"]
              fst (needsOf Map.empty t.hash s.needs) @?= Set.fromList ["sd", "±σ"]
            _ -> assertFailure "no definitions"
    , testCase "after switching, the memo refuses what it allowed before"
        $ expectLeft
          "`budgetOf` uses `sd`, which needs `:set samples N` under the double backend"
          ( runWith
              defaultConfig
              [ "let budgetOf x = sd (x ±σ 0.1)"
              , "budgetOf 1"
              , ":backend double"
              , "budgetOf 2"
              ]
          )
    ]

-- Choosing a backend -----------------------------------------------------------------------

switchingTests :: TestTree
switchingTests =
  testGroup
    ":backend chooses the evaluator of the scalars"
    [ testCase ":backend names the current one and switches"
        $ runWith
          defaultConfig
          [":backend", "0.5 + 0.25", ":backend double", ":backend", "0.1 + 0.2 == 0.3"]
          @?= Right ["affine", "0.75", "double", "false"]
    , testCase "the same expression under each"
        $ runWith
          defaultConfig
          [ "0.1 + 0.2 == 0.3"
          , ":backend double"
          , "0.1 + 0.2 == 0.3"
          , ":backend affine"
          , "0.1 + 0.2 == 0.3"
          ]
          @?= Right ["true", "false", "true"]
    , testCase "--backend starts a session under one, as :backend would" $ do
        case startBackend "double" emptySession of
          Left err -> assertFailure (T.unpack err)
          Right s -> do
            s.config.backend @?= DoubleBackend
            fmap snd (feed s ":backend") @?= Right ["double"]
        case startBackend "quad" emptySession of
          Left err -> err @?= "no backend quad; the backends are affine and double"
          Right _ -> assertFailure "quad accepted"
    , testCase "an unknown backend is refused"
        $ expectLeft
          "no backend single; the backends are affine and double"
          (runWith defaultConfig [":backend single"])
    , testCase ":exact, :budget and :covariance are the affine backend's"
        $ mapM_
          ( \c ->
              expectLeft
                (":" <> c <> " is the affine backend's; the double backend does not have it")
                (runDouble [":" <> c <> " 1"])
          )
          ["exact", "budget", "covariance"]
    , testCase
        "the affine backend's built-ins are refused under double, ± at every setting"
        $ do
          expectLeft
            "`±` is the affine backend's; the double backend does not have it"
            (runDouble ["1 ± 0.1"])
          expectLeft
            "`±` is the affine backend's; the double backend does not have it"
            (runWith doubleConfig{samples = 10} ["1 ± 0.1"])
          expectLeft
            "`bound` is the affine backend's"
            (runWith doubleConfig{samples = 10} ["bound 1"])
          expectLeft
            "`covariance` is the affine backend's"
            (runWith doubleConfig{samples = 10} ["covariance [1, 2]"])
    , testCase
        "noise is refused under double at every setting, as ± is; gauss is drawn"
        $ do
          let lacking = "`noise` is the affine backend's; the double backend does not have it"
          expectLeft lacking (runDouble ["noise 2"])
          expectLeft lacking (runWith doubleConfig{samples = 10} ["noise 2"])
          expectLeft lacking (runWith monteCarlo ["1 + 0.1 * (noise 1).0"])
          -- before running, through a definition
          expectLeft
            "`spread` uses `noise`, which the double backend does not have"
            ( runWith
                doubleConfig{samples = 10}
                ["let spread x = x + (noise 1).0", "spread 1"]
            )
          (length <$> runWith doubleConfig{samples = 10} ["gauss 2"]) @?= Right 1
    , testCase "the declared σ, gauss, mid and sd need samples under double" $ do
        expectLeft
          "`sd` needs `:set samples N` under the double backend"
          (runDouble ["sd 1"])
        expectLeft
          "`mid` needs `:set samples N` under the double backend"
          (runDouble ["mid 1"])
        expectLeft
          "`±σ` needs `:set samples N` under the double backend"
          (runDouble ["1 ±σ 0.1"])
        expectLeft "`gauss` needs `:set samples N`" (runDouble ["gauss 2"])
        runWith doubleConfig{samples = 10} ["sd 1", "mid 0.5"] @?= Right ["0", "0.5"]
    , testCase "the double backend's are refused under affine" $ do
        expectLeft
          "`errorOf` is the double backend's; the affine backend does not have it"
          (runWith defaultConfig ["errorOf 1"])
        expectLeft "`eps` is the double backend's" (runWith defaultConfig ["eps"])
    , testCase ":set samples takes 0 or at least two copies" $ do
        expectLeft "samples is 0" (runWith defaultConfig [":set samples 1"])
        runWith
          defaultConfig
          [":set samples 5", ":set seed 9", ":backend double", "1 / 4"]
          @?= Right ["0.25"]
    ]

-- | An error that says the given thing.
expectLeft :: Text -> Either Text [Text] -> Assertion
expectLeft needle = \case
  Left err -> T.isInfixOf needle err @? T.unpack err
  Right out ->
    assertFailure
      ("expected an error containing " <> T.unpack needle <> ", got " <> show out)

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

-- | The session after some lines.
sessionAfter :: Config -> [Text] -> Either Text Session
sessionAfter cfg = foldM (\s l -> fst <$> feed s l) emptySession{config = cfg}

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
    , testCase ":set seed: the same seed gives the same estimate, others others" $ do
        let run sd =
              runWith
                defaultConfig
                [ ":set samples 3"
                , ":set seed " <> sd
                , ":backend double"
                , "0.1 + 0.2 + 0.3 + 0.4 + 0.7 - 1.7"
                ]
            seeds = map (T.pack . show) [1 .. 8 :: Int]
        run "7" @?= run "7"
        case mapM run seeds of
          Left err -> assertFailure (T.unpack err)
          Right outs -> do
            let values = [T.takeWhile (/= ' ') o | o <- concat outs]
                estimates = [T.dropWhile (/= '±') o | o <- concat outs]
            -- The value is the IEEE result whatever the seed; the estimate is not.
            length (filter (/= "0") values) @?= 0
            (length (Set.fromList estimates) > 1) @? show estimates
    , testCase "at samples 3, the unstable branch of the default seed is flagged"
        $ case runWith
          defaultConfig
          [":set samples 3", ":backend double", "if 1 + 1e-16 > 1 then 1 else 2"] of
          Right [out] ->
            ( "2\nwarning: the comparison 1 > 1 goes both ways across the 3 samples"
                `T.isPrefixOf` out
            )
              @? T.unpack out
          other -> assertFailure (show other)
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

-- The settings of the copies --------------------------------------------------------------

settingTests :: TestTree
settingTests =
  testGroup
    ":set samples, seed and rounding, and --set"
    [ testCase "samples goes up to 10⁵, and one copy has no spread" $ do
        fmap (.config.samples) (sessionAfter defaultConfig [":set samples 100000"])
          @?= Right 100000
        expectLeft
          "from 2 to 100000 copies"
          (runWith defaultConfig [":set samples 100001"])
        expectLeft "from 2 to 100000 copies" (runWith defaultConfig [":set samples 1"])
    , testCase ":set rounding is nearest or random, random by default" $ do
        ( elem "rounding nearest"
            <$> runWith defaultConfig [":set rounding nearest", ":set"]
          )
          @?= Right True
        (elem "rounding random" <$> runWith defaultConfig [":set"]) @?= Right True
        expectLeft
          "rounding is nearest or random"
          (runWith defaultConfig [":set rounding up"])
    , testCase
        "rounding nearest: copies with no draws are the IEEE result, and print exact"
        $ case doubleOf doubleConfig{samples = 10, rounding = RoundNearest} "0.1 + 0.2 * 3" of
          Left err -> assertFailure (T.unpack err)
          Right x -> do
            x.estimate @?= Copies (VU.replicate 10 x.value)
            estimateOf x @?= 0
    , testCase "rounding random: the same copies do differ"
        $ case doubleOf doubleConfig{samples = 10} "0.1 + 0.2 * 3" of
          Left err -> assertFailure (T.unpack err)
          Right x -> (estimateOf x > 0) @? show x
    , testCase "rounding has no effect under samples 0"
        $ runWith doubleConfig{rounding = RoundNearest} ["0.1 + 0.2"]
          @?= runDouble ["0.1 + 0.2"]
    , testCase "--set takes samples, seed and rounding, in order" $ do
        let started =
              startSettings
                [("samples", "1000"), ("seed", "5"), ("rounding", "nearest"), ("seed", "6")]
                defaultConfig
        fmap (\c -> (c.samples, c.seed, c.rounding)) started
          @?= Right (1000, 6, RoundNearest)
    , testCase "--set refuses what :set refuses, and names an unknown setting" $ do
        expectLeft
          "from 2 to 100000"
          ([] <$ startSettings [("samples", "1")] defaultConfig)
        expectLeft
          "--set: no setting colour"
          ([] <$ startSettings [("colour", "on")] defaultConfig)
    , testCase "--set still takes the limits"
        $ fmap (.limits.steps) (startSettings [("steps", "500")] defaultConfig)
          @?= Right 500
    ]

-- Declared σ, sampled: Monte Carlo ------------------------------------------------------

{- | Monte Carlo under double (design §8.2): declared σ drawn in each copy.
The tolerances are five standard errors of the statistic at the sample
size, derived, not tuned: the mean's is @σ/√N@; a normal sample's
deviation's is @σ/√(2(N−1))@; for @n²@, @n@ standard normal, whose fourth
central moment is 60 and variance 2, @Var(s²) ≈ (60 − 4)/N@, so the
deviation's is @√(56/N)/(2√2)@. The draws are fixed by the seed, so each
check is deterministic; the tolerance says how far an honest sampler may
stray at any seed.
-}
monteCarloTests :: TestTree
monteCarloTests =
  testGroup
    "declared σ is sampled: Monte Carlo under double"
    [ testCase
        "a nearly linear formula: the orbital period with CODATA's G agrees with affine's σ"
        $ agreesWithAffine
          [ "let M = 5.9722e24 kg ±σ 6e20 kg"
          , "let T = 2 * pi * sqrt ((7000 km)^3 / (astro.G * M))"
          ]
          "T"
    , testCase "a product of small-σ values agrees with affine's σ"
        $ agreesWithAffine ["let a = 3 ±σ 0.01", "let b = 5 ±σ 0.02"] "a * b"
    , testCase "a non-linear value: n·n for n = 0 ±σ 1 has mean 1 and deviation √2" $ do
        expectLeft
          "non-linear"
          (runWith defaultConfig ["let n = 0 ±σ 1", "sd (n * n)"])
        case mapM
          (doubleOf monteCarlo)
          ["mid (let n = 0 ±σ 1 in n * n)", "sd (let n = 0 ±σ 1 in n * n)"] of
          Right [m, s] -> do
            let se = sqrt (56 / 10000) / (2 * sqrt 2)
            (abs (m.value - 1) <= 5 * sqrt 2 / 100) @? ("mean " <> show m.value)
            (abs (s.value - sqrt 2) <= 5 * se) @? ("sd " <> show s.value)
          other -> assertFailure (show other)
    , testCase "the shown value is the IEEE result at the nominal inputs"
        $ fmap (.value) (doubleOf monteCarlo "let n = 0.5 ±σ 1 in n * n + 0.1")
          @?= Right (0.5 * 0.5 + 0.1)
    , testCase "x - x is exactly 0 in every copy, under either rounding" $ do
        let zeroCopies cfg = case doubleOf cfg "let x = 1 ±σ 0.1 in (x * 3 + 1) - (x * 3 + 1)" of
              Right x -> x.estimate @?= Copies (VU.replicate cfg.samples 0)
              Left err -> assertFailure (T.unpack err)
        zeroCopies monteCarlo
        zeroCopies monteCarlo{rounding = RoundRandom}
    , testCase "the same unknown is one draw across definitions, by its identity"
        $ runWith monteCarlo ["let x = 2 ±σ 0.1", "let y = x * 2", "sd (y - 2 * x)"]
          @?= Right ["0"]
    , testCase "two independent ±σ values are independent" $ do
        case copiesIn monteCarlo "let a = 1 ±σ 1 in let b = 1 ±σ 1 in [a, b]" of
          Right [as, bs] -> do
            let r = correlation as bs
            (abs r <= 5 / sqrt 10000) @? ("correlation " <> show r)
          other -> assertFailure (show other)
        case doubleOf monteCarlo "sd (let a = 1 ±σ 1 in let b = 1 ±σ 1 in a - b)" of
          Right s -> (abs (s.value - sqrt 2) <= 5 * sqrt 2 / sqrt (2 * 9999)) @? show s.value
          Left err -> assertFailure (T.unpack err)
    , testCase "gauss draws standard normals, independent across components"
        $ case copiesIn monteCarlo "gauss 2" of
          Right [as, bs] -> do
            (abs (mean as) <= 5 / 100) @? show (mean as)
            (abs (deviation as - 1) <= 5 / sqrt (2 * 9999)) @? show (deviation as)
            (abs (correlation as bs) <= 5 / 100) @? show (correlation as bs)
          other -> assertFailure (show other)
    , testCase "a labelled unknown is one draw wherever the label appears"
        -- Independent, the difference would spread by √2 · 0.1; one draw
        -- leaves only the roundings of the two sums.
        $ case doubleOf monteCarlo "sd ((5 ±σ 0.1 #s7) - (3 ±σ 0.1 #s7))" of
          Right s -> (s.value < 1e-15) @? show s.value
          Left err -> assertFailure (T.unpack err)
    , testCase "the same seed gives the same copies; another seed, others" $ do
        let at sd = (.estimate) <$> doubleOf monteCarlo{seed = sd} "let x = 1 ±σ 0.1 in x * x"
        at 4 @?= at 4
        (at 4 /= at 5) @? "seeds 4 and 5 drew alike"
    , testCase "the draws do not depend on the order things are forced in" $ do
        let outs =
              runWith
                monteCarlo
                [ "let x = 1 ±σ 0.1"
                , "let y = 7 ±σ 0.3"
                , "[mid x, sd x]"
                , "[mid y, sd y, mid x, sd x]"
                , "[sd (y * x), sd x]"
                ]
            items = T.splitOn ", " . T.dropAround (`elem` ['[', ']'])
        case outs of
          Right [a, b, c] -> do
            drop 2 (items b) @?= items a
            drop 1 (items c) @?= drop 1 (items a)
          other -> assertFailure (show other)
    , testCase
        "rounding random adds rounding to the draws; nearest leaves the draws alone"
        $ do
          let at r = (.estimate) <$> doubleOf monteCarlo{rounding = r} "let x = 1 ±σ 0.1 in x / 3"
          (at RoundNearest /= at RoundRandom) @? "the roundings agree"
          case (at RoundNearest, at RoundRandom) of
            (Right (Copies ns), Right (Copies rs)) ->
              VU.all (<= 2.3e-16) (VU.zipWith (\n r -> abs (n - r)) ns rs)
                @? "a copy moved more than a rounding"
            other -> assertFailure (show other)
    , testCase "mid and sd under samples 0 are refused, naming the setting"
        $ expectLeft
          "`sd` needs `:set samples N` under the double backend"
          (runDouble ["let x = 1", "sd x"])
    , testCase "the definitions that were refused run once samples are set"
        $ runWith
          doubleConfig
          ["let budgetOf x = sd (x ±σ 0.1)", ":set samples 2", "budgetOf 1 < 1"]
          @?= Right ["true"]
    , testCase "a bound ± stays refused with samples, through definitions too"
        $ expectLeft
          "`ev` uses `±`"
          ( runWith
              monteCarlo
              [ "let ev n = if n == 0 then 1 else od (n - 1)\nlet od n = if n == 0 then 1 ± 0.1 else ev (n - 1)"
              , "ev 4"
              ]
          )
    ]
 where
  mean cs = VU.sum cs / fromIntegral (VU.length cs)
  deviation cs =
    let m = mean cs
     in sqrt
          ( VU.sum (VU.map (\c -> (c - m) ^ (2 :: Int)) cs)
              / fromIntegral (VU.length cs - 1)
          )
  correlation as bs =
    let ma = mean as
        mb = mean bs
        cov = VU.sum (VU.zipWith (\a b -> (a - ma) * (b - mb)) as bs)
     in cov
          / sqrt (VU.sum (VU.map (\a -> (a - ma) ^ (2 :: Int)) as))
          / sqrt (VU.sum (VU.map (\b -> (b - mb) ^ (2 :: Int)) bs))

-- | Pure Monte Carlo: 10⁴ copies rounded to nearest.
monteCarlo :: Config
monteCarlo = doubleConfig{samples = 10000, rounding = RoundNearest}

{- | Affine's first-order σ of an expression, after some definitions in the
seeded session, against double's sample deviation and mean at 10⁴
copies rounded to nearest: within five standard errors.
-}
agreesWithAffine :: [Text] -> Text -> Assertion
agreesWithAffine defs expr =
  case seededLines
    ( defs
        ++ ["sd (" <> expr <> ")", "mid (" <> expr <> ")"]
        ++ [":set samples 10000", ":set rounding nearest", ":backend double"]
        ++ ["sd (" <> expr <> ")", "mid (" <> expr <> ")"]
    ) of
    Left err -> assertFailure (T.unpack err)
    Right outs -> case mapM leading outs of
      Just [sigma, nominal, s, m] -> do
        let n = 10000 :: Double
        (abs (s / sigma - 1) <= 5 / sqrt (2 * (n - 1)))
          @? ("sd " <> show s <> " against affine's " <> show sigma)
        (abs (m - nominal) <= 5 * sigma / sqrt n)
          @? ("mean " <> show m <> " against " <> show nominal)
      _ -> assertFailure (show outs)
 where
  leading t = case reads (T.unpack (T.takeWhile (`notElem` [' ', '…']) t)) of
    [(x, "")] -> Just (x :: Double)
    _ -> Nothing

-- | Lines fed to the seeded session, with the standard library.
seededLines :: [Text] -> Either Text [Text]
seededLines ls = do
  s0 <- seededSession
  let go _ acc [] = Right (concat (reverse acc))
      go s acc (l : rest) = do
        (s', outs) <- feed s l
        go s' (outs : acc) rest
  go s0 [] ls

-- | The copies of each component of a vector, under a configuration.
copiesIn :: Config -> Text -> Either Text [VU.Vector Double]
copiesIn cfg src = do
  e <- parseExpr src
  (_, v) <- evalValueAs @Dbl cfg S.rootScope emptyCodebase src e
  vectorCopies src v

-- | The copies of each component of a vector.
vectorCopies :: Text -> ValueOf Dbl -> Either Text [VU.Vector Double]
vectorCopies src = \case
  VTensor [_] _ _ buf ->
    traverse
      ( \case
          Right x | Copies cs <- x.estimate -> Right cs
          other -> Left (T.pack (show other))
      )
      (V.toList buf)
  _ -> Left ("not a vector: " <> src)

-- The copies in parallel batches ---------------------------------------------------------

{- | @:set cores K@ (design §8.2): the copies run in K batches, each a whole
evaluation, and merge into what one evaluation gives, bit for bit.
-}
coresTests :: TestTree
coresTests =
  testGroup
    ":set cores: the copies in parallel batches"
    [ testCase
        "batches of the copies: in order, sizes within one, at least two copies each"
        $ do
          map (\b -> (b.first, b.count)) (batchesOf 10 4)
            @?= [(0, 3), (3, 3), (6, 2), (8, 2)]
          length (batchesOf 10 32) @?= 5
          batchesOf 7 1 @?= [Batch{first = 0, count = 7, batches = 1}]
    , testProperty "the batches cover the copies exactly, in order"
        $ \(Positive n) (Positive k) ->
          let bs = batchesOf n k
           in concatMap (\b -> [b.first .. b.first + b.count - 1]) bs == [0 .. n - 1]
                && all (\b -> b.batches == length bs) bs
    , testCase
        "K = 1, 2 and 4 give the same copies, bit for bit, and the same statistics"
        $ do
          let src =
                "let x = 1 ±σ 0.1 in let y = 2 ±σ 0.3 in [x * y / 3, sin (x * 1 rad) + y, if x > 0.9 then x else y]"
              at k = case copiesBatched batchedConfig{cores = k} src of
                Right (Just cs) -> pure cs
                other -> assertFailure (show other) >> pure []
          one <- at 1
          two <- at 2
          four <- at 4
          two @?= one
          four @?= one
          map stats four @?= map stats one
          -- and the same as the evaluation that never batches
          (map (.estimate) <$> numbersIn batchedConfig src) @?= Right (map Copies one)
    , testCase "under random rounding too, with no declared σ" $ do
        let src = "[0.1 + 0.2 * 3, sqrt 2 / 3, exp 0.3]"
            at k = copiesBatched batchedConfig{cores = k, rounding = RoundRandom} src
        at 4 @?= at 1
        (isJust <$> at 4) @?= Right True
    , testCase
        "an input that reads across the copies runs as one, with the same result"
        $ do
          let ls = ["let x = 1 ±σ 0.1", "[mid (x * x), sd (x * x), errorOf x]"]
          runWith batchedConfig{cores = 4} ls @?= runWith batchedConfig{cores = 1} ls
    , testCase "the batches' warnings come together" $ do
        let ls = ["if 1 + 1e-16 > 1 then 1 else 2"]
            outs k = runWith doubleConfig{samples = 10, cores = k} ls
        outs 4 @?= outs 1
        -- Two, in the order one evaluation makes them, whichever batch
        -- makes each first.
        let two k =
              runWith
                doubleConfig{samples = 6, cores = k}
                [ "[if 2 + 3e-16 > 2 then 1 else 2, if 1 + 1e-16 > 1 then 1 else 2, if 4 - 4e-16 < 4 then 1 else 2]"
                ]
        two 3 @?= two 1
        two 2 @?= two 1
        case outs 4 of
          Right [out] ->
            ( "warning: the comparison 1 > 1 goes both ways across the 10 samples"
                `T.isInfixOf` out
            )
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase "steps applies to each batch: accepted alike at every K" $ do
        let ls k steps =
              [ "let go n acc = if n == 0 then acc else go (n - 1) (acc + 1)"
              , ":set steps " <> T.pack (show (steps :: Int))
              , ":set cores " <> T.pack (show (k :: Int))
              , "go 1000 0"
              ]
            run k steps = runWith doubleConfig{samples = 8} (ls k steps)
        -- `go 1000 0` takes between 5000 and 20000 steps: under a count of
        -- all batches together, 20000 ran at K = 1 and was refused at K = 4.
        run 1 20000 @?= Right ["1000"]
        run 4 20000 @?= Right ["1000"]
        expectLeft "took more than 5000 steps" (run 1 5000)
        expectLeft "took more than 5000 steps" (run 4 5000)
    , testCase ":set cores and --set cores take a positive count" $ do
        (elem "cores 1" <$> runWith defaultConfig [":set"]) @?= Right True
        fmap (.config.cores) (sessionAfter defaultConfig [":set cores 4"]) @?= Right 4
        expectLeft
          "cores must be a positive integer"
          (runWith defaultConfig [":set cores 0"])
        fmap (.cores) (startSettings [("cores", "3")] defaultConfig) @?= Right 3
    , testCase "affine and samples 0 never batch"
        $ runWith defaultConfig{cores = 4} ["1 / 3 + 1"]
          @?= runWith defaultConfig ["1 / 3 + 1"]
    ]
 where
  stats cs =
    let n = fromIntegral (VU.length cs)
        m = VU.sum cs / n
     in (m, sqrt (VU.sum (VU.map (\c -> (c - m) * (c - m)) cs) / (n - 1)))

-- | Monte Carlo at 1000 copies, rounding to nearest, to batch.
batchedConfig :: Config
batchedConfig = doubleConfig{samples = 1000, rounding = RoundNearest}

-- | The copies of each component of a vector, evaluated in batches.
copiesBatched :: Config -> Text -> Either Text (Maybe [VU.Vector Double])
copiesBatched cfg src = do
  e <- parseExpr src
  r <- evalBatchedAs cfg S.rootScope emptyCodebase src e
  case r of
    Nothing -> Right Nothing
    Just (Left err) -> Left (T.pack (show err))
    Just (Right v) -> Just <$> vectorCopies src v

-- | The numbers of a vector, evaluated as one.
numbersIn :: Config -> Text -> Either Text [Dbl]
numbersIn cfg src = do
  e <- parseExpr src
  (_, v) <- evalValueAs @Dbl cfg S.rootScope emptyCodebase src e
  case v of
    VTensor [_] _ _ buf -> traverse (either (Left . T.pack . show) Right) (V.toList buf)
    _ -> Left ("not a vector: " <> src)
