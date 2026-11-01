{- | Backends (design §8.2): the double backend's arithmetic against GHC's
own, its IEEE cases and literal rounding, its running bound against the
affine backend as the reference, its stochastic estimate, and how a
session chooses a backend.
-}
module Backend (backendTests) where

import Control.Monad (foldM)
import Data.Foldable (for_)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Metron.Affine (Decide (..), Magnitude, midpoint, radius)
import Metron.Batch (batchesOf)
import Metron.Codebase (Codebase (..), Reference (..), emptyCodebase)
import Metron.Compile (evalBatchedAs, evalValueAs)
import Metron.Double (
  Dbl (..),
  Estimate (..),
  Spread (..),
  digitsOfDbl,
  estimateOf,
  showDouble,
  showSampled,
 )
import Metron.Driver (feed, seededSession, startBackend, startSettings)
import Metron.Eval (Config (..), ValueOf (..), defaultConfig, precisionOf)
import Metron.Limits (Limits (..))
import Metron.Needs (needsOf)
import Metron.Parser (parseExpr)
import Metron.Scalar (
  Backend (..),
  Batch (..),
  Rounding (..),
  Scalar,
  settingsAt,
 )
import Metron.Scalar qualified as Scalar (Settings (..))
import Metron.Session.Types (Session (..), emptySession)
import Metron.Syntax qualified as S (rootScope)
import Numeric (showFFloat)
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
    , tableTests
    , splitTests
    , mixtureTests
    , switchingTests
    , checkTests
    , settingTests
    , monteCarloTests
    , monteCarloPrintingTests
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
    , testCase "at samples 3, the unstable branch of the default seed has its table"
        $ runWith
          defaultConfig
          [":set samples 3", ":backend double", "if 1 + 1e-16 > 1 then 1 else 2"]
          @?= Right
            [ "2\n"
                <> ifTable "warning" "1 + 1e-16 > 1" "3 samples (lost in rounding" (1, 2) False
            ]
    , testCase
        "a branch the copies disagree on has its table, and the nominal result decides"
        $ runWith doubleConfig{samples = 10} ["if 1 + 1e-16 > 1 then 1 else 2"]
          @?= Right
            [ "2\n"
                <> ifTable "warning" "1 + 1e-16 > 1" "10 samples (lost in rounding" (7, 3) False
            ]
    , testCase "a stable branch has none"
        $ runWith doubleConfig{samples = 10} ["if 1 + 1e-3 > 1 then 1 else 2"]
          @?= Right ["1"]
    , testCase "under the running bound nothing has a table"
        $ runDouble ["if 1 + 1e-16 > 1 then 1 else 2"] @?= Right ["2"]
    ]

-- The table at a branch point ------------------------------------------------------------

{- | A branch point whose copies would choose otherwise than the branch
taken has a table (design §8.2, "Branches under copies"): a row for each
alternative counting the copies whose own scrutinee selects it, summed
over every batch, so the same at every @cores@. Where the copies carry
draws they split there, and the table is a note.
-}
tableTests :: TestTree
tableTests =
  testGroup
    "the table at a branch point"
    [ testCase "a row counts the copies whose own scrutinee selects its alternative" $ do
        cs <- copiesAfter batchedConfig defs "x"
        let held = VU.length (VU.filter (> 0.9) cs)
        (held > 0 && held < 1000) @? show held
        tablesOf (runWith batchedConfig (defs <> ["if x > 0.9 then 1 else 2"]))
          @?= Right [drawn "x > 0.9" "1000 samples" (held, 1000 - held) True]
    , testCase "an if and a case on its condition give the same table" $ do
        let at k e = runWith batchedConfig{cores = k} (defs <> [e])
        at 1 "case x > 0.9 of true -> 1; false -> 2" @?= at 1 "if x > 0.9 then 1 else 2"
        at 4 "case x > 0.9 of true -> 1; false -> 2" @?= at 1 "if x > 0.9 then 1 else 2"
    , testCase
        "the same at 1, 2 and 4 cores, with batches whose copies all agree"
        $ do
          cs <- copiesAfter batchedConfig defs "x"
          -- Only the smallest copy fails x > m, so at 4 cores three batches'
          -- copies all agree with the nominal branch: they count all the same.
          let m = VU.minimum cs
              held = VU.length (VU.filter (> 0.9) cs)
              slices = [VU.slice b.first b.count cs | b <- batchesOf 1000 4]
              src =
                "[if x > "
                  <> showDouble m
                  <> " then 1 else 2, if x > 0.9 then 1 else 2]"
              at k = runWith batchedConfig{cores = k} (defs <> [src])
          length (filter (VU.all (> m)) slices) @?= 3
          -- and the batches do run, and merge
          mergesAfter batchedConfig{cores = 4} defs src @?= Right True
          tablesOf (at 1)
            @?= Right
              [ drawn ("x > " <> showDouble m) "1000 samples" (999, 1) True
              , drawn "x > 0.9" "1000 samples" (held, 1000 - held) True
              ]
          at 2 @?= at 1
          at 4 @?= at 1
    , testCase "two branch points with the same condition are two tables" $ do
        cs <- copiesAfter batchedConfig defs "x"
        let held = VU.length (VU.filter (> 0.9) cs)
            at k =
              runWith
                batchedConfig{cores = k}
                (defs <> ["[if x > 0.9 then 1 else 2, if x > 0.9 then 3 else 4]"])
            table = drawn "x > 0.9" "1000 samples" (held, 1000 - held) True
        tablesOf (at 1) @?= Right [table, table]
        at 4 @?= at 1
    , testCase "a branch point reached twice counts both evaluations" $ do
        cs <- copiesAfter batchedConfig defs "x"
        let held = VU.length (VU.filter (> 0.9) cs)
            at k =
              runWith
                batchedConfig{cores = k}
                (defs <> ["let f z = if z > 0.9 then 1 else 0", "f x + f x"])
        tablesOf (at 1)
          @?= Right
            [ drawn
                "z > 0.9"
                "2 evaluations × 1000 samples"
                (2 * held, 2 * (1000 - held))
                True
            ]
        at 4 @?= at 1
    , testCase "a branch point in a loop: one table over its evaluations" $ do
        cs <- copiesAfter batchedConfig defs "x"
        let below n = VU.length (VU.filter (\c -> c * n <= 0.9 * n) cs)
            elses = sum (map below [3, 2, 1])
            at k =
              runWith
                batchedConfig{cores = k}
                ( defs
                    <> [ "let go n acc = if n == 0 then acc else go (n - 1) (if x * n > 0.9 * n then acc + 1 else acc)"
                       , "go 3 0"
                       ]
                )
        tablesOf (at 1)
          @?= Right
            [ drawn
                "x * n > 0.9 * n"
                "3 evaluations × 1000 samples"
                (3000 - elses, elses)
                True
            ]
        at 2 @?= at 1
        at 4 @?= at 1
    , testCase
        "a branch point inside another: the copies that went the other way left earlier"
        $ do
          cs <- copiesAfter batchedConfig defs "x"
          let count f = VU.length (VU.filter f cs)
              at k =
                runWith
                  batchedConfig{cores = k}
                  (defs <> ["if x > 0.9 then (if x > 1.05 then 1 else 3) else 2"])
              outer = count (> 0.9)
              inner = count (> 1.05)
          tablesOf (at 1)
            @?= Right
              [ drawn "x > 0.9" "1000 samples" (outer, 1000 - outer) True
              , ifTable
                  "note"
                  "x > 1.05"
                  ( "1000 samples (by the declared uncertainty; "
                      <> tshow (1000 - outer)
                      <> " had left the evaluated path at an earlier branch point"
                  )
                  (inner, outer - inner)
                  False
              ]
          at 2 @?= at 1
          at 4 @?= at 1
    , testCase
        "rounding alone: a short circuit's copies that would have gone on leave the path"
        $ do
          let cfg = doubleConfig{samples = 10}
          sum' <- either (assertFailure . T.unpack) pure (doubleOf cfg "1 + 1e-16")
          held <- case sum'.estimate of
            Copies RoundingOnly cs -> pure (VU.length (VU.filter (> 1) cs))
            other -> assertFailure (show other) >> pure 0
          let at k =
                runWith
                  cfg{cores = k}
                  ["if 1 + 1e-16 > 1 && 2 > 1 then 1 else (if 1 + 1e-16 > 1 then 2 else 3)"]
          at 1
            @?= Right
              [ "3\n"
                  <> ifTable
                    "warning"
                    "1 + 1e-16 > 1"
                    ( "10 samples (lost in rounding; "
                        <> tshow held
                        <> " had left the evaluated path at an earlier branch point"
                    )
                    (held, 10 - held)
                    False
              ]
          at 4 @?= at 1
    , testCase "draws: a short circuit splits the copies, as an if does" $ do
        cs <- copiesAfter batchedConfig defs "x"
        let count f = VU.length (VU.filter f cs)
            both = count (\c -> c > 1.05 && c < 1.1)
            inner = count (> 0.9) - both
        tablesOf
          ( runWith
              batchedConfig
              (defs <> ["if x > 1.05 && x < 1.1 then 1 else (if x > 0.9 then 2 else 3)"])
          )
          @?= Right
            [ drawn "x > 1.05 && x < 1.1" "1000 samples" (both, 1000 - both) False
            , ifTable
                "note"
                "x > 0.9"
                ( "1000 samples (by the declared uncertainty; "
                    <> tshow both
                    <> " had left the evaluated path at an earlier branch point"
                )
                (inner, 1000 - both - inner)
                True
            ]
    , testCase "copies that differ by rounding alone say so, with their count" $ do
        let cfg = doubleConfig{samples = 10}
        sum' <- either (assertFailure . T.unpack) pure (doubleOf cfg "1 + 1e-16")
        held <- case sum'.estimate of
          Copies RoundingOnly cs -> pure (VU.length (VU.filter (> 1) cs))
          other -> assertFailure (show other) >> pure 0
        (held > 0 && held < 10) @? show held
        let at k = runWith cfg{cores = k} ["if 1 + 1e-16 > 1 then 1 else 2"]
        at 1
          @?= Right
            [ "2\n"
                <> ifTable
                  "warning"
                  "1 + 1e-16 > 1"
                  "10 samples (lost in rounding"
                  (held, 10 - held)
                  False
            ]
        at 2 @?= at 1
        at 4 @?= at 1
    , testCase "`/=` reads as written, and a row of 0 needs no special wording"
        $ runWith batchedConfig (defs <> ["if x /= 1 then 1 else 2"])
          @?= Right
            [ "2 (Monte Carlo: mean 1, sd 0, 1000 samples)\n"
                <> drawn "x /= 1" "1000 samples" (1000, 0) False
            ]
    , testCase "a case on data whose copies choose nothing has no table"
        $ runWith batchedConfig (defs <> ["case {x, 2} of {} -> 0; y : ys -> y"])
          @?= runWith batchedConfig (defs <> ["x"])
    , testCase
        "a case on a list pattern: its scrutinee's samples have their own lengths"
        $ do
          cs <- copiesAfter batchedConfig defs "x"
          let long = VU.length (VU.filter (> 0.95) cs)
              at k =
                runWith
                  batchedConfig{cores = k}
                  ( defs
                      <> ["let g y = if y > 0.95 then {y} else {}", "case g x of {} -> 0; z : zs -> z"]
                  )
          tablesOf (at 1)
            @?= Right
              [ drawn "y > 0.95" "1000 samples" (long, 1000 - long) True
              , T.intercalate
                  "\n"
                  [ "note: the branch at `case g x of` goes both ways across 1000 samples (by the declared uncertainty):"
                  , "  {}       " <> T.justifyRight 3 ' ' (tshow (1000 - long))
                  , "  z : zs   "
                      <> T.justifyRight 3 ' ' (tshow long)
                      <> "   ← taken (the nominal branch)"
                  ]
              ]
          at 2 @?= at 1
          at 4 @?= at 1
    , testCase
        "a value shared with the evaluation around a split, at 1, 2, 4 and 32 cores"
        $ do
          let at k =
                runWith
                  batchedConfig{cores = k}
                  (defs <> ["let w = (if x > 0.85 then 3 else 4) in if x > 0.9 then 1 else w"])
          at 2 @?= at 1
          at 4 @?= at 1
          at 32 @?= at 1
    ]
 where
  defs = ["let x = 1 ±σ 0.1"]
  -- A note where the copies carry draws, after the condition and the
  -- copies it is across.
  drawn :: Text -> Text -> (Int, Int) -> Bool -> Text
  drawn cond across = ifTable "note" cond (across <> " (by the declared uncertainty")

-- Splitting: Monte Carlo follows each sample's own branch --------------------------------

{- | Where the copies carry draws, they are samples: each alternative is
evaluated with the group of copies that selects it, and the results are
put back together copy by copy (design §8.2).
-}
splitTests :: TestTree
splitTests =
  testGroup
    "splitting: each sample follows its own branch"
    [ testCase
        "if x > 0.9 then 1 else 2 at 10⁴ samples: a Bernoulli sample's mean and deviation"
        $ do
          -- x = 1 ±σ 0.1 is below 0.9 with probability Φ(−1).
          let p = 0.15865525393145707 :: Double
              n = 10000
              sigma = sqrt (p * (1 - p))
              se = sigma / sqrt n
              seSd = abs (1 - 2 * p) / (2 * sigma) * se
              at e = either (Left . T.unpack) (Right . (.value)) (doubleOf monteCarlo e)
              src = "let x = 1 ±σ 0.1 in let r = if x > 0.9 then 1 else 2 in "
          case (at (src <> "mid r"), at (src <> "sd r")) of
            (Right m, Right s) -> do
              (abs (m - (1 + p)) < 5 * se) @? ("mean " <> show m)
              (abs (s - sigma) < 5 * seSd) @? ("sd " <> show s)
            other -> assertFailure (show other)
    , testCase "each copy is its own branch's, keyed as before" $ do
        cs <- copiesAfter batchedConfig defs "x"
        out <- copiesAfter batchedConfig defs "if x > 0.9 then 1 else 2"
        out @?= VU.map (\c -> if c > 0.9 then 1 else 2) cs
    , testCase "groups split again at a later branch point" $ do
        cs <- copiesAfter batchedConfig defs "x"
        out <-
          copiesAfter
            batchedConfig
            defs
            "if x > 0.9 then (if x > 1.05 then 1 else 3) else 2"
        out @?= VU.map (\c -> if c > 0.9 then (if c > 1.05 then 1 else 3) else 2) cs
    , testCase "a tensor puts its components back together copy by copy"
        $ case numbersIn
          batchedConfig
          "let x = 1 ±σ 0.1 in let v = if x > 0.9 then [1, x] else [2, 0] in [x, v.0, v.1]" of
          Right [x, v0, v1] -> do
            let xs = copiesOf x
            copiesOf v0 @?= VU.map (\c -> if c > 0.9 then 1 else 2) xs
            copiesOf v1 @?= VU.map (\c -> if c > 0.9 then c else 0) xs
            -- the nominal value is the nominal branch's
            (v0.value, v1.value) @?= (1, 1)
          other -> assertFailure (show other)
    , testCase "the same constructor recombines field by field" $ do
        case numbersIn
          batchedConfig
          "let x = 1 ±σ 0.1 in let p = if x > 0.9 then (x, 1) else (2 * x, 2) in case p of (a, b) -> [x, a, b]" of
          Right [x, a, b] -> do
            let xs = copiesOf x
            copiesOf a @?= VU.map (\c -> if c > 0.9 then c else 2 * c) xs
            copiesOf b @?= VU.map (\c -> if c > 0.9 then 1 else 2) xs
          other -> assertFailure (show other)
        -- and prints as one tuple, not as outcomes
        case runWith batchedConfig (defs <> ["if x > 0.9 then (x, 1) else (2 * x, 2)"]) of
          Right [out] -> ("(1 (Monte Carlo" `T.isPrefixOf` out) @? T.unpack out
          other -> assertFailure (show other)
    , testCase "an alternative no copy selects is not evaluated"
        $
        -- Every copy of x is above 0.5, so `loop 0` would run to the limit.
        runWith
          batchedConfig
          ( defs
              <> ["let loop n = loop n", ":set steps 100000", "if x > 0.5 then 1 else loop 0"]
          )
          @?= Right ["1"]
    , testCase "a loop whose condition carries draws: 10⁵ steps, each sample its own" $ do
        -- Each copy stops at the first n with n · x > 10⁵ in its own
        -- doubles, up to 1.4 · 10⁵ steps, past the default depth: the
        -- split in tail position is a tail call (design §8.2).
        let cfg = batchedConfig{samples = 10}
            ls =
              [ "let x = 1 ±σ 0.1"
              , "let count n = if n * x > 100000 then n else count (n + 1)"
              ]
            firstAbove c =
              let n0 = floor (100000 / c) - 2 :: Int
               in head'
                    [fromIntegral n | n <- [max 0 n0 ..], fromIntegral n * c > (100000 :: Double)]
            head' = foldr const 0
        cs <- copiesAfter cfg ls "x"
        out <- copiesAfter cfg ls "count 0"
        out @?= VU.map firstAbove cs
        (VU.maximum out > 100000) @? show out
    , testCase "steps counts each path: a split's groups are not added together" $ do
        let run x =
              runWith
                batchedConfig
                [ "let work n = if n == 0 then 0 else work (n - 1)"
                , "let x = " <> x
                , ":set steps 3000"
                , "if x > 0.9 then work 300 else work 300"
                ]
        -- One evaluation of `work 300` fits; split, each path takes one.
        run "1" @?= Right ["0"]
        fmap (map (T.takeWhile (/= ' '))) (run "1 ±σ 0.1") @?= Right ["0"]
    , testCase "1, 2 and 4 cores give the same copies, bit for bit" $ do
        let src =
              "let x = 1 ±σ 0.1 in let y = 2 ±σ 0.3 in [if x > 0.9 then x * y else y, if y > 2 then (if x > 1 then 1 else 2) else 3]"
            at k = case copiesBatched batchedConfig{cores = k} src of
              Right (Just cs) -> pure cs
              other -> assertFailure (show other) >> pure []
        one <- at 1
        two <- at 2
        four <- at 4
        two @?= one
        four @?= one
        (map (.estimate) <$> numbersIn batchedConfig src)
          @?= Right (map (Copies Drawn) one)
    , testCase "rounding alone does not split: the copies follow the nominal branch" $ do
        runWith doubleConfig{samples = 10} ["if 1 + 1e-16 > 1 then 1 else 2"]
          @?= Right
            [ "2\n"
                <> ifTable "warning" "1 + 1e-16 > 1" "10 samples (lost in rounding" (7, 3) False
            ]
        -- a condition whose copies differ by rounding is no mixture
        runWith doubleConfig{samples = 10} ["1 + 1e-16 > 1"] @?= Right ["false"]
    , testCase "affine and samples 0 are unaffected" $ do
        expectLeft "cannot decide" (runWith defaultConfig defs')
        runWith
          doubleConfig
          ["if 1 + 1e-16 > 1 then 1 else 2", "if 2 > 1 then (3, true) else (4, false)"]
          @?= Right ["2", "(3, true)"]
    ]
 where
  defs = ["let x = 1 ±σ 0.1"]
  defs' = ["let x = 1 ±σ 0.1", "if x > 0.9 then 1 else 2"]
  copiesOf x = case x.estimate of
    Copies _ cs -> cs
    ErrorBound _ -> VU.empty

-- Mixtures: samples whose outcomes differ in kind -----------------------------------------

{- | Where the groups of a split give different constructors, the value is
a mixture of outcomes (design §8.2): each option a group of the copies
with its own value, printed as a table of outcomes.
-}
mixtureTests :: TestTree
mixtureTests =
  testGroup
    "mixtures of outcomes"
    [ testCase "classify: the outcomes' counts, and a case on them one numeric sample" $ do
        let cfg = monteCarlo
            lines' =
              [ "data Sign = Neg | Pos"
              , "let x = 0.05 ±σ 0.1"
              , "let classify z = if z < 0 then Neg else Pos"
              ]
        cs <- copiesAfter cfg lines' "x"
        let neg = VU.length (VU.filter (< 0) cs)
            pos = 10000 - neg
            -- Φ(−0.5), the chance of Neg
            p = 0.3085375387259869 :: Double
            se = sqrt (p * (1 - p) / 10000)
        (abs (fromIntegral neg / 10000 - p) < 5 * se) @? show neg
        out <- copiesAfter cfg lines' "case classify x of Neg -> -1; Pos -> 1"
        out @?= VU.map (\c -> if c < 0 then -1 else 1) cs
        case runWith cfg (lines' <> ["classify x"]) of
          Right [printed] ->
            take 4 (T.lines printed)
              @?= [ "Pos (Monte Carlo over 10000 samples, 2 outcomes):"
                  , "  outcome   samples   share"
                  , "  Pos          " <> tshow pos <> "   " <> share pos 10000 <> "   ← nominal"
                  , "  Neg          " <> tshow neg <> "   " <> share neg 10000
                  ]
          other -> assertFailure (show other)
        -- its mean, 1 − 2·Φ(−0.5), within five standard errors
        case runWith cfg (lines' <> ["mid (case classify x of Neg -> -1; Pos -> 1)"]) of
          Right (m : _) ->
            (abs (read (T.unpack (T.takeWhile (/= '\n') m)) - (1 - 2 * p)) < 5 * 2 * se)
              @? T.unpack m
          other -> assertFailure (show other)
    , testCase "an outcome with numbers shows each one's own cluster" $ do
        let lines' =
              [ "data Impact = Impact {arrival :: Num s, speed :: Num (m/s)}"
              , "data Shot = Hit Impact | Miss"
              , "let x = 1 ±σ 0.1"
              ]
        cs <- copiesAfter batchedConfig lines' "x"
        let hits = VU.length (VU.filter (> 0.9) cs)
        case runWith
          batchedConfig
          ( lines'
              <> [ "if x > 0.9 then Hit (Impact {arrival = 12 s + x * 1 s, speed = 3 m/s * x}) else Miss"
                 ]
          ) of
          Right [printed] -> case T.lines printed of
            header : columns : hitRow : missRow : _ -> do
              header
                @?= "Hit (Impact {arrival = 13 s, speed = 3 m s^-1}) (Monte Carlo over 1000 samples, 2 outcomes):"
              columns @?= "  outcome      samples   share   fields"
              ( "  Hit Impact       "
                  <> tshow hits
                  <> "   "
                  <> share hits 1000
                  <> "   0.arrival: mean 13."
                )
                `T.isPrefixOf` hitRow
                @? T.unpack hitRow
              ("0.speed: mean 3." `T.isInfixOf` hitRow && "← nominal" `T.isSuffixOf` hitRow)
                @? T.unpack hitRow
              missRow
                @?= "  Miss             "
                  <> tshow (1000 - hits)
                  <> "   "
                  <> share (1000 - hits) 1000
            _ -> assertFailure (T.unpack printed)
          other -> assertFailure (show other)
    , testCase "two mixtures combine copy by copy" $ do
        let lines' = ["let x = 1 ±σ 0.1", "let y = 1 ±σ 0.2"]
        xs <- copiesAfter batchedConfig lines' "x"
        ys <- copiesAfter batchedConfig lines' "y"
        let both = VU.length (VU.filter id (VU.zipWith (\a b -> a > 0.9 && b > 1) xs ys))
        out <- copiesAfter batchedConfig lines' "if x > 0.9 && y > 1 then 1 else 0"
        VU.sum out @?= fromIntegral both
        case runWith batchedConfig (lines' <> ["x > 0.9 && y > 1"]) of
          Right [printed] ->
            ( ("  true          " <> tshow both <> "   " <> share both 1000)
                `elem` T.lines printed
            )
              @? T.unpack printed
          other -> assertFailure (show other)
    , testCase "lists of different lengths: outcomes by structure" $ do
        let lines' = ["let x = 0.05 ±σ 0.1"]
            src = "if x > 0 then {x, 2 * x} else (if x > -0.1 then {x} else {})"
        cs <- copiesAfter batchedConfig lines' "x"
        let two = VU.length (VU.filter (> 0) cs)
            none = VU.length (VU.filter (<= -0.1) cs)
            one = 1000 - two - none
        case runWith batchedConfig (lines' <> [src]) of
          Right [printed] -> do
            let rows = map (T.unwords . T.words) (take 3 (drop 2 (T.lines printed)))
                expected =
                  [ "{_, _} " <> tshow two <> " " <> share two 1000 <> " 0: mean"
                  , "{_} " <> tshow one <> " " <> share one 1000 <> " 0: mean"
                  , "{} " <> tshow none <> " " <> share none 1000
                  ]
            take 1 (T.lines printed)
              @?= ["{0.05, 0.1} (Monte Carlo over 1000 samples, 3 outcomes):"]
            and (zipWith T.isPrefixOf expected rows) @? show rows
          other -> assertFailure (show other)
    , testCase "past `:set outcomes`, the usual limit error" $ do
        let lines' = ["let x = 0.05 ±σ 0.1", ":set outcomes 2"]
        expectLeft
          "error: the value has more than 2 outcomes (`:set outcomes`)"
          ( runWith
              batchedConfig
              (lines' <> ["if x > 0 then {x, 2 * x} else (if x > -0.1 then {x} else {})"])
          )
        expectLeft
          "error: the value would have more than 2 outcomes (`:set outcomes`)"
          ( runWith
              batchedConfig
              ( lines'
                  <> ["data T = A | B | C", "if x > 0.1 then A else (if x > 0 then B else C)"]
              )
          )
    , testCase "more than ten outcomes: the ten commonest, then the rest counted"
        $ case runWith
          batchedConfig
          [ "let x = 1 ±σ 0.1"
          , "let upto n k = if k >= n then {} else k : upto n (k + 1)"
          , "upto (floor (x * 30)) 0"
          ] of
          Right [printed] -> case drop 12 (T.lines printed) of
            others : _ ->
              ("  and " `T.isPrefixOf` others && " others" `T.isSuffixOf` others)
                @? T.unpack printed
            [] -> assertFailure (T.unpack printed)
          other -> assertFailure (show other)
    , testCase "a field of an outcome that nothing reads is never evaluated" $ do
        -- `loop 0` would run to the limit if anything forced it.
        let lines' = ["let x = 1 ±σ 0.1", "let loop n = loop n", ":set steps 100000"]
        cs <- copiesAfter batchedConfig ["let x = 1 ±σ 0.1"] "x"
        out <-
          copiesAfter
            batchedConfig
            (lines' <> ["let m = if x > 0.9 then {1, loop 0} else {}"])
            "case m of {} -> 0; y : ys -> y"
        out @?= VU.map (\c -> if c > 0.9 then 1 else 0) cs
        case runWith
          batchedConfig{cores = 4}
          (lines' <> ["case (if x > 0.9 then {1, loop 0} else {}) of {} -> 0; y : ys -> y"]) of
          Right [printed] -> ("1 (Monte Carlo" `T.isPrefixOf` printed) @? T.unpack printed
          other -> assertFailure (show other)
    , testCase "1, 2 and 4 cores give the same mixtures, and the batches merge" $ do
        let lines' =
              [ "data Sign = Neg | Pos"
              , "let x = 0.05 ±σ 0.1"
              , "let upto n k = if k >= n then {} else k : upto n (k + 1)"
              ]
            srcs =
              [ "if x < 0 then Neg else Pos"
              , "if x > 0 then {x, 2 * x} else (if x > -0.1 then {x} else {})"
              , "(if x < 0 then Neg else Pos, x > 0.1)"
              , "upto (floor (x * 300)) 0"
              ]
            at k = runWith batchedConfig{cores = k} (lines' <> srcs)
        at 2 @?= at 1
        at 4 @?= at 1
        mapM_ (\s -> mergesAfter batchedConfig{cores = 4} lines' s @?= Right True) srcs
    ]
 where
  share :: Int -> Int -> Text
  share k n =
    T.pack
      (showFFloat (Just 1) (100 * fromIntegral k / fromIntegral n :: Double) "")
      <> "%"

-- | The tables printed after each value, each as its lines.
tablesOf :: Either Text [Text] -> Either Text [Text]
tablesOf = fmap (concatMap tablesIn)
 where
  tablesIn out = map (T.intercalate "\n") (grouped (dropWhile (not . header) (T.lines out)))
  header l = "note: " `T.isPrefixOf` l || "warning: " `T.isPrefixOf` l
  grouped = \case
    [] -> []
    h : rest -> let (rows, more) = break header rest in (h : rows) : grouped more

{- | The table of an @if@: its kind, condition, what it is across (the
samples, the cause and anything more, without the closing parenthesis),
its rows and whether the nominal branch is @then@.
-}
ifTable :: Text -> Text -> Text -> (Int, Int) -> Bool -> Text
ifTable kind cond across (thenN, elseN) takenThen =
  T.intercalate
    "\n"
    [ kind
        <> ": the branch at `if "
        <> cond
        <> "` goes both ways across "
        <> across
        <> "):"
    , row "then" thenN takenThen
    , row "else" elseN (not takenThen)
    ]
 where
  w = T.length (tshow (max thenN elseN))
  row l n t =
    "  "
      <> l
      <> "   "
      <> T.justifyRight w ' ' (tshow n)
      <> (if t then "   ← taken (the nominal branch)" else "")

tshow :: (Show a) => a -> Text
tshow = T.pack . show

-- | The copies of a number, evaluated after some lines.
copiesAfter :: Config -> [Text] -> Text -> IO (VU.Vector Double)
copiesAfter cfg ls src = either (\e -> assertFailure (T.unpack e) >> pure VU.empty) pure $ do
  s <- sessionAfter cfg ls
  e <- parseExpr src
  (_, v) <- evalValueAs @Dbl s.config s.scope s.staging src e
  case v of
    VTensor [] _ _ buf
      | [Right x] <- V.toList buf
      , Copies _ cs <- x.estimate ->
          Right cs
    _ -> Left ("no copies: " <> src)

-- | Whether an input, after some lines, runs in batches that merge.
mergesAfter :: Config -> [Text] -> Text -> Either Text Bool
mergesAfter cfg ls src = do
  s <- sessionAfter cfg ls
  e <- parseExpr src
  r <- evalBatchedAs s.config s.scope s.staging src e
  Right (case r of Just (Right _) -> True; _ -> False)

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
    , testCase "the backend's defaults are the session's: seed 1, as :set shows" $ do
        -- The printer's settings once had seed 0 while :set showed 1.
        let backend = settingsAt (precisionOf defaultConfig)
        backend.seed @?= 1
        ( backend.decide.sigma
          , backend.decide.nonlinear
          , backend.samples
          , backend.rounding
          )
          @?= ( defaultConfig.sigma
              , defaultConfig.nonlinear
              , defaultConfig.samples
              , defaultConfig.rounding
              )
        (elem ("seed " <> T.pack (show backend.seed)) <$> runWith defaultConfig [":set"])
          @?= Right True
    , testCase
        "rounding nearest: copies with no draws are the IEEE result, and print exact"
        $ case doubleOf doubleConfig{samples = 10, rounding = RoundNearest} "0.1 + 0.2 * 3" of
          Left err -> assertFailure (T.unpack err)
          Right x -> do
            x.estimate @?= Copies RoundingOnly (VU.replicate 10 x.value)
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
              Right x -> x.estimate @?= Copies Drawn (VU.replicate cfg.samples 0)
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
            (Right (Copies _ ns), Right (Copies _ rs)) ->
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

{- | Printing under Monte Carlo (design §8.2, corrections after building):
a value whose copies carry draws prints its nominal IEEE value with the
sample beside it, never @±@ the standard error of the copies' mean, and
@errorOf@ and @digitsOf@, which measure rounding, refuse it. Whether the
copies carry draws propagates through arithmetic.
-}
monteCarloPrintingTests :: TestTree
monteCarloPrintingTests =
  testGroup
    "printing under Monte Carlo: the sample beside the nominal value"
    [ testCase
        "n·n prints 0, its nominal value, with mean and sd, not ± a standard error"
        $ runWith monteCarlo ["let n = 0 ±σ 1", "n * n"]
          @?= Right ["0 (Monte Carlo: mean 1.015, sd 1.441, 10000 samples)"]
    , testCase "units are kept, in the sample too"
        $ do
          runWith monteCarlo ["let n = 0 ±σ 1", "n * 1 m"]
            @?= Right ["0 m (Monte Carlo: mean -0.016 m, sd 1.0073 m, 10000 samples)"]
          seededLines
            [ ":set samples 10000"
            , ":set rounding nearest"
            , ":backend double"
            , "let M = 5.9722e24 kg ±σ 6e20 kg"
            , "2 * pi * sqrt ((7000 km)^3 / (astro.G * M))"
            ]
            @?= Right
              [ "5828.501263698674 s (Monte Carlo: mean 5828.5079 s, sd 0.3027 s, 10000 samples)"
              ]
    , testCase "under random rounding too, and never with ±" $ do
        let outs = runWith monteCarlo{rounding = RoundRandom} ["let x = 1 ±σ 0.1", "x / 3"]
        case outs of
          Right [out] -> do
            ("0.3333333333333333 (Monte Carlo: mean " `T.isPrefixOf` out) @? T.unpack out
            not ("±" `T.isInfixOf` out) @? T.unpack out
          other -> assertFailure (show other)
    , testCase "a tensor prints each component's mean and sd in its shape and unit"
        $ runWith monteCarlo ["let n = 0 ±σ 1", "[n, n * n, 2] * 1 m"]
          @?= Right
            [ "[0, 0, 2] m (Monte Carlo: mean [-0.016, 1.015, 2] m, sd [1.0073, 1.441, 0] m, 10000 samples)"
            ]
    , testCase "a record and a tuple print per component, each with its own sample"
        $ do
          runWith
            monteCarlo
            [ "data Body = Body {mass :: Num kg, vel :: Vec 2 (m/s)}"
            , "let n = 0 ±σ 1"
            , "Body {mass = 5 kg, vel = [1, 2 + n] * 1 m/s}"
            ]
            @?= Right
              [ "Body {mass = 5 kg, vel = [1, 2] m s^-1 (Monte Carlo: mean [1, 1.984] m s^-1, sd [0, 1.0073] m s^-1, 10000 samples)}"
              ]
          runWith monteCarlo ["let n = 0 ±σ 1", "(n, 0.5)"]
            @?= Right ["(0 (Monte Carlo: mean -0.016, sd 1.0073, 10000 samples), 0.5)"]
    , testCase "with rounding alone, printing, errorOf and digitsOf are as before" $ do
        let random = monteCarlo{rounding = RoundRandom}
        case runWith random ["0.1 + 0.2", "errorOf (0.1 + 0.2) > 0", "digitsOf 0.5"] of
          Right [sum', positive, digits] -> do
            ( "0.30000000000000004 ± " `T.isPrefixOf` sum'
                && " (estimate, 10000 samples)" `T.isSuffixOf` sum'
              )
              @? T.unpack sum'
            positive @?= "true"
            digits @?= "15.954589770191003"
          other -> assertFailure (show other)
        -- Copies that agree, rounded to nearest, have no spread to show.
        runWith monteCarlo ["0.1 + 0.2", "errorOf (0.1 + 0.2)"]
          @?= Right ["0.30000000000000004", "0"]
    , testCase "errorOf and digitsOf refuse a value whose copies carry declared σ" $ do
        let refusal = "its copies carry declared σ; read `sd`"
        expectLeft refusal (runWith monteCarlo ["let x = 1 ±σ 0.1", "errorOf x"])
        expectLeft
          ("`digitsOf` measures rounding: " <> refusal)
          (runWith monteCarlo ["let x = 1 ±σ 0.1", "digitsOf (x * 2 + 1)"])
        expectLeft refusal (runWith monteCarlo ["errorOf (gauss 2)"])
        expectLeft
          refusal
          ( runWith
              monteCarlo{rounding = RoundRandom}
              ["let x = 1 ±σ 0.1", "errorOf (sin (x * 1 rad))"]
          )
    , testCase "carrying draws propagates through arithmetic, and a mix carries them" $ do
        let spread src =
              (\x -> case x.estimate of Copies sp _ -> Just sp; _ -> Nothing)
                <$> doubleOf monteCarlo{rounding = RoundRandom} src
        spread "let x = 1 ±σ 0.1 in x" @?= Right (Just Drawn)
        spread "let x = 1 ±σ 0.1 in sqrt (x * 3 + 1) / 2" @?= Right (Just Drawn)
        -- one operand drawn and the other rounded only
        spread "let x = 1 ±σ 0.1 in x + (0.1 + 0.2)" @?= Right (Just Drawn)
        spread "let x = 1 ±σ 0.1 in atan2 (0.3 * 1) x" @?= Right (Just Drawn)
        spread "0.1 + 0.2" @?= Right (Just RoundingOnly)
        -- the same unknown cancelled still carries its draws, all zero
        spread "let x = 1 ±σ 0.1 in x - x" @?= Right (Just Drawn)
        runWith monteCarlo ["let x = 1 ±σ 0.1", "x - x"]
          @?= Right ["0 (Monte Carlo: mean 0, sd 0, 10000 samples)"]
        -- the sample's statistics are numbers known exactly: no draws pass
        spread "let x = 1 ±σ 0.1 in sd x + 0.5" @?= Right (Just RoundingOnly)
        runWith monteCarlo ["let x = 1 ±σ 0.1", "errorOf (sd x)"] @?= Right ["0"]
    , testCase "batches print what one evaluation prints" $ do
        let ls = ["let x = 1 ±σ 0.1", "let y = 2 ±σ 0.3", "[x * y, 0.5] * 1 s"]
        runWith batchedConfig{cores = 4} ls @?= runWith batchedConfig{cores = 1} ls
        (all (T.isInfixOf "Monte Carlo") <$> runWith batchedConfig{cores = 4} ls)
          @?= Right True
    , testCase "a statistic's digits come from its standard error" $ do
        -- two significant digits of the error: 0.0144 sets the place 10⁻³
        showSampled 0.0144 1.0153 @?= "1.015"
        showSampled 0.0102 1.4407 @?= "1.441"
        -- trailing zeros are digits the sample resolves
        showSampled 0.0065 5828.5 @?= "5828.5000"
        showSampled 30 12345.6 @?= "12346"
        showSampled 300 12345.6 @?= "12350"
        showSampled 0.0144 (-0.0001) @?= "0.000"
        showSampled 1.0e18 (-1.6e18) @?= "-1.6e18"
        showSampled 1.0e17 (-1.6e18) @?= "-1.60e18"
        showSampled 7.1e-12 1.0073e-9 @?= "1.0073e-9"
        -- no error, or more digits than a double holds: the shortest digits
        showSampled 0 0.30000000000000004 @?= "0.30000000000000004"
        showSampled 1.0e-30 0.30000000000000004 @?= "0.30000000000000004"
    ]

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
          Right x | Copies _ cs <- x.estimate -> Right cs
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
          (map (.estimate) <$> numbersIn batchedConfig src)
            @?= Right (map (Copies Drawn) one)
    , testCase "under random rounding too, with no declared σ" $ do
        let src = "[0.1 + 0.2 * 3, sqrt 2 / 3, exp 0.3]"
            at k = copiesBatched batchedConfig{cores = k, rounding = RoundRandom} src
        at 4 @?= at 1
        (isJust <$> at 4) @?= Right True
    , testCase
        "an input that reads across the copies runs as one, with the same result"
        $ do
          let ls = ["let x = 1 ±σ 0.1", "[mid (x * x), sd (x * x), errorOf (0.1 + 0.2)]"]
          runWith batchedConfig{cores = 4} ls @?= runWith batchedConfig{cores = 1} ls
          (length <$> runWith batchedConfig{cores = 4} ls) @?= Right 1
    , testCase "the batches' tables come together" $ do
        let ls = ["if 1 + 1e-16 > 1 then 1 else 2"]
            outs k = runWith doubleConfig{samples = 10, cores = k} ls
        outs 4 @?= outs 1
        -- Three, in the order one evaluation reaches them, whichever batch
        -- reaches each first.
        let three k =
              runWith
                doubleConfig{samples = 6, cores = k}
                [ "[if 2 + 3e-16 > 2 then 1 else 2, if 1 + 1e-16 > 1 then 1 else 2, if 4 - 4e-16 < 4 then 1 else 2]"
                ]
        three 3 @?= three 1
        three 2 @?= three 1
        three 1
          @?= Right
            [ T.intercalate
                "\n"
                [ "[1, 2, 1]"
                , ifTable "warning" "2 + 3e-16 > 2" "6 samples (lost in rounding" (2, 4) True
                , ifTable "warning" "1 + 1e-16 > 1" "6 samples (lost in rounding" (4, 2) False
                , ifTable "warning" "4 - 4e-16 < 4" "6 samples (lost in rounding" (2, 4) True
                ]
            ]
        outs 4
          @?= Right
            [ "2\n"
                <> ifTable "warning" "1 + 1e-16 > 1" "10 samples (lost in rounding" (7, 3) False
            ]
    , testCase "steps counts each path: accepted alike at every K" $ do
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
    , testCase "a split near the limit: accepted or refused alike at K = 1, 2 and 4" $ do
        -- Two groups that never share a batch at K = 2 or 4, each doing
        -- one `work 1000` (7000 to 8000 steps); the nominal copy does
        -- none. Counted per batch, K = 1 took both and was refused at
        -- 12000 steps where K = 2 and 4 were not; per path, each path
        -- takes one.
        cs <- copiesAfter eight ["let x = 1 ±σ 0.1"] "x"
        let at i = T.pack (show (cs VU.! i))
            is i = "x == " <> at i
            program =
              "if "
                <> is 0
                <> " || "
                <> is 1
                <> " then work 1000 else (if "
                <> is 6
                <> " then work 1000 else 0)"
            outs k steps = runWith eight (pathLines k steps <> [program])
        VU.length cs @?= 8
        for_ [1, 2, 4] $ \k -> do
          fmap (map firstWord) (outs k 12000) @?= Right ["0"]
          expectLeft "took more than 4000 steps" (outs k 4000)
    , testCase "work shared before a split is on each path that forces it" $ do
        -- `w` is bound before the split and forced only by the group of
        -- copy 0, then the evaluation goes on: on copy 0's path, `w` and
        -- the work after the join, at every K.
        cs <- copiesAfter eight ["let x = 1 ±σ 0.1"] "x"
        let program =
              "let w = work 1000 in (if x == "
                <> T.pack (show (cs VU.! 0))
                <> " then w else 0) + work 1000"
            outs k steps = runWith eight (pathLines k steps <> [program])
        for_ [1, 2, 4] $ \k -> do
          fmap (map firstWord) (outs k 25000) @?= Right ["0"]
          expectLeft "took more than 12000 steps" (outs k 12000)
    , testCase "the work after a join is on every path through it" $ do
        -- Each group does one `work 1000`, and the evaluation goes on
        -- with another: every path takes two, whether its batch split
        -- (K = 1) or not (the batches without copy 0 at K = 2 and 4).
        cs <- copiesAfter eight ["let x = 1 ±σ 0.1"] "x"
        let program =
              "(if x == "
                <> T.pack (show (cs VU.! 0))
                <> " then work 1000 else work 1000) + work 1000"
            outs k steps = runWith eight (pathLines k steps <> [program])
        for_ [1, 2, 4] $ \k -> do
          fmap (map firstWord) (outs k 25000) @?= Right ["0"]
          expectLeft "took more than 12000 steps" (outs k 12000)
    , testCase "depth near the limit: refused or accepted alike at K = 1, 2 and 4" $ do
        -- A recursion that is not a tail call, under a condition on
        -- draws: some batches split where others do not, and the depth
        -- along a path is the same either way.
        let outs k d =
              runWith
                eight
                [ "let x = 1 ±σ 0.1"
                , "let g n = if n * x > 100 then 0 else 1 + g (n + 1)"
                , ":set depth " <> T.pack (show (d :: Int))
                , ":set cores " <> T.pack (show (k :: Int))
                , "g 0"
                ]
        for_ [1, 2, 4] $ \k -> do
          expectLeft "nested more than 105 calls deep" (outs k 105)
          fmap (map firstWord) (outs k 110) @?= Right ["101"]
    , testCase "a runaway on one split path is still stopped"
        $ for_ [1, 2, 4]
        $ \k ->
          expectLeft
            "took more than 100000 steps"
            ( runWith
                batchedConfig{cores = k}
                [ "let x = 1 ±σ 0.1"
                , "let loop n = loop n"
                , ":set steps 100000"
                , "if x > 0.9 then 1 else loop 0"
                ]
            )
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

-- | Monte Carlo at eight copies, rounding to nearest: few enough to place.
eight :: Config
eight = batchedConfig{samples = 8}

-- | A countdown, the steps limit and the cores, for the steps-per-path tests.
pathLines :: Int -> Int -> [Text]
pathLines k steps =
  [ "let x = 1 ±σ 0.1"
  , "let work n = if n == 0 then 0 else work (n - 1)"
  , ":set steps " <> T.pack (show steps)
  , ":set cores " <> T.pack (show k)
  ]

-- | A printed value's first word: its IEEE value, before any statistics.
firstWord :: Text -> Text
firstWord = T.takeWhile (/= ' ')

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
