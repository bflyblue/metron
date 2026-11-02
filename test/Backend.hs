module Backend (backendTests, doubleOf, numberAs, doubleConfig, runWith) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Metron.Codebase (emptyCodebase)
import Metron.Compile (evalValueAs)
import Metron.Double (Dbl (..), Estimate (..), Layout (..), sampleNote)
import Metron.Driver (feed)
import Metron.Eval (Config (..), ValueOf (..), defaultConfig)
import Metron.Parser (parseExpr)
import Metron.Scalar (Rounding (..), Scalar)
import Metron.Session.Types (Session (..), emptySession)
import Metron.Syntax qualified as S
import Test.Tasty
import Test.Tasty.HUnit

-- Core/language tests can explicitly select rational arithmetic; runtime defaults are doubles.
doubleConfig :: Config
doubleConfig = defaultConfig
runWith :: Config -> [Text] -> Either Text [Text]
runWith cfg = go emptySession{config = cfg} []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do (s', out) <- feed s l; go s' (out : acc) ls
numberAs :: forall s. (Scalar s) => Config -> Text -> Either Text s
numberAs cfg src = do
  e <- parseExpr src
  (_, v) <- evalValueAs @s cfg S.rootScope emptyCodebase src e
  case v of
    VTensor [] _ _ buf | [x] <- V.toList buf -> either (Left . T.pack . show) Right x
    VUnit (VTensor [] _ _ buf) | [x] <- V.toList buf -> either (Left . T.pack . show) Right x
    _ -> Left ("not a scalar: " <> src)
doubleOf :: Config -> Text -> Either Text Dbl
doubleOf = numberAs @Dbl

backendTests :: TestTree
backendTests =
  localOption (mkTimeout 30_000_000)
    $ testGroup
      "independent arithmetic and grouped rounding"
      [ testCase "ordinary arithmetic follows IEEE operation order"
          $ forM_
            [ ("0.1 + 0.2", 0.1 + 0.2)
            , ("(1e16+1)-1e16", 0)
            , ("sqrt 2", sqrt 2)
            , ("exp 1", exp 1)
            , ("log 2", log 2)
            , ("sin (1 rad)", sin 1)
            , ("1.1^7", 1.1 ^ (7 :: Int))
            , ("fma 0.1 0.2 0.3", 0.32)
            ]
          $ \(src, expected) ->
            fmap (.value) (doubleOf doubleConfig src) @?= Right expected
      , testCase "IEEE exceptional results stay explicit" $ do
          fmap (isInfinite . (.value)) (doubleOf doubleConfig "1/0") @?= Right True
          fmap (isNaN . (.value)) (doubleOf doubleConfig "0/0") @?= Right True
          fmap (isNaN . (.value)) (doubleOf doubleConfig "sqrt (-1)") @?= Right True
          fmap (.value) (doubleOf doubleConfig "1e-320/10") @?= Right (1e-320 / 10)
      , testCase "no-input diagnostics have one baseline and R repetitions" $ do
          x <- get analysis "(1e16+1)-1e16"
          x.value @?= 0
          case x.estimate of
            Copies l cs -> do
              l.rounds @?= 16
              l.sampled @?= False
              VU.length cs @?= 17
              cs VU.! 0 @?= 0
              VU.any (/= 0) cs @? "cancellation should expose rounding sensitivity"
            _ -> assertFailure "missing diagnostic runs"
      , testCase "input baselines are unchanged by rounding mode or count" $ do
          let src = "let x = sample (normal 10 0.1) in x*x/3"
          off <- get doubleConfig{samples = 12} src
          on <- get analysis{samples = 12} src
          more <- get analysis{samples = 12, roundingSamples = 24} src
          baselines off @?= baselines on
          baselines off @?= baselines more
          -- Existing (i,j) repetitions keep their keys when R grows.
          forM_ [0 .. 11] $ \i -> take 16 (roundsFor i on) @?= take 16 (roundsFor i more)
      , testCase "shared inputs and shared computed expressions reuse their runs" $ do
          x <-
            get analysis{samples = 8} "let x = sample (normal 10 0.1) in let y = x/3 in y-y"
          case x.estimate of
            Copies _ cs -> VU.all (== 0) cs @? show cs
            _ -> assertFailure "missing input runs"
      , testCase "rounding repetitions follow their own branch" $ do
          x <- get analysis "let x = (1e16+1)-1e16 in if x == 0 then 0 else 1"
          case x.estimate of
            Copies _ cs -> do
              cs VU.! 0 @?= 0
              VU.any (== 1) cs @? show cs
            _ -> assertFailure "missing branch results"
      , testCase "constant branch results retain their input distribution" $ do
          x <-
            get doubleConfig{samples = 32} "if sample (uniform 0 1) < 0.5 then 0 else 1"
          case x.estimate of
            Copies grid cs -> do
              grid.sampled @?= True
              VU.any (== 0) cs && VU.any (== 1) cs @? show cs
            _ -> assertFailure "sample layout was lost"
      , testCase "grouped branch tables distinguish input and rounding visits" $ do
          case runWith analysis{samples = 8} ["if sample (uniform 0 1) < 0.5 then 0 else 1"] of
            Right outs ->
              T.isInfixOf "ordinary inputs / stochastic rounding repetitions" (T.unlines outs)
                @? show outs
            Left err -> assertFailure (T.unpack err)
      , testCase "IEEE predicates inspect every realized value" $ do
          x <-
            get
              doubleConfig{samples = 32}
              "let x = sample (uniform (-1) 1) in if isNaN (sqrt x) then 0 else 1"
          case x.estimate of
            Copies _ cs -> VU.any (== 0) cs && VU.any (== 1) cs @? show cs
            _ -> assertFailure "predicate discarded input outcomes"
      , testCase "matrix scaling preserves ordinary sampled results under diagnostics" $ do
          let src = "(expm [[sample (uniform 0.1 4)]]).0.0"
          off <- get doubleConfig{samples = 8} src
          on <- get analysis{samples = 8} src
          baselines off @?= baselines on
      , testCase "sample reductions reject rounding analysis" $ do
          isLeft (doubleOf analysis "sd (sample (normal 1 0.1))")
            @? "reduction must refuse diagnostics"
      , testCase "cores cannot change either axis or reports" $ do
          let src = "let x = sample (uniform 1 2) in if x < 1.5 then x/3 else x*x"
              outputs cfg = [runWith cfg{samples = 12, cores = k} [src] | k <- [1, 2, 4]]
          forM_ [doubleConfig, analysis] $ \cfg -> case outputs cfg of
            a : rest -> all (== a) rest @? show (outputs cfg)
            [] -> assertFailure "missing core counts"
      , testCase "grouped reports keep constants and diagnostic offsets aligned" $ do
          let sampled = Dbl 1 (Copies (Layout 2 True) (VU.fromList [1, 0, 2, 3, 2, 4])) Nothing
              constant = Dbl 7 NoSamples Nothing
              layout ys = "[" <> T.intercalate ", " ys <> "]"
          case sampleNote layout [sampled, constant] of
            Nothing -> assertFailure "missing grouped report"
            Just report -> do
              T.isInfixOf "mean [2, 7]" report @? T.unpack report
              T.isInfixOf "outcome 95% [[1.05, 7], [2.95, 7]]" report @? T.unpack report
              T.isInfixOf "RMS displacement [1, 0]" report @? T.unpack report
              T.isInfixOf "2 input samples" report @? T.unpack report
      , testCase "controls reject incompatible arithmetic and excessive combined work" $ do
          isLeft
            ( runWith
                doubleConfig
                [":set arithmetic rational", ":set roundingAnalysis stochastic"]
            )
            @? "rational analysis refused"
          isLeft (runWith analysis [":set arithmetic rational"]) @? "switch refused"
          isLeft (runWith doubleConfig [":set samples 0"]) @? "zero input count refused"
          isLeft (runWith doubleConfig [":set roundingSamples 1"])
            @? "one repetition refused"
          isLeft
            ( doubleOf
                analysis{samples = 100000, roundingSamples = 1000}
                "sample (normal 0 1)"
            )
            @? "combined grid refused"
          runWith
            doubleConfig
            [":set propagation montecarlo", ":set arithmetic rational", "3 * (1/3)"]
            @?= Right ["1"]
      , testCase "removed operators, settings and commands are unavailable" $ do
          forM_
            [ "1 ± 0.1"
            , "1 ±σ 0.1"
            , "noise 1"
            , "gauss 1"
            , "within 1 0.1"
            , "sigma 1 0.1"
            , "bound 1"
            , "errorOf 1"
            , "digitsOf 1"
            , ":backend affine"
            , ":budget 1"
            , ":exact 1"
            , ":set sigma 3"
            , ":set nonlinear 1"
            , ":set rounding random"
            ]
            $ \src ->
              isLeft (runWith doubleConfig [src]) @? T.unpack src
      , testCase "mixed constructors separate baseline and rounding counts" $ do
          case runWith analysis ["if (1e16+1)-1e16 == 0 then true else false"] of
            Left err -> assertFailure (T.unpack err)
            Right out -> do
              let text = T.unlines out
              T.isInfixOf "ordinary baseline over 1 run" text @? T.unpack text
              T.isInfixOf "diagnostic runs only" text @? T.unpack text
              not (T.isInfixOf "Monte Carlo over" text) @? T.unpack text
      , testCase "separate output labels make no hard-bound claim" $ do
          case runWith analysis{samples = 8} ["sample (normal 10 0.1)/3"] of
            Left err -> assertFailure (T.unpack err)
            Right out -> do
              let text = T.unlines out
              T.isInfixOf "Monte Carlo: mean" text @? T.unpack text
              T.isInfixOf "stochastic rounding: typical spread" text @? T.unpack text
              not (T.isInfixOf "±" text) @? T.unpack text
          case runWith analysis ["1+1"] of
            Right out -> T.isInfixOf "no variation observed" (T.unlines out) @? show out
            Left err -> assertFailure (T.unpack err)
      ]
 where
  analysis = doubleConfig{rounding = RoundRandom, roundingSamples = 16, samples = 10000}
  get cfg src = either (assertFailure . T.unpack) pure (doubleOf cfg src)
  baselines x = case x.estimate of
    NoSamples -> [x.value]
    Copies l cs -> [cs VU.! i | i <- [0, l.rounds + 1 .. VU.length cs - 1]]
  roundsFor i x = case x.estimate of
    NoSamples -> []
    Copies l cs -> take l.rounds (drop (i * (l.rounds + 1) + 1) (VU.toList cs))
