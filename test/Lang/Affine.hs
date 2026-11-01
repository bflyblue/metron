-- | Affine uncertainty.
module Lang.Affine (
  affineTests,
) where

import Control.Exception (evaluate)
import Control.Monad (foldM)
import Data.Map.Strict qualified as Map (elems, empty)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T (
  drop,
  isInfixOf,
  isPrefixOf,
  length,
  pack,
  unpack,
 )
import Data.Time.Clock.POSIX (getPOSIXTime)
import Lang.Common (
  Tree (Lb, N, O, V),
  caseLimit,
  evalP,
  evalText,
  evalU,
  expectError,
  expecting,
  hashShownAs,
  multiline,
  parseShape,
  runLines,
  runLinesP,
  sessionP,
  typeOfTextP,
 )
import Metron.Affine (
  Magnitude (Affine, Exact),
  Nudge (kind, origin),
  Origin (Declared, Tagged),
  addM,
  cosM,
  divM,
  enclose,
  expM,
  logM,
  midpoint,
  mulM,
  nudges,
  piM,
  radius,
  recipM,
  scaleM,
  sinM,
  sqrtM,
  subM,
  uncertain,
 )
import Metron.Affine qualified as A (Origin (Builtin))
import Metron.Codebase (Codebase (charts, names, typeNames))
import Metron.Core (Hash (..), NudgeKind (Bound, Stat))
import Metron.Driver (Session (codebase), exportSource)
import Metron.Numerical.Approx (isqrt)
import Metron.Syntax qualified as S (Op (Eq, PlusMinus))
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))
import Test.Tasty.QuickCheck (
  NonNegative (NonNegative),
  Positive (Positive),
  Small (Small),
  counterexample,
  testProperty,
  within,
 )

-- Affine arithmetic -----------------------------------------------------------------
--
-- Design §3.2: exact values stay exact, approximations carry rigorous
-- enclosures, declared uncertainty keeps its identity, and printing never
-- shows a digit that is not certain.

{- | Newton's method for Kepler's equation, @E − e sin E = M@, with the
step count as an argument: @ea@ is used four times in each step.
-}
keplerIter :: Text
keplerIter =
  "let keplerIter m e k ea = if k == 0 then ea else keplerIter m e (k - 1) (ea - (ea - e * sin ea * 1 rad - m) / (1 - e * cos ea))"

-- | @k@ steps of 'keplerIter' from @M = 235.4°@, @e = 0.4@.
keplerAt :: Int -> Text
keplerAt k = "keplerIter (235.4 deg) 0.4 " <> T.pack (show k) <> " (235.4 deg)"

-- | The most decimal digits in a numerator or denominator of a magnitude.
longestRational :: Magnitude -> Int
longestRational = \case
  Exact r -> digits r
  Affine m ts s _ -> maximum (digits m : digits s : map (digits . fst) (Map.elems ts))
 where
  digits r = max (length (show (abs (numerator r)))) (length (show (denominator r)))

{- | A position and a velocity built on two shared statistical nudges, so
that their cross-covariance is full: over @(e0, e1)@, @r@ has coefficient
rows @(1, 2)@ and @(3, 0)@, @v@ rows @(0, 1)@ and @(1, -1)@.
-}
correlatedPair :: [Text]
correlatedPair =
  [ "let e = gauss 2"
  , "let r = [e.0 + 2 * e.1, 3 * e.0] m"
  , "let v = [e.1, e.0 - e.1] m/s"
  ]

{- | Design §12, "A filter step in blocks": the lines whose outputs the
document quotes. A change here goes there too.
-}
filterStep :: [Text]
filterStep =
  [ "let eye = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
  , "let r0 = [7000, 0, 0] km ±σ 1 km"
  , "let v0 = [0, 7.5, 0] km/s ±σ 1 m/s"
  , "let r1 = r0 + v0 * (10 s)"
  , "let p1 = jointCovariance (r1, v0)"
  , "p1.rv"
  , ":covariance (r1, v0)"
  , "let dt = 60 s"
  , "let phi = (eye, dt * eye, [0, 0, 0; 0, 0, 0; 0, 0, 0] s^-1, eye)"
  , "let p2 = propagateCov2 phi p1"
  , "p2 == jointCovariance (r1 + v0 * dt, v0)"
  , "p2.rr"
  , "p2.rv"
  , "let h_r = [[1, 0, 0]]"
  , "let h_v = [[0, 0, 0]] s"
  , "let r_meas = [[(10 m)^2]]"
  , "let s_innov = innovationCov2 h_r h_v p2 r_meas"
  , "s_innov"
  , "let k = gain2 h_r h_v p2 (inverse s_innov)"
  , "k"
  , "let p3 = updateCov2 k h_r h_v p2"
  , "p3.rr to m^2"
  , "p3.rv to m^2/s"
  , "p3.vv to m^2/s^2"
  , "transpose p2.rv - snd k @ (h_r @ p2.rr + h_v @ transpose p2.rv) == transpose p3.rv"
  ]

affineTests :: TestTree
affineTests =
  testGroup
    "affine"
    [ testCase "exact values print in full or with an ellipsis" $ do
        evalText "1/3" @?= Right ["0.33333333333333333333…"]
        evalText "sqrt 16" @?= Right ["4"]
        evalText "6.62607015e-34" @?= Right ["6.62607015e-34"]
    , testCase "certain digits of approximations end in an ellipsis, zeros included" $ do
        evalText "sin (1 rad)" @?= Right ["0.84147098480789650665…"]
        evalText "pi" @?= Right ["3.1415926535897932384…"]
        evalText "exp 1" @?= Right ["2.7182818284590452353…"]
        evalText "log 2" @?= Right ["0.69314718055994530941…"]
        evalText "tan (pi/4 * 1 rad)" @?= Right ["1.0000000000000000000…"]
        evalText "sqrt 2 * sqrt 2" @?= Right ["2.0000000000000000000…"]
        evalText "exp (-80)" @?= Right ["1.8048513878454151723…e-35"]
        evalText "sinh 1e-20" @?= Right ["1.0000000000000000000…e-20"]
    , testCase "the same operation twice gives the same nudge, so it cancels" $ do
        evalText "sin (1 rad) - sin (1 rad)" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x - x" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x + 2 * x - 3 * x" @?= Right ["0"]
        evalText "let y = 1 ± 0.1 in y / y" @?= Right ["1"]
    , testCase "a denominator that may be zero is refused before anything cancels" $ do
        evalText "let x = 1 ± 1 in 1 / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in x / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in 0 / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in (3 * x) / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 2 in x / x" @?= Left "error: division by zero"
        -- clear of zero, proportional forms still cancel
        evalText "let x = 2 ± 1.5 in (3 * x) / x" @?= Right ["3"]
    , testCase "equal slack is not a shared unknown, so it does not cancel" $ do
        let anonymous = Affine 2 Map.empty 1 mempty
        case divM 24 anonymous anonymous of
          Right (Exact q) -> assertFailure ("cancelled to " <> show q)
          Right q -> radius q > 0 @? show q
          Left err -> assertFailure (show err)
        -- named nudges beside slack: the slack keeps it from cancelling
        let named = uncertain Bound (Tagged "s" 0) (Exact 2) (Exact (1 / 2))
            withSlack = addM 24 named anonymous
        case divM 24 withSlack withSlack of
          Right (Exact q) -> assertFailure ("cancelled to " <> show q)
          Right q -> radius q > 0 @? show q
          Left err -> assertFailure (show err)
        divM 24 (scaleM 24 3 named) named @?= Right (Exact 3)
    , localOption (mkTimeout 10_000_000)
        $ testCase
          "past 64 nudges, the bound ones beyond the 32 largest fold into slack (design §3.2.7)"
        $ do
          -- 100 plus n bound nudges, b1 .. bn of coefficient i/1000, and m
          -- statistical ones; sqrt adds its own remainder, a nudge smaller
          -- than any of them, and scales the others alike (by 1/20).
          let p = 24
              term k tag i = uncertain k (Tagged tag i) (Exact 0) (Exact (fromIntegral i / 1000))
              form n m =
                foldl
                  (addM p)
                  (Exact 100)
                  ([term Bound "b" i | i <- [1 .. n]] ++ [term Stat "s" i | i <- [1 .. m]])
              rooted n m = either (error . show) id (sqrtM p (form n m))
              slackOf x = radius x - sum (map (abs . fst) (nudges x))
              kept k x = [i | (_, nu) <- nudges x, nu.kind == k, Tagged _ i <- [nu.origin]]
          -- 64 nudges: nothing folds.
          let at64 = rooted 63 0
          length (nudges at64) @?= 64
          slackOf at64 @?= 0
          -- 65: the 32 largest bound nudges stay, the rest are slack.
          let at65 = rooted 64 0
          length (nudges at65) @?= 32
          kept Bound at65 @?= [64, 63 .. 33]
          slackOf at65 >= sum [fromIntegral i / 20000 | i <- [1 .. 32 :: Int]]
            @? show (slackOf at65)
          -- A statistical nudge never folds, however small.
          let mixed = rooted 40 40
          length (kept Stat mixed) @?= 40
          kept Bound mixed @?= [40, 39 .. 9]
    , testCase "remainders of different operand lists never share a nudge" $ do
        -- [1, 12] and [1/11, 2] once ran together as the same bytes
        let remainder operands = enclose "op" 24 operands 1 (Exact 0)
            a = remainder [Exact 1, Exact 12]
            b = remainder [Exact (1 / 11), Exact 2]
        map fst (nudges a) @?= [1]
        subM 24 a b /= Exact 0 @? "the remainders cancelled"
        radius (subM 24 a b) @?= 2
        -- the same operation twice is still one unknown
        subM 24 a (remainder [Exact 1, Exact 12]) @?= Exact 0
        -- an operand's kind and its count are part of the identity
        let x = uncertain Bound (Tagged "s" 0) (Exact 1) (Exact (1 / 2))
        subM 24 (remainder [x]) (remainder [x, Exact 0]) /= Exact 0 @? "count"
    , testCase "declared bounds print as mid ± r" $ do
        evalText "5 ± 0.1" @?= Right ["5.0 ± 0.1"]
        evalText "(5 ± 0.1) * (5 ± 0.1)" @?= Right ["25 ± 1"]
        evalText "(2 ± 0.1) ^ 3" @?= Right ["8.0 ± 1.3"]
        evalText "1e-30 * (1 ± 0.5)" @?= Right ["1.0e-30 ± 5e-31"]
    , testCase "a second-order term below the precision floor never marks" $ do
        -- x (4 − x) is stationary at 2, so its first-order σ cancels
        -- exactly; its second-order term, 1.4e-30, is arithmetic noise at 4
        evalText "let x = 2 ±σ 1e-15 in x * (4 - x)" @?= Right ["4"]
        -- at σ = 1e-3 the term, 1.4e-6, is real and visible
        evalText "let x = 2 ±σ 1e-3 in x * (4 - x)"
          @?= Right
            [ "4 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        -- at a midpoint of zero there is no floor: a square is all second order
        evalText "let n = 0 ±σ 1 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "let n = 0 ±σ 1e-15 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
    , testCase "a shared nudge squares into a one-sided range" $ do
        evalText "let n = noise 1 in n.0 * n.0" @?= Right ["0.5 ± 0.5"]
        evalText "let x = 5 ± 0.1 in x * x" @?= Right ["25 ± 1"]
    , testCase
        "standard uncertainties keep the σ marker and show a bound when it matters"
        $ do
          evalText "6.67430e-11 ±σ 1.5e-15" @?= Right ["6.67430e-11 ±σ 1.5e-15"]
          evalText "(6.67430e-11 ±σ 1.5e-15) * (2 ± 0.1)"
            @?= Right
              [ "1.335e-10 ±σ 3e-15 (bound 6.7e-12) (non-linear: mul: uncertain statistical coefficient, second-order term 5% of the first-order σ; a mean and a σ do not describe it)"
              ]
          -- σ by σ is second order: measured, never a bound (design §3.2)
          evalText "(1 ±σ 0.1) * (1 ±σ 0.1)"
            @?= Right
              [ "1.00 ±σ 0.14 (non-linear: mul, second-order term 7.1% of the first-order σ; a mean and a σ do not describe it)"
              ]
    , testCase "a statistical part non-linear through n*n is marked, never a bound" $ do
        let marked op r = case r of
              Right [v] ->
                T.isInfixOf ("(non-linear: " <> op <> ", ") v
                  && not (T.isInfixOf "0.5 ± 0.5" v)
                  @? T.unpack v
              other -> assertFailure (show other)
            refused what r = case r of
              Left err -> T.isInfixOf what err @? T.unpack err
              Right v -> assertFailure (show v)
        marked "mul" (evalText "let n = 0 ±σ 1 in n * n")
        refused
          "the difference is marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in (n * n) < 2")
        refused
          "sd of a value marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in sd (n * n)")
        refused
          "mid of a value marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in mid (n * n)")
        -- The discarded remainder has no identity: equal linear models
        -- alone cannot prove either equality or cancellation.
        refused "marked non-linear" (evalText "let n = 0 ±σ 1 in (n * n) == (n * n)")
        evalText "let n = 0 ±σ 1 in bound (n * n)" @?= Right ["0"]
        -- the mark propagates
        marked "mul" (evalText "let n = 0 ±σ 1 in n * n + 5")
        -- a σ of zero after a non-linear step prints as no certainty
        evalText "let n = 0 ±σ 1 in n * n + 5"
          @?= Right
            [ "5 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "let n = 0 ±σ 1 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        marked "mul" (evalText "let n = 0 ±σ 1 in sqrt (n * n + 5)")
        -- :budget names the operation
        expecting (runLines [":budget let n = 0 ±σ 1 in n * n"]) $ \out ->
          any (T.isInfixOf "non-linear: mul, second-order term unbounded") out @? show out
    , testCase "discarded statistical remainders cannot establish exact equality" $ do
        let refused src = case evalText src of
              Left err -> T.isInfixOf "marked non-linear" err @? T.unpack err
              Right out -> assertFailure (show out)
        refused "let n = 0 ±σ 1 in n*n == 0"
        refused "let n = 0 ±σ 1 in let q = 0 ±σ 2 in n*n == q*q"
        refused "let n = 0 ±σ 1 in sin (n * rad) == n"
        refused "let n = 0 ±σ 1 in sinh n == n"
        refused "sd (sinh (0 ±σ 10))"
        refused "let n = 0 ±σ 1 in sd ((1 ± 1) * n)"
        refused "let n = 0 ±σ 1 in covariance [(1 ± 1) * n]"
        refused "let n = 0 ±σ 1 in crossCovariance [n*n] [n]"
        -- Even below the warning threshold, a discarded remainder
        -- prevents an exact equality proof.
        refused "let n = 0 ±σ 0.00001 in sin (n * rad) == n"
        evalText "let n = 0 ±σ 1 in n - n" @?= Right ["0"]
    , testCase "expm refuses statistical inputs instead of erasing them" $ do
        let refused src = case evalP src of
              Left err ->
                T.isInfixOf "expm with statistical uncertainty is not supported" err
                  @? T.unpack err
              Right out -> assertFailure (show out)
        refused "let n = 0 ±σ 1 in expm [n, 0; 0, 0]"
        refused "let n = 0 ±σ 1 in expm [0, n; -n, 0]"
        refused "let n = 0 ±σ 1 in expm [n*n, 0; 0, 0]"
    , testCase "a small relative σ stays first order and unmarked" $ do
        let g = "(6.67430e-11 ±σ 1.5e-15)"
        evalText ("sqrt " <> g) @?= Right ["8.169639e-6 ±σ 9.2e-11"]
        evalText (g <> " * " <> g) @?= Right ["4.45463e-21 ±σ 1.4e-25"]
        evalText ("sin (" <> g <> " * 1 rad)") @?= Right ["6.67430e-11 ±σ 1.5e-15"]
        evalText "sqrt (100 ±σ 1)" @?= Right ["10.00 ±σ 0.05"]
        -- the delta method's second-order term, |f''|·σ² against |f'|·σ
        evalText "exp (0 ±σ 0.1)"
          @?= Right
            [ "1.0 ±σ 0.1 (non-linear: exp, second-order term 11% of the first-order σ; a mean and a σ do not describe it)"
            ]
        evalText "sqrt (100 ±σ 10)"
          @?= Right
            [ "10.0 ±σ 0.5 (non-linear: sqrt, second-order term 5.4% of the first-order σ; a mean and a σ do not describe it)"
            ]
        -- the threshold is a setting
        runLines [":set nonlinear 10", "(1 ±σ 0.1) * (1 ±σ 0.1)"]
          @?= Right ["1.00 ±σ 0.14"]
    , testCase "a statistical coefficient is never a hard limit" $ do
        -- no division by zero: the bound enclosure excludes zero
        evalText "1 / (1 ±σ 1)"
          @?= Right
            [ "1 ±σ 1 (non-linear: recip, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "abs (1 ±σ 0.1)" @?= Right ["1.0 ±σ 0.1"]
        -- integer rounding is a comparison, decided at the stated sigma
        evalText "floor (2.5 ±σ 0.1)" @?= Right ["2"]
        case evalText "floor (2.5 ±σ 0.17)" of
          Left err -> T.isInfixOf "straddles a rounding boundary" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "mid, bound and sd take an enclosure apart" $ do
        let parts x = map (\f -> evalP (f <> " (" <> x <> ")")) ["mid", "bound", "sd"]
        parts "1 ± 0.1" @?= [Right ["1"], Right ["0.1"], Right ["0"]]
        parts "1 ±σ 0.1" @?= [Right ["1"], Right ["0"], Right ["0.1"]]
        parts "(1 ± 0.1) + (2 ± 0.2)" @?= [Right ["3"], Right ["0.3"], Right ["0"]]
        parts "(1 ±σ 0.1) * 2 + (1 ± 0.05)"
          @?= [Right ["3"], Right ["0.05"], Right ["0.2"]]
        parts "5" @?= [Right ["5"], Right ["0"], Right ["0"]]
        parts "1/3" @?= [Right ["0.33333333333333333333…"], Right ["0"], Right ["0"]]
        -- the bound of a nonlinear result is the printed one
        evalP "bound ((5 ± 0.1) * (5 ± 0.1))" @?= Right ["1.01"]
        -- the operand's dimension and display unit
        evalP "bound (10 mm ± 0.1 mm)" @?= Right ["0.1 mm"]
        evalP "mid (10 mm ± 0.1 mm)" @?= Right ["10 mm"]
        evalP "sd (2 km ±σ 3 m)" @?= Right ["0.003 km"]
        -- elementwise on tensors
        evalP "bound ([1, 2] m ± 0.1 m)" @?= Right ["[0.1, 0.1] m"]
        evalP "mid ([1, 2; 3, 4] ±σ 0.5)" @?= Right ["[1, 2; 3, 4]"]
        evalP "sd ([1, 2] ±σ 0.5)" @?= Right ["[0.5, 0.5]"]
        -- σ is a square root: exact when the variance is a square, an
        -- enclosure otherwise
        case evalP "sd ((1 ±σ 0.1) + (1 ±σ 0.1 #other))" of
          Right [v] -> T.isPrefixOf "0.1414213562" v @? T.unpack v
          other -> assertFailure (show other)
        typeOfTextP "mid" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "bound" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "sd" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "bound (1 m ± 1 cm)" @?= Right "Num m"
        -- a policy of one's own: consistent within the bound and three σ
        runLinesP
          [ "let consistent a b = let d = a - b in abs (mid d) <= bound d + 3 * sd d"
          , "consistent (5 ± 0.1) (5.05)"
          , "consistent (5 ±σ 0.01) (5.1)"
          ]
          @?= Right ["true", "false"]
    , testCase "sigma a e is the prefix spelling of a ±σ e, beside within" $ do
        evalP "sigma 1 0.1" @?= Right ["1.0 ±σ 0.1"]
        evalP "1 `sigma` 0.1" @?= evalP "1 ±σ 0.1"
        evalP "sd (sigma 1 0.1)" @?= Right ["0.1"]
        runLinesP ["let x = sigma 1 0.1", ":view x"] @?= Right ["x = 1 ±σ 0.1"]
        -- it declares an uncertainty, so a #label may follow it
        evalP "(sigma 1 0.1 #a) - (1 ±σ 0.1 #a)" @?= Right ["0"]
        -- and, like within, it is not a unit
        case evalP "3 sigma" of
          Left err -> T.isInfixOf "not a unit or a chart: write the `*`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "noise and gauss are vectors of unit nudges" $ do
        evalText "noise 2" @?= Right ["[0 ± 1, 0 ± 1]"]
        evalText "gauss 1" @?= Right ["[0 ±σ 1]"]
        evalText "noise 2 · noise 2" @?= Right ["0 ± 2"]
        case evalText "noise x" of
          Left err -> T.isInfixOf "literal natural number" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testCase "tiny magnitudes keep their significant digits" $ do
        evalText "sqrt (1e-68 * (1 ± 1e-10))" @?= Right ["1.00000000000e-34 ± 5e-45"]
        evalText "sin (1e-20 rad)" @?= Right ["1.0000000000000000000…e-20"]
    , testCase "comparisons are decided only when the enclosures separate" $ do
        evalText "5 ± 0.1 < 6" @?= Right ["true"]
        evalText "let x = 5 ± 0.1 in x == x" @?= Right ["true"]
        evalText "5 ± 0.1 < 5.05"
          @?= Left
            "error: cannot decide comparison at sigma 3: the difference is -5.0e-2 ± 0.1"
        evalText "5 ±σ 0.1 < 5.4" @?= Right ["true"]
        evalText "5 ±σ 0.1 < 5.2"
          @?= Left
            "error: cannot decide comparison at sigma 3: the difference is -0.2 ± 0.0 ±σ 0.1"
        evalText "abs (sqrt 2 * sqrt 2 - 2) < 1e-9" @?= Right ["true"]
    , testCase ":set sigma widens the margin for statistical nudges only" $ do
        runLines [":set sigma 1", "5 ±σ 0.1 < 5.2"] @?= Right ["true"]
        runLines [":set sigma 1", "5 ± 0.1 < 5.05"]
          @?= Left
            "error: cannot decide comparison at sigma 1: the difference is -5.0e-2 ± 0.1"
    , testCase "integer rounding needs an enclosure inside one step" $ do
        evalText "floor (2.5 ± 0.1)" @?= Right ["2"]
        evalText "floor (2.5 ± 0.6)"
          @?= Left
            "error: cannot decide floor of an enclosure that straddles a rounding boundary"
    , testCase "domain errors name the problem" $ do
        evalText "sqrt (0 ± 1)" @?= Left "error: sqrt of a value that may be negative"
        evalText "log 0" @?= Left "error: log of a value that may be zero or negative"
        evalText "1 / (1 ± 2)" @?= Left "error: division by zero"
        evalText "asin 1" @?= Right ["1.5707963267948966192… rad"]
    , testCase "abs, atan2 and the hyperbolics" $ do
        evalText "abs (0 ± 1)" @?= Right ["0.5 ± 0.5"]
        evalText "abs ((5 ± 0.1) - 7)" @?= Right ["2.0 ± 0.1"]
        evalText "atan2 1 1" @?= Right ["0.78539816339744830961… rad"]
        evalText "atan2 (-1) (-1)" @?= Right ["-2.3561944901923449288… rad"]
        evalText "acos 0" @?= Right ["1.5707963267948966192… rad"]
        evalText "cosh 0" @?= Right ["1"]
        evalText "tanh 1" @?= Right ["0.76159415595576488811…"]
    , testCase "linear algebra over enclosures" $ do
        evalText "det [[1, 2], [3, 4]]" @?= Right ["-2"]
        evalText "det [[1 ± 0.01, 2], [3, 4]]" @?= Right ["-2.00 ± 0.04"]
        evalText "inverse [[1, 2], [3, 4]]" @?= Right ["[-2, 1; 1.5, -0.5]"]
        evalText "inverse [[1, 2], [3, 4]] · [[1, 2], [3, 4]]"
          @?= Right ["[1, 0; 0, 1]"]
        evalText "inverse [[1, 1], [1, 1]]"
          @?= Left "error: inverse of a singular matrix"
        evalText "inverse [[1 ± 1, 2], [3, 4]]"
          @?= Left "error: cannot decide inverse of a matrix whose enclosure may be singular"
        evalText "det [[0, 0], [0, 0]]" @?= Right ["0"]
        -- det is polymorphic in the size, with no static size check, and is
        -- on dimensionless matrices only (design §4.3, §4.6).
        typeOfTextP "det" @?= Right "forall n a. Mat n a -> Num"
        typeOfTextP "\\a -> det a + 1" @?= Right "forall n a. Mat n a -> Num"
        runLinesP ["let d a = det a", "d [[2, 0, 0], [0, 3, 0], [0, 0, 4]] + d [[2]]"]
          @?= Right ["26"]
        evalP "det ([[1 m, 0 m], [0 m, 2 m]] / (1 m))" @?= Right ["2"]
        case evalP "det [[1 m, 0 m], [0 m, 1 m]]" of
          Left err ->
            T.isInfixOf "expected Mat n n, got Mat 2 2 m: dimensions differ by 1/m" err
              @? T.unpack err
          Right v -> assertFailure (show v)
        evalText "norm [3, 4]" @?= Right ["5"]
        evalText "norm [1, 1, 1]" @?= Right ["1.7320508075688772935…"]
    , testCase ":set precision changes the digits printed and the working precision" $ do
        runLines [":set precision 5", "pi", "1/3", "5 ± 0.1"]
          @?= Right ["3.1415…", "0.33333…", "5.0 ± 0.1"]
        runLines [":set precision 40", "pi"]
          @?= Right ["3.141592653589793238462643383279502884197…"]
    , testCase ":exact shows the midpoint, the nudges and their origins" $ do
        evalText ":exact 2 ± 0.1" @?= Right ["2 + 0.1·e[bound, input]"]
        runLines ["let x = 5 ± 0.1", ":exact x"] @?= Right ["5 + 0.1·e[bound, x]"]
        case evalText ":exact sin (1 rad)" of
          Right [out] ->
            T.isPrefixOf "0.84147098480789650665… + " out
              && T.isInfixOf "·e[bound, sin]" out
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase ":budget lists nudges by kind, source and share"
        $ runLines ["let f x = sqrt x ± 1e-9", ":budget f 2"]
          @?= Right
            [ "1.4142135624 ± 1.4e-9"
            , "  kind   source  contribution  share"
            , "  bound  f @0    1e-9          100% of bound"
            , "  bound  sqrt    9.3e-28       0% of bound"
            ]
    , testCase "the library's G carries its σ and a mass derived from it inherits it" $ do
        evalU ["astro"] "G" @?= Right ["6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
        evalU ["astro"] "iau2015.earth.mu / G" @?= Right ["5.97217e24 ±σ 1.3e20 kg"]
        case evalU ["astro"] ":budget iau2015.earth.mu / G" of
          Right (_ : _ : row : _) -> T.isInfixOf "σ      G" row && T.isInfixOf "100% of σ²" row @? T.unpack row
          other -> assertFailure (show other)
    , testCase "a unit is its own term: an amount of the same size is not one" $ do
        runLinesP ["let x = 1", "x + 2"] @?= Right ["3"]
        -- A unit's declaration makes its body a unit (design §3.10, U7), so
        -- the unit and the amount it was declared from are two terms.
        runLinesP
          [ "unit dozen = 12"
          , "let eggs = 12"
          , "3 dozen"
          , "eggs + 1"
          , ":hash dozen"
          , ":type 1 dozen"
          , ":type eggs"
          ]
          @?= Right ["3 dozen", "13", "#" <> dozenHash, "Num", "Num"]
        hashes <-
          either
            (assertFailure . T.unpack)
            pure
            (runLinesP ["unit dozen = 12", "let eggs = 12", ":hash dozen", ":hash eggs"])
        case hashes of
          [d, e] -> (d /= e) @? "a unit and an amount share a hash"
          other -> assertFailure (show other)
        case runLinesP ["let x = 1", "5 x"] of
          Left err -> T.isInfixOf "`x` is a Num, not a unit or a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
        -- Bq and Hz are one definition and two units; each prints as written.
        runLinesP ["5 Bq", "5 Hz", "1 Bq == 1 Hz"] @?= Right ["5 Bq", "5 Hz", "true"]
    , testCase "a let that rebinds a unit name makes it a quantity"
        $ runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2", "2 g"]
          @?= Left
            "error at 1:3\n  2 g\n    ^\n  `g` is a Num (m/s^2), not a unit or a chart: write the `*`"
    , testCase
        "an alias of a unit is a unit, and a renamed unit prints under its new name"
        $ runLinesP
          [ ":alias klick km"
          , "5 klick"
          , "let d = 5 km"
          , ":add"
          , ":unname km"
          , "d"
          , ":view d"
          ]
          @?= Right
            [ "`klick` now also names #" <> kmHash
            , "5 klick"
            , "added d"
            , "removed the label `km`"
            , "5 klick"
            , "d = 5 klick"
            ]
    , testCase ":prefer sets a display unit per dimension; to still wins; it persists" $ do
        runLinesP
          [ ":prefer km/h"
          , "5 m/s"
          , "100 km / (2 h)"
          , "5 m/s to m/s"
          , "3 m + 2 m"
          , ":prefer m/s"
          , ":prefer"
          , "5 km/h"
          , ":unprefer m/s"
          , "5 km/h"
          ]
          @?= Right
            [ "values of dimension m/s print in km/h"
            , "18 km h^-1"
            , "50 km h^-1"
            , "5 m s^-1"
            , "5 m"
            , "values of dimension m/s print in m/s"
            , "prefer m/s"
            , "1.3888888888888888888… m s^-1"
            , "removed the preference m/s"
            , "5 km h^-1"
            ]
        -- A preference is a unit (design §3.10, U7), not an amount.
        case evalP ":prefer 5" of
          Left err -> T.isInfixOf "expected unit syntax" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP ":prefer 1 km/h" of
          Left err -> T.isInfixOf "expected unit syntax" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "± on tensors: one independent nudge per component" $ do
        evalP "[1, 1, 1] m ± 0.1 m" @?= Right ["[1.0 ± 0.1, 1.0 ± 0.1, 1.0 ± 0.1] m"]
        runLinesP ["let v = [1, 1, 1] m ± 0.1 m", "v.0 - v.1", "v - v"]
          @?= Right ["0.0 ± 0.2 m", "[0, 0, 0] m"]
        evalP "[1, 2] ± [0.1, 0.2]" @?= Right ["[1.0 ± 0.1, 2.0 ± 0.2]"]
        case evalP "[1, 2] ± [0.1, 0.2, 0.3]" of
          Left err -> T.isInfixOf "shape and dimension of the value" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "covariance is the square-root factor's product; cholesky inverts it" $ do
        evalP "let x = gauss 2 in covariance [x.0 + 3 * x.1, 2 * x.0]"
          @?= Right ["[10, 2; 2, 4]"]
        evalP "cholesky [[4, 2], [2, 10]]" @?= Right ["[2, 0; 1, 3]"]
        evalP "cholesky [[4, 2], [2, 3]]"
          @?= Right ["[2, 0; 1, 1.4142135623730950488…]"]
        evalP "cholesky [[1, 2], [2, 1]]"
          @?= Left "error: sqrt of a value that may be negative"
        typeOfTextP "covariance" @?= Right "forall n d. Vec n d -> Mat n n (d^2)"
        typeOfTextP "cholesky" @?= Right "forall n a d. Mat n a (d^2) -> Mat n a d"
    , testCase "cholesky and ±σ refuse a matrix that is provably not symmetric" $ do
        evalP "cholesky [1, 100; 0, 1]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.1 and .1.0 differ"
        evalP "[0, 0] ±σ [1, 100; 0, 1]"
          @?= Left "error: ±σ needs a symmetric covariance: entries .0.1 and .1.0 differ"
        evalP "cholesky [4, 0, 1; 0, 4, 0; 2, 0, 4]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.2 and .2.0 differ"
        -- enclosures that do not overlap
        evalP "cholesky [4, 2 ± 0.1; 3, 3]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.1 and .1.0 differ"
        -- Overlap is not proof of symmetry.
        evalP "cholesky [4, 2 ± 0.1; 2, 3]"
          @?= Left
            "error: cholesky needs a symmetric matrix: symmetry of entries .0.1 and .1.0 cannot be established"
        evalP "[0, 0] m ±σ [1, 0.5; 0.5, 1] m^2" @?= Right ["[0 ±σ 1, 0 ±σ 1] m"]
    , testCase "v ±σ P is a vector with covariance P, stamped like any ±" $ do
        runLinesP
          [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "w"
          , "covariance w"
          , ":covariance w"
          ]
          @?= Right
            [ "[0 ±σ 2, 0.0 ±σ 3.2] m"
            , "[4, 2; 2, 10] m^2"
            , "covariance [4, 2; 2, 10] m^2"
            , "bound box [0, 0] m"
            ]
        runLinesP
          [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "let w2 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "covariance (w - w2)"
          ]
          @?= Right ["[8, 4; 4, 20] m^2"]
        runLinesP
          [ "let w3 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2 #gps"
          , "let w4 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2 #gps"
          , "w3 - w4"
          ]
          @?= Right ["[0, 0] m"]
        case evalP "[0, 0] m ± [[4, 2], [2, 10]] m^2" of
          Left err -> T.isInfixOf "a bound has no covariance" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase ":covariance separates the statistical part from the bound box" $ do
        evalP ":covariance 5 ±σ 0.1" @?= Right ["variance 0.01", "bound 0"]
        runLinesP ["let t = 45 deg ± 0.001 rad", ":covariance [cos t, sin t, 0] km"]
          @?= Right
            [ "covariance [0, 0, 0; 0, 0, 0; 0, 0, 0] km^2"
            , "bound box [0.00071, 0.00071, 0] km"
            ]
    , testCase
        "crossCovariance sums cᵢc'ⱼᵀ over the statistical nudges two vectors share"
        $ do
          -- Over (e0, e1): r has rows (1, 2) and (3, 0), v rows (0, 1) and
          -- (1, -1), so Cov(r, v) = [1·0 + 2·1, 1·1 + 2·(-1); 3·0, 3·1].
          runLinesP
            ( correlatedPair
                ++ [ "crossCovariance r v"
                   , "crossCovariance v r == transpose (crossCovariance r v)"
                   , "crossCovariance r r == covariance r"
                   ]
            )
            @?= Right ["[2, -1; 0, 3] m^2 s^-1", "true", "true"]
          -- Correlated nudges from a covariance matrix.
          runLinesP
            [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
            , "crossCovariance w w == covariance w"
            , "crossCovariance w w"
            ]
            @?= Right ["true", "[4, 2; 2, 10] m^2"]
          -- Independent vectors: all zeros, in the product of the dimensions.
          runLinesP
            [ "crossCovariance ([1, 2] m ±σ 1 m) ([3, 4, 5] s ±σ 1 s)"
            , ":type crossCovariance ([1, 2] m ±σ 1 m) ([3, 4, 5] s ±σ 1 s)"
            , "crossCovariance ([1, 2] km ±σ 1 m) ([1, 2] h ±σ 1 s)"
            ]
            @?= Right ["[0, 0, 0; 0, 0, 0] m s", "Mat 2 3 (m*s)", "[0, 0; 0, 0] km h"]
          -- A shared bound nudge is no covariance.
          evalP "crossCovariance ([1, 2] m ± 1 m #a) ([3, 4] m ± 1 m #a)"
            @?= Right ["[0, 0; 0, 0] m^2"]
          typeOfTextP "crossCovariance"
            @?= Right "forall n d m d1. Vec n d -> Vec m d1 -> Mat n m (d*d1)"
    , testCase "jointCovariance and the block filter: the types" $ do
        typeOfTextP "jointCovariance"
          @?= Right "forall n d d1. (Vec n d, Vec n d1) -> Cov2 n d d1"
        typeOfTextP "Cov2"
          @?= Right
            "forall n d d1. Mat n n (d^2) -> Mat n n (d*d1) -> Mat n n (d1^2) -> Cov2 n d d1"
        typeOfTextP "propagateCov2"
          @?= Right
            "forall n m d d1 d2 d3. (Mat n m (d1*d2*d3/d^2), Mat n m (d1*d3^2/d^2), Mat n m d2, Mat n m d3) -> Cov2 m (d/d2) (d/d3) -> Cov2 n (d1*d3/d) d"
        typeOfTextP "innovationCov2"
          @?= Right
            "forall n m d d1 d2. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Mat n n (d1^2*d2^2) -> Mat n n (d1^2*d2^2)"
        typeOfTextP "gain2"
          @?= Right
            "forall n m d d1 d2 s d3. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Tensor (n : s) d3 -> (Tensor (m : s) (d1^2*d2^2*d3/d), Tensor (m : s) (d1*d2^2*d3))"
        typeOfTextP "updateCov2"
          @?= Right
            "forall n m d d1 d2. (Mat n m d, Mat n m (d1^2/d2)) -> Mat m n (1/d) -> Mat m n (d2/d1^2) -> Cov2 n (d*d2/d1) d1 -> Cov2 n (d*d2/d1) d1"
    , testCase "propagateCov2 agrees exactly with the affine forms' own correlation" $ do
        runLinesP
          ( correlatedPair
              ++ [ "let p = jointCovariance (r, v)"
                 , "p"
                 , "let eye = [[1, 0], [0, 1]]"
                 , -- Φ = I is the identity on the record.
                   "propagateCov2 (eye, [[0, 0], [0, 0]] s, [[0, 0], [0, 0]] s^-1, eye) p == p"
                 , -- Φ = [I, Δt I; 0, I]: the blocks of Φ P Φᵀ against the
                   -- covariance of (r + v Δt, v) read off the nudges.
                   "propagateCov2 (eye, 10 s * eye, [[0, 0], [0, 0]] s^-1, eye) p == jointCovariance (r + v * (10 s), v)"
                 , -- A Φ with every block full and of its own dimension.
                   "let f_rr = [[1, 2], [0, 1]]"
                 , "let f_rv = [[3, 0], [1, 1]] s"
                 , "let f_vr = [[0, 1], [2, 0]] s^-1"
                 , "let f_vv = [[1, 0], [1, 1]]"
                 , "propagateCov2 (f_rr, f_rv, f_vr, f_vv) p"
                 , "jointCovariance (f_rr @ r + f_rv @ v, f_vr @ r + f_vv @ v)"
                 , "propagateCov2 (f_rr, f_rv, f_vr, f_vv) p == jointCovariance (f_rr @ r + f_rv @ v, f_vr @ r + f_vv @ v)"
                 ]
          )
          @?= Right
            [ "Cov2 {rr = [5, 3; 3, 9] m^2, rv = [2, -1; 0, 3] m^2 s^-1, vv = [1, -1; -1, 2] m^2 s^-2}"
            , "true"
            , "true"
            , "Cov2 {rr = [74, 28; 28, 16] m^2, rv = [26, 41; 12, 12] m^2 s^-1, vv = [10, 13; 13, 25] m^2 s^-2}"
            , "Cov2 {rr = [74, 28; 28, 16] m^2, rv = [26, 41; 12, 12] m^2 s^-1, vv = [10, 13; 13, 25] m^2 s^-2}"
            , "true"
            ]
    , testCase
        ":covariance of a pair prints the blocks of jointCovariance and both boxes"
        $ do
          expecting
            ( runLinesP
                ( correlatedPair
                    ++ [ ":covariance (r, v)"
                       , "let p = jointCovariance (r, v)"
                       , "p.rr"
                       , "p.rv"
                       , "p.vv"
                       ]
                )
            )
            $ \outs -> do
              take 4 outs
                @?= [ "rr [5, 3; 3, 9] m^2"
                    , "rv [2, -1; 0, 3] m^2 s^-1"
                    , "vv [1, -1; -1, 2] m^2 s^-2"
                    , "bound box ([0, 0] m, [0, 0] m s^-1)"
                    ]
              map (T.drop 3) (take 3 outs) @?= drop 4 outs
          runLinesP [":covariance ([1, 2] m ± 0.5 m, [3, 4] m/s ±σ 1 m/s)"]
            @?= Right
              [ "rr [0, 0; 0, 0] m^2"
              , "rv [0, 0; 0, 0] m^2 s^-1"
              , "vv [1, 0; 0, 1] m^2 s^-2"
              , "bound box ([0.5, 0.5] m, [0, 0] m s^-1)"
              ]
          evalP ":covariance ([1, 2] m, [[1]])"
            @?= Left "covariance: a number, a vector, or a pair of vectors"
    , testCase "design §12: a filter step in blocks"
        $ runLinesP filterStep
          @?= Right
            [ "[1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1"
            , "rr [1.0001, 0, 0; 0, 1.0001, 0; 0, 0, 1.0001] km^2"
            , "rv [1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1"
            , "vv [1e-6, 0, 0; 0, 1e-6, 0; 0, 0, 1e-6] km^2 s^-2"
            , "bound box ([0, 0, 0] km, [0, 0, 0] km s^-1)"
            , "true"
            , "[1.0049, 0, 0; 0, 1.0049, 0; 0, 0, 1.0049] km^2"
            , "[7e-5, 0, 0; 0, 7e-5, 0; 0, 0, 7e-5] km^2 s^-1"
            , "[[1005000]] m^2"
            , "([0.99990049751243781094…; 0; 0], [6.9651741293532338308…e-5; 0; 0] s^-1)"
            , "[99.990049751243781094…, 0, 0; 0, 1004900, 0; 0, 0, 1004900] m^2"
            , "[0.0069651741293532338308…, 0, 0; 0, 70, 0; 0, 0, 70] m^2 s^-1"
            , "[0.99512437810945273631…, 0, 0; 0, 1, 0; 0, 0, 1] m^2 s^-2"
            , "true"
            ]
    , testCase "points: charts, .+ and .-, printing on the written chart" $ do
        evalP "20 degC" @?= Right ["20 degC"]
        evalP "20 °C .+ 5 K" @?= Right ["25 degC"]
        evalP "20 degC .+ 9 deltaF" @?= Right ["25 degC"]
        evalP "77 °F .- 68 °F" @?= Right ["9 deltaF"]
        evalP "20 degC to degF" @?= Right ["68 degF"]
        evalP "(25 degC .- 20 degC) to K" @?= Right ["5 K"]
        evalP "100 degC .- (32 degF to degC)" @?= Right ["100 K"]
        evalP "0 kelvin to degC" @?= Right ["-273.15 degC"]
        evalP "0 J2000 to JD" @?= Right ["2451545 JD"]
        evalP "(0 J2000 .+ 365.25 day) .- 0 J2000" @?= Right ["365.25 day"]
        evalP "20 degC to kelvin" @?= Right ["293.15 kelvin"]
        -- Two frames are two types (design §3.10, F5): convert first.
        expectError
          (evalP "100 degC .- 32 degF")
          "points on degC and degF: convert one with `to`"
    , testCase "points over vectors: frames, projection, conversion between frames" $ do
        runLinesP
          [ "space Lab = Vec 3 m"
          , "chart site on Lab at [100, 200, 0] m"
          , "[1, 2, 3] site"
          , ":type [1, 2, 3] site"
          , "([1, 2, 3] site) .- ([0, 0, 0] site)"
          , "([1, 2, 3] site) .+ [1, 1, 1] km"
          , "([1, 2, 3] site).0"
          , ":type ([1, 2, 3] site).0"
          , "[1, 2, 3] site == [1, 2, 3] site"
          , -- a chart in km, translated from site, is on site's axes
            "chart ground on site at [-100, -200, 0] m step km"
          , "[7000, 0, 0] ground to site"
          , -- two roots on one space convert (design §3.10, F2)
            "chart bench on Lab"
          , "[0, 0, 0] site to bench"
          ]
          @?= Right
            [ "[1, 2, 3] site"
            , "Point site"
            , "[1, 2, 3] m"
            , "[1001, 1002, 1003] site"
            , "1 m"
            , "Num m"
            , "true"
            , "[6999900, -200, 0] site"
            , "[100, 200, 0] bench"
            ]
        -- Roots on two spaces never meet.
        expectError
          ( runLinesP
              [ "space Lab = Vec 3 m"
              , "space Sky = Vec 3 m"
              , "chart site on Lab at [100, 200, 0] m"
              , "chart eci on Sky step km"
              , "[7000, 0, 0] eci to site"
              ]
          )
          "frames of two spaces, Sky and Lab"
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "forall c. Point c -> Diff c -> Point c"
        case runLinesP
          ["space Lab = Vec 3 m", "chart site on Lab", "[1, 2, 3] site + [1, 1, 1] m"] of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case runLinesP
          ["space Lab = Vec 3 m", "chart site on Lab", "[1, 2, 3] site < [2, 3, 4] site"] of
          Left err -> T.isInfixOf "no ordering on Point site" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "points compare and have no sum" $ do
        evalP "20 degC < (70 degF to degC)" @?= Right ["true"]
        evalP "20 degC == (68 degF to degC)" @?= Right ["true"]
        evalP "0 J2000 < (0 MJD to J2000)" @?= Right ["false"]
        typeOfTextP "20 degC" @?= Right "Point degC"
        typeOfTextP "degC" @?= Right "Chart degC"
        typeOfTextP "\\p q -> p .- q"
          @?= Right "forall c. Point c -> Point c -> Diff c"
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "forall c. Point c -> Diff c -> Point c"
        typeOfTextP "\\a b -> a < b" @?= Right "forall d. Num d -> Num d -> Bool"
        case evalP "20 degC + 5 degC" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "2 * (20 degC)" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "20 degC to K" of
          Left err -> T.isInfixOf "to with a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "[1, 2] < [1, 3]" of
          Left err -> T.isInfixOf "no ordering on Vec 2" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "chart declarations: user charts, :view and :edit read back as written" $ do
        runLinesP
          [ "unit mmHg = 133.322 Pa"
          , "space ISA = Num Pa"
          , "chart bp on ISA step mmHg"
          , "120 bp .+ 10 mmHg"
          , "(120 bp .- 80 bp)"
          ]
          @?= Right ["130 bp", "40 mmHg"]
        runLinesP ["let boil = 100 degC", ":view boil"] @?= Right ["boil = 100 degC"]
        -- The library lives in namespaces, so :edit prints its definitions in their block.
        runLinesP [":edit degC"]
          @?= Right ["namespace temperature", "  chart degC on ITS90 at 273.15 K"]
        runLinesP [":edit km"]
          @?= Right ["namespace si", "  unit km = kilo * 1 metre"]
    , testCase
        "chart is a keyword: a declaration, its type, :view and :ls"
        $ do
          runLinesP
            [ "unit mmHg = 133.322 Pa"
            , "space ISA = Num Pa"
            , "chart bp on ISA step mmHg"
            , "120 bp .+ 10 mmHg"
            , ":type bp"
            , ":view bp"
            , ":ls --charts bp"
            , "bp"
            ]
            @?= Right
              [ "130 bp"
              , "Chart bp"
              , "chart bp on ISA step mmHg"
              , "chart bp : Chart bp"
              , "chart bp"
              ]
          typeOfTextP "\\c -> (c :: Chart degC)"
            @?= Right "Chart degC -> Chart degC"
          -- `chart` is a keyword, not a name.
          case runLinesP ["let chart = 3"] of
            Left _ -> pure ()
            Right v -> assertFailure (show v)
          expectError
            (runLinesP ["chart bp at 0 K"])
            "name its space: `chart … on ITS90`"
    , testCase
        "mkRoot and mkChart: a frame, a parent, a list of generators, antisymmetry"
        $ do
          let inertial = "space GCRS = Vec 3 m"
              eci = "chart eci on GCRS"
          -- A chart's frame is its declaration's (design §3.10, F3): the
          -- primitive takes the minted constructor no source can write.
          expectError
            (runLinesP [inertial, eci, "data Eci = Eci", "mkChart {Eci} {} eci {} {} {} {}"])
            "mkChart takes the frame a chart declaration mints first"
          typeOfTextP "rotationOf"
            @?= Right "forall s (c : s). Chart c -> Mat s c"
          -- A generator: exact, or scaled by an approximate angle, is a bivector.
          let turnedBy gs = [inertial, eci, "chart t on eci at [1, 0, 0] m by " <> gs, "[0, 0, 0] t"]
          runLinesP (turnedBy "[0, -1, 0; 1, 0, 0; 0, 0, 0]") @?= Right ["[0, 0, 0] t"]
          runLinesP (turnedBy "[0, -1, 0; 1, 0, 0; 0, 0, 0] * pi / 6")
            @?= Right ["[0, 0, 0] t"]
          let refused lines' needle = case runLinesP lines' of
                Left err -> T.isInfixOf needle err @? T.unpack err
                Right v -> assertFailure (show v)
          refused
            (turnedBy "[0, 1, 0; 1, 0, 0; 0, 0, 0]")
            "the generator of a chart must be antisymmetric: a bivector, such as rotz θ or a ∧ b"
          -- Every generator of the list is checked.
          refused
            (turnedBy "rotz (30 deg) then [1, 0, 0; 0, 0, 0; 0, 0, 0]")
            "must be antisymmetric"
          -- The type cannot tell a turned chart from another, so `rotationOf`
          -- is exactly the identity on one that is not turned.
          runLinesP [inertial, eci, "rotationOf eci == [1, 0, 0; 0, 1, 0; 0, 0, 1]"]
            @?= Right ["true"]
          -- The parent's dimension and shape, and the generator's size, are the child's.
          refused
            [inertial, eci, "chart k on eci at 0 K"]
            "expected Vec GCRS m, got Num K"
          refused [inertial, eci, "chart k on eci at [1, 2] m"] "lengths differ: 3 and 2"
          refused (turnedBy "[0, 1; -1, 0]") "lengths differ: 3 and 2"
          -- A space of numbers has no axes to turn.
          refused
            ["chart tilt on degC by rotz (30 deg)"]
            "a chart on a space of numbers has no axes to turn"
    , testCase "charts with a parent: the translated tree, to and .- through it" $ do
        -- design §3.8's hierarchy without the rotations
        let tree =
              [ "space GCRS = Vec 3 m"
              , "chart eci on GCRS"
              , "chart site on eci at [6378, 0, 0] km"
              , "chart antenna on site at [2, 0, 1] m"
              ]
        runLinesP
          ( tree
              ++ [ "[1, 2, 3] antenna to eci"
                 , "([1, 2, 3] antenna to eci) to antenna"
                 , "[0, 0, 0] antenna to site"
                 , "[1, 2, 3] antenna .- [0, 0, 0] site on site"
                 , "([1, 2, 3] antenna to eci) == [6378003, 2, 4] eci"
                 , ":type antenna"
                 , ":view antenna"
                 , ":view site"
                 , ":ls --charts antenna"
                 , ":edit antenna"
                 , -- a temperature scale is untouched
                   "20 degC to degF"
                 , "77 °F .- 68 °F"
                 ]
          )
          @?= Right
            [ "[6378003, 2, 4] eci"
            , "[1, 2, 3] antenna"
            , "[2, 0, 1] site"
            , "[3, 2, 4] m"
            , "true"
            , "Chart antenna"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart site on eci at [6378, 0, 0] km"
            , "chart antenna : Chart antenna"
            , "chart antenna on site at [2, 0, 1] m"
            , "68 degF"
            , "9 deltaF"
            ]
        -- Two roots on one space have one set of axes and convert (design
        -- §3.10, F2); their points never mix unconverted.
        runLinesP
          ( tree
              ++ ["chart pad on GCRS at [6378000, 10, 0] m", "[1, 2, 3] antenna to pad"]
          )
          @?= Right ["[3, -8, 4] pad"]
        expectError
          ( runLinesP
              (tree ++ ["chart pad on GCRS", "[1, 2, 3] antenna .- [0, 0, 0] pad"])
          )
          "points on antenna and pad: convert one with `to`"
        -- :edit reads back to the same hash.
        let hashAfter def = runLinesP (take 3 tree ++ [def, ":hash antenna"])
        expecting (runLinesP (tree ++ [":edit antenna"])) $ \outs ->
          hashAfter (last outs) @?= hashAfter (tree !! 3)
        -- An origin that is a name, or an expression, runs to the next clause.
        runLinesP
          ( tree
              ++ [ -- a named value has a frame only when given one (design §3.9)
                   "let r0 = withAxes eci ([1, 0, 0] km)"
                 , "chart c1 on eci at r0"
                 , "chart c2 on site at r0 + r0"
                 , "[0, 0, 0] c1 to eci"
                 , "[0, 0, 0] c2 to eci"
                 , ":view c1"
                 , ":view c2"
                 ]
          )
          @?= Right
            [ "[1000, 0, 0] eci"
            , "[6380000, 0, 0] eci"
            , "chart c1 on eci at r0"
            , "chart c2 on site at r0 + r0"
            ]
        -- The parent's dimension is the child's.
        expectError
          (runLinesP (tree ++ ["chart t on site at 3 K", "t"]))
          "expected Vec GCRS m, got Num K"
        runLinesP ["chart warm on ITS90 at 300 K", "0 warm to degC"]
          @?= Right ["26.85 degC"]
    , testCase
        "a chart turned by a generator: by and then parse, and read back as written"
        $ do
          let eci = multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
              turn = "[0, -1, 0; 1, 0, 0; 0, 0, 0]"
          runLinesP
            [ eci
            , "chart lvlh on eci by " <> turn
            , ":view lvlh"
            , ":type lvlh"
            ]
            @?= Right ["chart lvlh on eci by " <> turn, "Chart lvlh"]
          -- `by` runs to the next clause, so the generator is a whole expression.
          runLinesP
            [ eci
            , "chart lvlh on eci by " <> turn <> " * pi / 6"
            , ":view lvlh"
            ]
            @?= Right ["chart lvlh on eci by " <> turn <> " * pi / 6"]
          -- Several generators, applied in order, separated by `then`; an `if`
          -- inside one keeps its own `then`.
          runLinesP
            [ eci
            , "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
            , ":view pf"
            , "chart odd on eci by (if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
            , ":view odd"
            ]
            @?= Right
              [ "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
              , "chart odd on eci by (if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
              ]
          let hashOfChart c = runLinesP [eci, "chart odd on eci by " <> c, ":hash odd"]
          hashOfChart "if 1 < 2 then rotz (1 deg) else rotx (1 deg) then rotx (2 deg)"
            @?= hashOfChart "(if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
          -- Clauses come in any order and read back in one.
          hashOfChart "rotz (1 deg)"
            @?= runLinesP [eci, "chart odd on eci by rotz (1 deg)", ":hash odd"]
          runLinesP [eci, "chart o2 on eci step km at [1, 0, 0] m", ":view o2"]
            @?= Right ["chart o2 on eci at [1, 0, 0] m step km"]
          -- A coordinate of a point on a turned chart is along the chart's own
          -- axes (design §3.10, F5).
          let lvlh = "chart lvlh on eci by " <> turn
          runLinesP
            [ eci
            , lvlh
            , "([1, 2, 3] lvlh).0"
            , "([1, 2, 3] lvlh .- [0, 0, 0] lvlh) == [1, 2, 3] m"
            ]
            @?= Right ["1 m", "true"]
          expectError
            ( runLinesP
                [eci, "chart bad on eci by [0, 1, 0; 1, 0, 0; 0, 0, 0]", "bad"]
            )
            "the generator of a chart must be antisymmetric: a bivector, such as rotz θ or a ∧ b"
          -- A root may be turned too: its axes are its own.
          runLinesP
            [ eci
            , "chart free on GCRS by " <> turn
            , ":type [1, 2, 3] free .- [0, 0, 0] free"
            ]
            @?= Right ["Vec free m"]
          -- `by` stays a name everywhere else, and inside brackets here.
          runLinesP
            [ eci
            , "let by = 5"
            , "by + 1"
            , "chart c on eci at [by, 0, 0] m"
            , "[0, 0, 0] c to eci"
            ]
            @?= Right ["6", "[5, 0, 0] eci"]
          expectError
            (runLinesP [eci, "chart c on eci at [1, 0, 0] m at [2, 0, 0] m"])
            "a chart has one `at` clause"
    , testCase
        "charts in a namespace block resolve their parent; the parent survives :export"
        $ do
          let block =
                multiline
                  [ "namespace frames"
                  , "  space GCRS = Vec 3 m"
                  , "  chart eci on GCRS"
                  , "  chart site on eci at [6378, 0, 0] km"
                  , "  chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
                  ]
          runLinesP [block, "[1, 2, 3] frames.site to frames.eci", ":view frames.lvlh"]
            @?= Right
              [ "[6378001, 2, 3] frames.eci"
              , "chart frames.lvlh on frames.site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
              ]
          original <- either (assertFailure . T.unpack) pure (sessionP [block, ":add"])
          source <-
            either (assertFailure . T.unpack) pure (exportSource original (Just "frames"))
          reloaded <-
            either (assertFailure . T.unpack) pure (sessionP [source, ":add"])
          reloaded.codebase.names @?= original.codebase.names
          reloaded.codebase.charts @?= original.codebase.charts
          reloaded.codebase.typeNames @?= original.codebase.typeNames
    , testCase "display units of one dimension cancel against each other" $ do
        evalP "2 m * 90 deg / rad" @?= Right ["3.1415926535897932384… m"]
        evalP "3 h / min" @?= Right ["180"]
        evalP "1 km / m" @?= Right ["1000"]
        evalP "(2 km)^2 / 1 m" @?= Right ["4000 km"]
        evalP "5 km / h" @?= Right ["5 km h^-1"]
        evalP "(3 rad/s) * 2 s" @?= Right ["6 rad"]
    , testCase
        "angle is a dimension: the circular functions take it, their inverses give it"
        $ do
          evalP "sin (45 deg)" @?= Right ["0.70710678118654752440…"]
          evalP "atan2 1 1 to deg" @?= Right ["45.000000000000000000… deg"]
          evalP "asin 1 to deg" @?= Right ["90 deg"]
          evalP "5 mrad to deg" @?= Right ["0.28647889756541160438… deg"]
          evalP "1 sr" @?= Right ["1 sr"]
          case evalP "sin 1" of
            Left err -> T.isInfixOf "write 1 rad or 45 deg" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalP "1 rad / s + 1 Hz" of
            Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "angles: deg is a unit built on pi" $ do
        evalP "90 deg" @?= Right ["90 deg"]
        evalP "90 deg to rad" @?= Right ["1.5707963267948966192… rad"]
        evalP "sin (90 deg)" @?= Right ["1.0000000000000000000…"]
        evalP "1 arcsec to deg" @?= Right ["0.00027777777777777777777… deg"]
    , testCase "identical definitions are different measurements; a - a still cancels" $ do
        runLines
          ["let a = 5 ± 0.1", "let b = 5 ± 0.1", "a - b", "a - a", "a - 2 * a + a"]
          @?= Right ["0.0 ± 0.2", "0", "0"]
        case runLines ["let a = 5 ± 0.1", "let b = 5 ± 0.1", ":hash a", ":hash b"] of
          Right [ha, hb] -> ha /= hb @? "a and b share a hash"
          other -> assertFailure (show other)
    , testCase
        "the owner stamp is implied: :view prints no label and the text round-trips"
        $ runLines ["let a = 5 ± 0.1", ":view a"] @?= Right ["a = 5 ± 0.1"]
    , testCase "a function-level tolerance is one unknown per input"
        $ runLines ["let f x = x ± 0.01", "f 2 - f 2", "f 2 - f 3"]
          @?= Right ["0", "-1.00 ± 0.02"]
    , testCase "a #label names the unknown: shared across definitions and values" $ do
        runLines ["let a = 5 ± 0.1 #s7", "let b = 5 ± 0.1 #s7", "a - b"] @?= Right ["0"]
        runLines ["let a = 5.0 ± 0.1 #s7", "let b = 5.2 ± 0.1 #s7", "a - b", "a + b"]
          @?= Right ["-0.2", "10.2 ± 0.2"]
        evalText "(5 ± 0.1 #s7) - (5 ± 0.1 #s7)" @?= Right ["0"]
        evalText "(5 ± 0.1 #s7) - (5 ± 0.1 #s8)" @?= Right ["0.0 ± 0.2"]
        evalText "(noise 2 #n) - (noise 2 #n)" @?= Right ["[0, 0]"]
    , testCase "labels print, parse and hash" $ do
        parseShape "5 ± 0.1 #s7"
          @?= Right (Lb "s7" (O (S.PlusMinus Bound) (N 5) (N (1 / 10))))
        parseShape "x == 5 ± 0.1 #s7"
          @?= Right (O S.Eq (V "x") (Lb "s7" (O (S.PlusMinus Bound) (N 5) (N (1 / 10)))))
        runLines ["let a = 5 ± 0.1 #s7", ":view a"] @?= Right ["a = 5 ± 0.1 #s7"]
        case runLines ["let a = 5 ± 0.1 #s7", "let b = 5 ± 0.1", ":hash a", ":hash b"] of
          Right [ha, hb] -> ha /= hb @? "tag and owner share a hash"
          other -> assertFailure (show other)
        case evalText "5 #s7" of
          Left err -> T.isInfixOf "labels nothing here" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase ":budget names tagged and owned nudges"
        $ runLines ["let span = (10 ± 0.01 #left) + (10 ± 0.01 #right)", ":budget span"]
          @?= Right
            [ "20.00 ± 0.02"
            , "  kind   source  contribution  share"
            , "  bound  left    0.01          50% of bound"
            , "  bound  right   0.01          50% of bound"
            ]
    , testCase "sqrt of a dimension that is not a square is a type error, not a loop"
        $ case evalP "sqrt (1 kg)" of
          Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testProperty "a product of enclosures encloses every product of their points"
        $ \(Small a) (Small b) (Small c) (Small d) (Small f) e1 e2 ->
          let x =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact (fromIntegral (a :: Int)))
                  (Exact (fromIntegral (c :: Int) / 7))
              y0 =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact (fromIntegral (b :: Int)))
                  (Exact (fromIntegral (d :: Int) / 7))
              y =
                uncertain
                  Bound
                  (Declared (Hash "y") [] 0)
                  y0
                  (Exact (fromIntegral (f :: Int) / 11))
              -- x and y share the nudge at site x (same midpoint-free id
              -- only when a == b; either way the check must hold).
              at = pointOf [(Hash "x", e1), (Hash "y", e2)]
              z = mulM 24 x y
           in within caseLimit (abs (at x * at y - midpoint z) <= radius z)
    , testProperty "the integer square root under sqrt is the floor of the root"
        $ \(Positive a) (NonNegative k) ->
          -- a long integer, as an uncertain value's endpoints become
          let n = (a :: Integer) * 7 ^ (k `mod` 400 :: Int)
              s = isqrt n
           in within caseLimit (s * s <= n && n < (s + 1) * (s + 1))
    , -- A generated case that once took ten seconds: the integer square
      -- root started Newton's method from n itself, one step per halving
      -- of a numerator thousands of bits long.
      localOption (mkTimeout 3_000_000)
        . testCase "sqrt of a long rational is fast"
        $ case evalText "sqrt ((7 / cos (-4 rad))^2)" of
          Right [v] -> T.isPrefixOf "10.70919959526478302" v @? T.unpack v
          other -> assertFailure (show other)
    , -- Newton's method for Kepler's equation took ten times longer with
      -- every step (four steps took 110 s): nothing shortened the
      -- coefficients and remainders a non-linear operation produced, and a
      -- value fed back into several places multiplied their length.
      localOption (mkTimeout 5_000_000)
        . testCase "Newton's method for Kepler's equation iterates quickly"
        $ runLinesP [keplerIter, keplerAt 12]
          @?= Right ["220.51207476752206740… deg"]
    , localOption (mkTimeout 20_000_000)
        . testCase "an iteration's cost grows linearly with its steps"
        $ do
          let timed k = do
                start <- getPOSIXTime
                out <- evaluate (runLinesP [keplerIter, keplerAt k])
                _ <- evaluate (either T.length (sum . map T.length) out)
                end <- getPOSIXTime
                out @?= Right ["220.51207476752206740… deg"]
                pure (end - start)
          t10 <- timed 10
          t20 <- timed 20
          -- linear is 2; the suite runs tests in parallel, so allow noise
          t20 < 5 * t10 @? "10 steps took " <> show t10 <> ", 20 took " <> show t20
    , localOption (mkTimeout 10_000_000)
        . testCase "an iteration's rationals stay short"
        $ do
          let p = 24
              meanAnomaly =
                uncertain
                  Stat
                  (Tagged "m" 0)
                  (mulM p (Exact (1177 / 5)) (scaleM p (1 / 180) (piM p)))
                  (Exact (1 / 1000))
              step ea = do
                let e = Exact (2 / 5)
                    residual = subM p (subM p ea (mulM p e (sinM p ea))) meanAnomaly
                    den = subM p (Exact 1) (mulM p e (cosM p ea))
                subM p ea <$> divM p residual den
              steps k = foldM (\ea _ -> step ea) meanAnomaly [1 .. k :: Int]
          case (longestRational <$> steps 10, longestRational <$> steps 40) of
            (Right l10, Right l40) ->
              l40 <= 2 * l10 @? "10 steps: " <> show l10 <> " digits; 40: " <> show l40
            other -> assertFailure (show other)
    , testProperty "sqrt, recip, exp and log enclose their true values"
        $ \(Positive n) (Positive d) e1 (Small k) ->
          let r = fromIntegral (n :: Int) / fromIntegral (d :: Int) :: Rational
              x =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact r)
                  (Exact (r / fromIntegral (2 + abs (k :: Int))))
              v = pointOf [(Hash "x", e1)] x
              lo z = midpoint z - radius z
              hi z = midpoint z + radius z
              inside z t = lo z <= t && t <= hi z
              squares z = lo z * lo z <= v && v <= hi z * hi z
              approx t = toRational (t :: Double)
           in within caseLimit . counterexample (show (r, v))
                $ either (const False) squares (sqrtM 24 x)
                  && either (const False) (`inside` recip v) (recipM 24 x)
                  && near (expM 24 x) (approx (exp (fromRational v)))
                  && either (const False) (`near` approx (log (fromRational v))) (logM 24 x)
    ]
 where
  -- A point in the enclosure: every nudge at a chosen value in [-1, 1].
  pointOf :: [(Hash, Double)] -> Magnitude -> Rational
  pointOf es = \case
    Exact r -> r
    m@(Affine mid _ _ _) -> mid + sum [c * eOf n | (c, n) <- nudges m]
   where
    eOf n = case n.origin of
      Tagged _ _ -> 0
      Declared site _ _ -> maybe 0 (toRational . max (-1) . min 1) (lookup site es)
      A.Builtin _ -> 0
  -- Double arithmetic is only good to about 1e-15 relative.
  near z t = abs (t - midpoint z) <= radius z + abs t * 1e-12 + 1e-300

dozenHash :: Text
dozenHash = hashShownAs ["unit dozen = 12"] "dozen"

kmHash :: Text
kmHash = hashShownAs [] "km"
