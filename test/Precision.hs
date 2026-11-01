{- | Working precision (design §3.2.8, "exact while small, as built"):
every built-in's result is at working precision, every rounding goes
into its bound, and its series run in fixed point rather than in long
exact rationals.

The elementary functions are checked against the exact-rational series
they replaced ("Support.ExactApprox"), slow but rigorous: two enclosures
of one number must overlap.
-}
module Precision (precisionTests) where

import Data.Bits qualified as Bits (shiftR, (.&.))
import Data.ByteString qualified as BS (empty, length, pack)
import Data.ByteString.Builder (Builder, byteString, toLazyByteString, word8)
import Data.Either (fromRight)
import Data.Map.Strict qualified as Map (size)
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Read qualified as TR (decimal, signed)
import GHC.Num (integerLog2)
import Metron.Affine (
  Decide (..),
  Magnitude (..),
  Origin (..),
  absM,
  acosM,
  addM,
  asinM,
  atan2M,
  atanM,
  cosM,
  coshM,
  divM,
  expM,
  logM,
  midpoint,
  mulM,
  piM,
  powM,
  radius,
  recipM,
  scaleM,
  sinM,
  sinhM,
  sqrtM,
  subM,
  tanM,
  tanhM,
  uncertain,
 )
import Metron.Core (NudgeKind (..))
import Metron.Driver (Session, feed, seededSession)
import Metron.Encode (sint, varint)
import Metron.Numerical.Approx qualified as New
import Metron.Numerical.Linear (choleskyRows, determinant, invert, matrixExp)
import Support.ExactApprox qualified as Old
import Support.References (reference)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

precisionTests :: TestTree
precisionTests =
  testGroup
    "working precision (design §3.2.8)"
    [ oracleTests
    , exactWhileSmallTests
    , logisticTests
    , builtinTests
    , sizeTests
    , curvatureTests
    ]

-- Running sessions -------------------------------------------------------------------

seeded :: Session
seeded = either (error . T.unpack) id seededSession

-- | Lines fed in turn to a seeded session; the outputs, or the first error.
run :: [Text] -> Either Text [Text]
run = go seeded []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

-- Sizes ------------------------------------------------------------------------------

-- | Working precision at the default setting, 20 digits and four guard digits.
p24 :: Int
p24 = 24

{- | A rational's length beyond its size, in decimal digits: the shorter of
its numerator and denominator.
-}
digitsOf :: Rational -> Int
digitsOf r = min (len (abs (numerator r))) (len (denominator r))
 where
  len n = if n == 0 then 0 else (fromIntegral (integerLog2 n) * 1000) `div` 3322 + 1

-- | The longest rational in a magnitude: its midpoint, coefficients and slack.
longest :: Magnitude -> Int
longest = \case
  Exact r -> digitsOf r
  Affine m ts s _ -> maximum (digitsOf m : digitsOf s : [digitsOf c | (c, _) <- foldr (:) [] ts])

-- | The number of nudges a magnitude carries.
nudgeCount :: Magnitude -> Int
nudgeCount = \case
  Exact _ -> 0
  Affine _ ts _ _ -> Map.size ts

-- | A magnitude of bound nudges only encloses a value.
encloses :: Magnitude -> Rational -> Bool
encloses x v = abs (midpoint x - v) <= radius x

-- Exact while small ----------------------------------------------------------------------

exactWhileSmallTests :: TestTree
exactWhileSmallTests =
  testGroup
    "exact while small"
    [ testCase "1/3 + 1/6 is exactly 1/2, and so prints" $ do
        addM p24 (Exact (1 / 3)) (Exact (1 / 6)) @?= Exact (1 / 2)
        run ["1/3 + 1/6"] @?= Right ["0.5"]
    , testProperty "a short exact result stays exact"
        $ forAll shortRational
        $ \a -> forAll shortRational $ \b ->
          conjoin
            [ addM p24 (Exact a) (Exact b) === Exact (a + b)
            , subM p24 (Exact a) (Exact b) === Exact (a - b)
            , mulM p24 (Exact a) (Exact b) === Exact (a * b)
            , if b == 0
                then property True
                else divM p24 (Exact a) (Exact b) === Right (Exact (a / b))
            , powM p24 (Exact a) 3 === Right (Exact (a ^ (3 :: Int)))
            ]
    , testProperty "a long exact result is rounded into a bound that encloses it"
        $ forAll longRational
        $ \a -> forAll longRational $ \b ->
          let check exact x =
                counterexample (show x)
                  $ not (isExactM x)
                    .&&. encloses x exact
                    .&&. longest x <= p24 + 5
                    .&&. radius x <= abs exact * 10 ^^ negate (p24 + 2)
           in conjoin
                [ check (a + b) (addM p24 (Exact a) (Exact b))
                , check (a * b) (mulM p24 (Exact a) (Exact b))
                , either (const (property False)) (check (a / b)) (divM p24 (Exact a) (Exact b))
                ]
    , testCase "an exact power that grows long runs at working precision"
        $ case powM p24 (Exact (2 / 3)) 1000 of
          Right x -> do
            encloses x ((2 / 3) ^ (1000 :: Int)) @? show x
            longest x <= p24 + 5 @? show (longest x)
          Left err -> assertFailure (show err)
    , testCase "a sum's operands in either order round to one unknown" $ do
        let a = 1 / 7 ^ (300 :: Int)
            b = 1 / 3
        addM p24 (Exact a) (Exact b) @?= addM p24 (Exact b) (Exact a)
        subM p24 (addM p24 (Exact a) (Exact b)) (addM p24 (Exact b) (Exact a))
          @?= Exact 0
        run ["let big = 1/7^300", "big + 1/3 == 1/3 + big"] @?= Right ["true"]
    , testCase "linear operations on a form never round: x - x and (x + c) - x" $ do
        let x = uncertain Bound (Tagged "x" 0) (Exact (17 / 7)) (Exact (1 / 100))
            c = Exact (1 / 7 ^ (300 :: Int))
        subM p24 x x @?= Exact 0
        subM p24 (addM p24 x c) x @?= c
        run ["let x = 5 ± 0.1", "x - x", "(x + 1/3) - x"]
          @?= Right ["0", "0.33333333333333333333…"]
    , testCase "a long value cancels with itself, and its rounding is a bound"
        $ run ["let a = (1/3)^500 + 1", "a - a", "bound (a - 1) > 0"]
          @?= Right ["0", "true"]
    ]

-- | A rational of a few digits.
shortRational :: Gen Rational
shortRational = do
  n <- choose (negate (10 ^ (12 :: Int)), 10 ^ (12 :: Int))
  d <- choose (1, 10 ^ (12 :: Int))
  pure (n % d)

-- | A rational longer than the limit at the default precision, 224 digits.
longRational :: Gen Rational
longRational = do
  n <- choose (10 ^ (230 :: Int), 10 ^ (260 :: Int))
  d <- choose (10 ^ (230 :: Int), 10 ^ (260 :: Int))
  s <- elements [1, -1]
  pure (s * n % d)

-- The logistic map -----------------------------------------------------------------------

{- | @x ↦ 3.7 x (1 − x)@ from @1/3@, the exact iteration that doubles its
digits every step (design §8.1, "what the limits do not stop"): exact
for its first steps, then at working precision.
-}
logisticTests :: TestTree
logisticTests =
  testGroup
    "the exact logistic map runs at working precision"
    [ testCase "its enclosure holds the exact value for eighteen steps"
        $ mapM_
          ( \(k, x, exact) ->
              encloses x exact @? ("step " <> show k <> ": " <> show x)
          )
          ( take
              19
              (zip3 [0 :: Int ..] (iterate step (Exact (1 / 3))) (iterate exactStep (1 / 3)))
          )
    , testCase "its rationals stay short and its nudges few for a hundred steps" $ do
        let xs = take 101 (iterate step (Exact (1 / 3)))
            exactSteps = length (takeWhile isExactM xs)
        -- exact while within the limit, eight times the working precision
        maximum (map longest xs) <= 8 * (p24 + 4) @? show (map longest xs)
        exactSteps <= 9 @? show exactSteps
        -- then at working precision
        maximum (map longest (drop exactSteps xs)) <= 2 * (p24 + 4)
          @? show (map longest xs)
        maximum (map nudgeCount xs) <= 64 @? show (map nudgeCount xs)
    , localOption (mkTimeout 5_000_000)
        $ testCase "a hundred steps in the language finish in a moment"
        $ case run
          [ "let iter x k = if k == 0 then x else iter (x * (1 - x) * 37/10) (k - 1)"
          , "iter (1/3) 100"
          ] of
          Right [out] -> T.isPrefixOf "0.81" out @? T.unpack out
          other -> assertFailure (show other)
    ]
 where
  step x = scaleM p24 (37 / 10) (mulM p24 x (subM p24 (Exact 1) x))
  exactStep x = 37 / 10 * x * (1 - x) :: Rational

isExactM :: Magnitude -> Bool
isExactM = \case
  Exact _ -> True
  _ -> False

-- The series against the exact ones ----------------------------------------------------

type Approx = (Rational, Rational)

oracleTests :: TestTree
oracleTests =
  testGroup
    "fixed-point series agree with the exact-rational ones within both bounds"
    [ testProperty "decimalExponent"
        $ forAll anyNonZero
        $ \x ->
          New.decimalExponent x === Old.decimalExponent x
    , agree "sqrt" positive New.sqrtApprox Old.sqrtApprox relative
    , agree "exp" (bounded 60) New.expApprox Old.expApprox relative
    , agree "log" positive New.logApprox Old.logApprox relative
    , agree "atan" anyRational New.atanApprox Old.atanApprox relative
    , agree
        "sin"
        (bounded 1000000)
        (\p -> fst . New.sinCosApprox p)
        (\p -> fst . Old.sinCosApprox p)
        absolute
    , agree
        "cos"
        (bounded 1000000)
        (\p -> snd . New.sinCosApprox p)
        (\p -> snd . Old.sinCosApprox p)
        absolute
    , agree
        "sin, small"
        (bounded 1)
        (\p -> fst . New.sinCosApprox p)
        (\p -> fst . Old.sinCosApprox p)
        relative
    , agree "sinh" (bounded 8) New.sinhApprox Old.sinhApprox relative
    , agree "cosh" (bounded 8) New.coshApprox Old.coshApprox relative
    , agree
        "tan"
        (bounded 1000)
        New.tanApprox
        (quotient (\p -> fst . Old.sinCosApprox p) (\p -> snd . Old.sinCosApprox p))
        relative
    , agree
        "tanh"
        (bounded 60)
        New.tanhApprox
        (quotient Old.sinhApprox Old.coshApprox)
        relative
    , agree
        "tan′"
        (bounded 1000)
        New.sec2Approx
        ( \p x ->
            let (t, e) =
                  quotient
                    (\q -> fst . Old.sinCosApprox q)
                    (\q -> snd . Old.sinCosApprox q)
                    (p + 4)
                    x
             in (1 + t * t, (2 * abs t + e) * e)
        )
        relative
    , agree
        "tanh′"
        (bounded 15)
        New.sech2Approx
        ( \p x ->
            let (c, e) = Old.coshApprox (p + 8) x
             in (1 / (c * c), 3 * e / ((c - e) ^ (3 :: Int)))
        )
        relative
    , testProperty "π"
        $ forAll (choose (5, 300))
        $ \p ->
          overlap (New.piApprox p) (Old.piApprox (p + 4))
            .&&. tight relative p (New.piApprox p)
    , testProperty "sqrt is from below"
        $ forAll positive
        $ \x -> forAll (choose (5, 60)) $ \p ->
          let (s, _) = New.sqrtApprox p x in s * s <= x
    , testProperty "a long integer encodes as it did, byte for byte"
        $ forAll (choose (0, 3000 :: Int))
        $ \bits -> forAll (choose (0, 2 ^ bits)) $ \m ->
          forAll (elements [1, -1]) $ \s ->
            let n = s * m
             in toLazyByteString (sint n) === toLazyByteString (byteBySint n)
    ]

{- | The signed encoding as it was, shifting by one byte at a time: the
hashes of every stored term depend on it, so the faster one must agree.
-}
byteBySint :: Integer -> Builder
byteBySint n =
  let mag = magnitude (abs n)
   in word8 (if n < 0 then 1 else 0)
        <> varint (fromIntegral (BS.length mag))
        <> byteString mag
 where
  magnitude 0 = BS.empty
  magnitude m = BS.pack (reverse (go m))
  go 0 = []
  go m = fromIntegral (m Bits..&. 0xFF) : go (m `Bits.shiftR` 8)

{- | The two approximations of one function at one point overlap, and the
new one's error is within the precision: relative to the value, or
absolute for one that may be near zero where its argument is not.
-}
agree ::
  String ->
  Gen Rational ->
  (Int -> Rational -> Approx) ->
  (Int -> Rational -> Approx) ->
  (Rational -> Rational) ->
  TestTree
agree name gen new old sizeOf =
  testProperty name
    $ forAll gen
    $ \x ->
      forAll (choose (5, 50)) $ \p ->
        let a = new p x
            b = old p x
         in counterexample (show (x, p, a, b))
              $ overlap a b .&&. tight sizeOf p a

overlap :: Approx -> Approx -> Property
overlap (a, ea) (b, eb) =
  counterexample "the enclosures do not overlap" (abs (a - b) <= ea + eb)

-- | The error is within @10^-(p-2)@ of the value's scale.
tight :: (Rational -> Rational) -> Int -> Approx -> Property
tight sizeOf p (a, ea) =
  counterexample
    ("the error is wider than the precision: " <> show (fromRational ea :: Double))
    (ea <= sizeOf a * 10 ^^ negate (p - 2))

relative, absolute :: Rational -> Rational
relative = abs
absolute = max 1 . abs

-- | One approximation over another, with the quotient's error.
quotient ::
  (Int -> Rational -> Approx) ->
  (Int -> Rational -> Approx) ->
  Int ->
  Rational ->
  Approx
quotient f g p x =
  let (a, ae) = f (p + 8) x
      (b, be) = g (p + 8) x
      q = a / b
   in (q, (ae + abs q * be) / (abs b - be))

-- Generators ---------------------------------------------------------------------------

-- | A rational of a few digits, times a power of ten.
anyRational :: Gen Rational
anyRational = do
  n <- choose (-100000, 100000)
  d <- choose (1, 100000)
  e <- choose (-30, 30 :: Int)
  pure (n % d * 10 ^^ e)

anyNonZero :: Gen Rational
anyNonZero = anyRational `suchThat` (/= 0)

positive :: Gen Rational
positive = abs <$> anyNonZero

-- | A rational of at most the given size, some of them tiny.
bounded :: Rational -> Gen Rational
bounded limit = (`suchThat` (/= 0)) $ do
  n <- choose (-100000, 100000)
  d <- choose (1, 100000)
  e <- choose (-20, 0 :: Int)
  let x = n % d * 10 ^^ e
  pure (if abs x > limit then limit * signum x else x)

-- Every built-in against a reference -------------------------------------------------

-- | What a printed component is compared with.
data Ref
  = -- | the reference numbered so in "Support.References"
    R Int
  | -- | its negation
    Neg Int
  | -- | it plus a number
    Plus Int Rational
  | -- | it times a factor
    Times Int Rational
  | -- | an exact value
    Is Rational

refValue :: Ref -> Rational
refValue = \case
  R i -> parseRef (reference i)
  Neg i -> negate (parseRef (reference i))
  Plus i k -> k + parseRef (reference i)
  Times i k -> k * parseRef (reference i)
  Is r -> r
 where
  parseRef t =
    maybe
      0
      (.value)
      ( printedNumber
          (T.replace "-." "-0." (if "." `T.isPrefixOf` t then "0" <> t else t))
      )

{- | Each built-in at precisions 20, 50 and 200, against bc's value to 260
digits (design §3.2.8, as built): every printed digit within one unit
of the last place, as many significant digits as the precision (so the
enclosure is narrower than the last digit, and the value is at working
precision), and an exact result printed in full only when it is exact.
Each case's three precisions together get ten seconds.
-}
builtinTests :: TestTree
builtinTests =
  testGroup
    "every built-in at precisions 20, 50 and 200 agrees with bc"
    [ localOption (mkTimeout 10_000_000)
        $ testCase name
        $ mapM_ (agreesAt expr refs) [20, 50, 200]
    | (name, expr, refs) <- builtinCases
    ]

builtinCases :: [(String, Text, [Ref])]
builtinCases =
  [ ("sqrt: s2 = sqrt(2)", "sqrt 2", [R 1])
  , ("sqrt of a fraction: sqrt(1/3)", "sqrt (1/3)", [R 2])
  ,
    ( "sqrt of a tiny number: sqrt(10) · 10^-50000"
    , "sqrt 1e-99999"
    , [Times 50 (10 ^^ (-50000 :: Int))]
    )
  , ("exp: e(1/3)", "exp (1/3)", [R 3])
  , ("exp of a large number: e(100)", "exp 100", [R 4])
  , ("exp of a tiny number: e(10^-30)", "exp 1e-30", [Plus 37 1])
  , ("log: l(1/3)", "log (1/3)", [R 5])
  , ("log of a small number: -999 l(10)", "log 1e-999", [R 6])
  , ("log of a very small number: -99999 l(10)", "log 1e-99999", [R 29])
  , ("sin: s(1/3)", "sin (1/3 * 1 rad)", [R 7])
  , ("cos: c(1/3)", "cos (1/3 * 1 rad)", [R 8])
  , ("tan: s(1/3)/c(1/3)", "tan (1/3 * 1 rad)", [R 9])
  , ("tan near a pole: s(1.5)/c(1.5)", "tan (1.5 rad)", [R 28])
  , ("sin of a large angle: s(1000)", "sin (1000 rad)", [R 10])
  , ("sin of a very large angle: s(10^10)", "sin (1e10 rad)", [R 38])
  , ("asin: a(x/sqrt(1-x^2)) at 1/3", "asin (1/3)", [R 11])
  , ("acos: pi/2 - asin(1/3)", "acos (1/3)", [R 12])
  , ("atan: a(1/3)", "atan (1/3)", [R 13])
  , ("atan of a large number: a(100)", "atan 100", [R 14])
  , ("atan of a tiny number: a(10^-30)", "atan 1e-30", [R 44])
  , ("atan2: a(7/3)", "atan2 (1/3) (1/7)", [R 15])
  , ("sinh: (e(x) - e(-x))/2 at 1/3", "sinh (1/3)", [R 16])
  , ("sinh of a tiny number, 10^-20", "sinh 1e-20", [R 43])
  , ("cosh: (e(x) + e(-x))/2 at 1/3", "cosh (1/3)", [R 17])
  , ("cosh of a large number, 50", "cosh 50", [R 42])
  , ("tanh: sinh/cosh at 1/3", "tanh (1/3)", [R 18])
  , ("tanh near one: sinh/cosh at 5", "tanh 5", [R 27])
  , ("pi: 4 a(1)", "pi", [R 19])
  , ("+, - and abs: 2 - s2", "abs (sqrt 2 - 2)", [R 23])
  , ("*: s2 s3", "sqrt 2 * sqrt 3", [R 21])
  , ("/: s2/s3", "sqrt 2 / sqrt 3", [R 22])
  , ("^: s2^7", "sqrt 2 ^ 7", [R 20])
  , ("^ of an exact fraction stays exact", "(1/3) ^ 50", [Is (1 / 3 ^ (50 :: Int))])
  , ("+ of exact fractions stays exact", "1/3 + 1/6", [Is (1 / 2)])
  , ("norm: sqrt(2 + 3 + 1/49)", "norm [sqrt 2, sqrt 3, 1/7]", [R 24])
  , ("dot: s2/7 + s3/3", "[sqrt 2, 1/3] · [1/7, sqrt 3]", [R 25])
  ,
    ( "outer"
    , "outer [sqrt 2, 1/3] [1/7, sqrt 3]"
    , [Times 1 (1 / 7), R 21, Is (1 / 21), R 2]
    )
  , ("cross", "[sqrt 2, 1/3, 1] × [1/7, sqrt 3, 2]", [R 39, R 40, R 41])
  , ("wedge", "[sqrt 2, 1/3] ∧ [1/7, sqrt 3]", [Is 0, R 41, Neg 41, Is 0])
  ,
    ( "inverse: the adjugate over the determinant"
    , "inverse [sqrt 2, 1/3; 1/7, sqrt 3]"
    , [R 30, R 31, R 32, R 33]
    )
  ,
    ( "det: by cofactors"
    , "det [sqrt 2, 1/3, 1; 1/7, sqrt 3, 2; 3, 1/11, sqrt 5]"
    , [R 26]
    )
  ,
    ( "cholesky: sqrt(s3 - 1/36)"
    , "cholesky [4, 1/3; 1/3, sqrt 3]"
    , [Is 2, Is 0, Is (1 / 6), R 34]
    )
  ,
    ( "expm of a rotation: c(1/3), s(1/3)"
    , "expm [0, -(1/3); 1/3, 0]"
    , [R 35, Neg 36, R 36, R 35]
    )
  ,
    ( "expm: the 2 × 2 closed form"
    , "expm [1/3, 1/7; 1/11, 1/5]"
    , [R 46, R 47, R 48, R 49]
    )
  ,
    ( "floor, ceil and round"
    , "[floor (sqrt 2 * 10), ceil (sqrt 2 * 10), round (sqrt 2 * 10)]"
    , [Is 14, Is 15, Is 14]
    )
  ,
    ( "mid, sd and bound"
    , "[mid (sqrt 2 ±σ 0.1), sd (sqrt 2 ±σ 0.1), bound (sqrt 2 ± 0.1)]"
    , [R 1, Is (1 / 10), Is (1 / 10)]
    )
  ,
    ( "covariance"
    , "covariance [sqrt 2 ±σ 0.1, 1/3 ±σ 0.2]"
    , [Is (1 / 100), Is 0, Is 0, Is (4 / 100)]
    )
  ]

-- | One case at one precision.
agreesAt :: Text -> [Ref] -> Int -> Assertion
agreesAt expr refs precision =
  case run [":set precision " <> T.pack (show precision), expr] of
    Right [out] -> do
      let printed = mapM printedNumber (components out)
          context = "at precision " <> show precision <> ": " <> T.unpack out
      case printed of
        Nothing -> assertFailure ("unreadable " <> context)
        Just ps -> do
          length ps == length refs @? ("components " <> context)
          not (T.isInfixOf "±" out || T.isInfixOf "non-linear" out)
            @? ("an enclosure " <> context)
          mapM_ (agrees context precision) (zip ps (map refValue refs))
    other -> assertFailure ("at precision " <> show precision <> ": " <> show other)

{- | A component cut short with "…" agrees with its reference to within one
unit in its @precision@-th significant digit (design §3.2.10; a large
number's integer part is printed whole, padded with zeros past those
digits), and has at least that many; one printed in full is exact and
must be the reference.
-}
agrees :: String -> Int -> (Printed, Rational) -> Assertion
agrees context precision (p, ref) = case p.lastPlace of
  Nothing -> p.value == ref @? ("not exactly the reference " <> context)
  Just _ -> do
    let unit = 10 ^^ (New.decimalExponent ref - precision + 1) :: Rational
    abs (p.value - ref) <= unit @? ("beyond the last digit " <> context)
    p.digits >= precision @? ("fewer digits than the precision " <> context)

-- | A printed number: its value, its significant digits, and the place of its last digit when it is cut short with "…".
data Printed = Printed {value :: Rational, digits :: Int, lastPlace :: Maybe Int}

-- | The numbers of a printed scalar, vector or matrix, without units.
components :: Text -> [Text]
components out =
  let body = T.filter (`notElem` ("[]" :: String)) out
   in map
        (T.takeWhile (/= ' ') . T.strip)
        (concatMap (T.splitOn ", ") (T.splitOn "; " body))

printedNumber :: Text -> Maybe Printed
printedNumber t =
  let (mantissa, rest) = T.breakOn "e" t
      cut = "…" `T.isSuffixOf` mantissa
      plain = T.dropWhileEnd (== '…') mantissa
      negative = "-" `T.isPrefixOf` plain
      unsigned = if negative then T.drop 1 plain else plain
      (whole, point) = T.breakOn "." unsigned
      fraction = T.drop 1 point
      sign = if negative then -1 else 1
   in do
        ex <- if T.null rest then Just 0 else integer (T.drop 1 rest)
        n <- integer (whole <> fraction)
        let places = T.length fraction
            significant = T.length (T.dropWhile (== '0') (whole <> fraction))
        Just
          Printed
            { value = sign * fromInteger n * 10 ^^ (ex - places)
            , digits = significant
            , lastPlace = if cut then Just (ex - places) else Nothing
            }
 where
  integer s = case TR.signed TR.decimal s of
    Right (v, "") -> Just v
    _ -> Nothing

-- Every built-in's rationals ------------------------------------------------------------

{- | Each built-in's result at working precisions 24, 54 and 204 (precision
20, 50 and 200), from an exact argument, an argument with a bound and one
with a σ: no rational in it longer than the precision allows, @p + 5@
digits, and from an exact argument an enclosure within the precision.
-}
sizeTests :: TestTree
sizeTests =
  testGroup
    "every built-in's rationals are within the working precision"
    ( [ testCase name
          $ sequence_ [check p (isExactM x) (f p x) | p <- [24, 54, 204], x <- arguments]
      | (name, f) <- unary
      ]
        ++ [ testCase name
               $ sequence_
                 [ check p (isExactM x && isExactM y) (f p x y)
                 | p <- [24, 54, 204]
                 , x <- arguments
                 , y <- arguments
                 ]
           | (name, f) <- binary
           ]
        ++ [ testCase name $ sequence_ [checkAll p (f p (matrix p)) | p <- [24, 54, 204]]
           | (name, f) <- matrices
           ]
    )
 where
  third = Exact (1 / 3)
  arguments =
    [ third
    , uncertain Bound (Tagged "b" 0) third (Exact (1 / 10 ^ (12 :: Int)))
    , uncertain Stat (Tagged "s" 0) third (Exact (1 / 10 ^ (6 :: Int)))
    ]
  unary :: [(String, Int -> Magnitude -> Either String Magnitude)]
  unary =
    [ ("sqrt", \p -> shown . sqrtM p)
    , ("exp", \p -> Right . expM p)
    , ("log", \p -> shown . logM p)
    , ("sin", \p -> Right . sinM p)
    , ("cos", \p -> Right . cosM p)
    , ("tan", \p -> shown . tanM p)
    , ("asin", \p -> shown . asinM p)
    , ("acos", \p -> shown . acosM p)
    , ("atan", \p -> Right . atanM p)
    , ("sinh", \p -> Right . sinhM p)
    , ("cosh", \p -> Right . coshM p)
    , ("tanh", \p -> Right . tanhM p)
    , ("abs", \p -> Right . absM p)
    , ("recip", \p -> shown . recipM p)
    , ("^ 7", \p x -> shown (powM p x 7))
    , ("^ -3", \p x -> shown (powM p x (-3)))
    , ("pi", \p _ -> Right (piM p))
    ]
  binary :: [(String, Int -> Magnitude -> Magnitude -> Either String Magnitude)]
  binary =
    [ ("+", \p x y -> Right (addM p x (sqrtOf p y)))
    , ("*", \p x y -> Right (mulM p x (sqrtOf p y)))
    , ("/", \p x y -> shown (divM p x (sqrtOf p y)))
    , ("atan2", \p x y -> shown (atan2M p x (sqrtOf p y)))
    ]
  matrices :: [(String, Int -> [[Magnitude]] -> Either String [[Magnitude]])]
  matrices =
    [ ("det", \p m -> (\d -> [[d]]) <$> shown (determinant p 3 m))
    , ("inverse", \p m -> shown (invert p 3 m))
    , -- two by two: at p = 204 the 3 × 3 series takes seconds (design §3.2.8, as built)
      ("expm", \p m -> shown (matrixExp p 2 (map (take 2) (take 2 m))))
    ,
      ( "cholesky"
      , \p m -> shown (choleskyRows "cholesky" (Decide 3 (1 / 100)) p (spd p m))
      )
    ]
  sqrtOf p y = fromRight y (sqrtM p (addM p y (Exact 2)))
  matrix p =
    [ [sqrtOf p (Exact 2), Exact (1 / 3), Exact 1]
    , [Exact (1 / 7), sqrtOf p (Exact 3), Exact 2]
    , [Exact 3, Exact (1 / 11), sqrtOf p (Exact 5)]
    ]
  -- m mᵀ, symmetric and positive definite
  spd p m =
    [ [foldr (addM p . uncurry (mulM p)) (Exact 0) (zip r c) | c <- m]
    | r <- m
    ]
  shown :: (Show e) => Either e a -> Either String a
  shown = either (Left . show) Right
  check p exactArguments = \case
    Left err -> assertFailure err
    Right x -> do
      longest x <= p + 5 @? ("p = " <> show p <> ": " <> show x)
      -- of exact arguments, an enclosure within the precision
      not exactArguments
        || radius x <= max 1 (abs (midpoint x)) * 10 ^^ negate (p - 2)
        @? ("wide, p = " <> show p <> ": " <> show x)
  checkAll p = \case
    Left err -> assertFailure err
    Right rows ->
      mapM_
        (\x -> longest x <= p + 5 @? ("p = " <> show p <> ": " <> show x))
        (concat rows)

-- The second-order estimate -------------------------------------------------------------

{- | A function's statistical part is marked non-linear when its second
order term, about @|f''| σ / |f'|@ of the first-order σ, passes 1%
(design §3.2). The cases below have that ratio known: well under 1% is
not marked, over it is, and the measure is within a few times the ratio.
-}
curvatureTests :: TestTree
curvatureTests =
  testGroup
    "the second-order estimate follows the true curvature"
    [ testCase "atan2 near 90°: the angle is nearly linear, 0.1%" $ do
        unmarked "atan2 ((1 ±σ 0.001) * 1 m) ((0.03 ±σ 0.001) * 1 m)"
        unmarked "atan2 ((1 ±σ 0.001) * 1 m) ((-0.03 ±σ 0.001) * 1 m)"
        unmarked "atan2 ((-1 ±σ 0.001) * 1 m) ((0.03 ±σ 0.001) * 1 m)"
        unmarked "atan2 ((0.03 ±σ 0.001) * 1 m) ((-1 ±σ 0.001) * 1 m)"
    , testCase "atan2 at 45° with σ a thirtieth of the radius: 2.4%, marked"
        $ markedWithin 30 "atan2 ((0.03 ±σ 0.001) * 1 m) ((0.03 ±σ 0.001) * 1 m)"
    , testCase "atan far from zero: 0.2%"
        $ unmarked "atan (75 ±σ 0.075)"
    , testCase "sin near zero and cos near its zero: 0.02% and 0.14%" $ do
        unmarked "sin ((0.01 ±σ 0.02) * 1 rad)"
        unmarked "cos ((1.5 ±σ 0.02) * 1 rad)"
    , testCase "tan near a pole: 2.8%, marked"
        $ markedWithin 6 "tan ((1.5 ±σ 0.001) * 1 rad)"
    , testCase "tan near zero: nearly a line"
        $ unmarked "tan ((0.01 ±σ 0.001) * 1 rad)"
    , testCase "tanh at 5: 20%, marked, where the quotient said 78000%"
        $ markedWithin 40 "tanh (5 ±σ 0.1)"
    , localOption (mkTimeout 5_000_000)
        $ testCase "tanh far out is ±1 to every digit, unmarked, at once"
        $ do
          run ["tanh 1e6"] @?= Right ["1.0000000000000000000…"]
          run ["tanh ((-1e6 ±σ 1))"] @?= Right ["-1.0000000000000000000…"]
          -- its σ and second-order term are both below the last digit
          unmarked "tanh ((40 ±σ 1))"
    , testCase "asin near one: 5%, marked"
        $ markedWithin 15 "asin (0.99 ±σ 0.001)"
    , testCase "tan refuses an enclosure that reaches a pole"
        $ case run ["tan ((1.5707963 ± 0.001) * 1 rad)"] of
          Left err -> T.isInfixOf "pole" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testCase "a σ that reaches a pole is unbounded"
        $ case run ["tan ((1.56 ±σ 0.02) * 1 rad)"] of
          Right [out] -> T.isInfixOf "second-order term unbounded" out @? T.unpack out
          other -> assertFailure (show other)
    , testCase "a near-polar orbit's elements from a ±σ state are first order"
        $ case run
          [ "use astro"
          , "use astro.kepler"
          , "let curtis = Body {mu = 398600 km^3/s^2, radius = 6378 km, flattening = 0, j2 = 0.00108263, rate = 0 rad/s}"
          , "let el = fromState curtis ([7000 ±σ 0.1, 100 ±σ 0.1, 50 ±σ 0.1] km) ([0.01 ±σ 0.0001, 0.1 ±σ 0.0001, 7.5 ±σ 0.0001] km/s)"
          , "el.i"
          , "el.e"
          ] of
          Right [i, e] -> do
            T.isPrefixOf "1.557484 ±σ 1.3e-5 rad" i @? T.unpack i
            not (T.isInfixOf "non-linear" i) @? T.unpack i
            T.isPrefixOf "0.014691 ±σ 2.7e-5" e @? T.unpack e
          other -> assertFailure (show other)
    ]
 where
  unmarked expr = case run [expr] of
    Right [out] -> not (T.isInfixOf "non-linear" out) @? T.unpack out
    other -> assertFailure (show other)
  -- marked, with a measure of at most the given percent
  markedWithin limit expr = case run [expr] of
    Right [out] -> case T.breakOn "second-order term " out of
      (_, rest)
        | Just pct <- percent (T.drop (T.length "second-order term ") rest) ->
            pct <= limit @? T.unpack out
      _ -> assertFailure ("not marked: " <> T.unpack out)
    other -> assertFailure (show other)
  percent t = (.value) <$> printedNumber (T.takeWhile (/= '%') t)
