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
import Data.Map.Strict qualified as Map (size)
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Num (integerLog2)
import Metron.Affine (
  Magnitude (..),
  Origin (..),
  addM,
  divM,
  midpoint,
  mulM,
  powM,
  radius,
  scaleM,
  subM,
  uncertain,
 )
import Metron.Core (NudgeKind (..))
import Metron.Driver (Session, feed, seededSession)
import Metron.Encode (sint, varint)
import Metron.Numerical.Approx qualified as New
import Support.ExactApprox qualified as Old
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
