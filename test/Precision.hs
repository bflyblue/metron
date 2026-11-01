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
import Data.Ratio ((%))
import Metron.Encode (sint, varint)
import Metron.Numerical.Approx qualified as New
import Support.ExactApprox qualified as Old
import Test.Tasty
import Test.Tasty.QuickCheck

precisionTests :: TestTree
precisionTests =
  testGroup
    "working precision (design §3.2.8)"
    [ oracleTests
    ]

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
