{- | Deterministic input draws. Rounding repetitions do not enter an input
key, and distribution generation uses rational approximation kernels.
-}
module Metron.Numerical.Sampling (
  Distribution,
  normal,
  uniform,
  draw,
  inputWord,
  roundingWord,
) where

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bits (shiftR, xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Ratio ((%))
import Data.Word (Word64)
import Metron.Numerical.Approx (Precision)
import Metron.Numerical.Error (ArithError (..))
import Metron.Numerical.Rational qualified as R

data Distribution
  = Normal !Rational !Rational
  | Uniform !Rational !Rational
  deriving stock (Eq, Show)

normal :: Rational -> Rational -> Either ArithError Distribution
normal mean deviation
  | deviation < 0 = Left (Domain "normal needs a nonnegative standard deviation")
  | otherwise = Right (Normal mean deviation)

uniform :: Rational -> Rational -> Either ArithError Distribution
uniform lower upper
  | lower > upper = Left (Domain "uniform needs ordered endpoints")
  | otherwise = Right (Uniform lower upper)

{- | An input realization before its conversion into the selected arithmetic.
The same seed, declaration and global input index give the same draw.
-}
draw ::
  Precision ->
  Int ->
  ByteString ->
  Int ->
  Distribution ->
  Either ArithError Rational
draw p seed identity i distribution
  | p < 1 = Left (Domain "sampling precision must be positive")
  | i < 0 = Left (Domain "input sample index must be nonnegative")
  | otherwise = case distribution of
      Uniform lo hi -> Right (lo + (hi - lo) * u 0)
      Normal mean 0 -> Right mean
      Normal mean deviation -> do
        l <- R.logarithm (p + 8) (u 0)
        radius <- R.squareRoot (p + 8) (-(2 * l))
        let angle = 2 * R.piAt (p + 8) * u 1
        Right (mean + deviation * radius * R.cosine (p + 8) angle)
 where
  -- Midpoints of 2^64 cells: strictly inside (0,1), avoiding log 0.
  u component = (2 * toInteger (inputWord seed identity i component) + 1) % (2 ^ (65 :: Int))

-- | Independent seed domains distinguish physical draws from rounding coins.
inputWord :: Int -> ByteString -> Int -> Int -> Word64
inputWord seed identity i component =
  keyed 0x696e707574 seed identity [fromIntegral i, fromIntegral component]

{- | A rounding key includes the operation occurrence, its deterministic
invocation index, and both sample indices. Operands are not identities.
-}
roundingWord :: Int -> ByteString -> Int -> Int -> Int -> Word64
roundingWord seed occurrence invocation i j =
  keyed
    0x726f756e64
    seed
    occurrence
    [fromIntegral invocation, fromIntegral i, fromIntegral j]

keyed :: Word64 -> Int -> ByteString -> [Word64] -> Word64
keyed domain seed identity =
  foldl'
    (\state coordinate -> mix (state + mix coordinate))
    (mix (domain `xor` fromIntegral seed `xor` fingerprint identity))

fingerprint :: ByteString -> Word64
fingerprint =
  BS.foldl' (\acc byte -> acc * 256 + fromIntegral byte) 0
    . BS.take 8
    . SHA256.hash

-- SplitMix64's finalizer; all arithmetic intentionally wraps in Word64.
mix :: Word64 -> Word64
mix x =
  let a = (x `xor` (x `shiftR` 30)) * 0xbf58476d1ce4e5b9
      b = (a `xor` (a `shiftR` 27)) * 0x94d049bb133111eb
   in b `xor` (b `shiftR` 31)
