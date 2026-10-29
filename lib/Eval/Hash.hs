-- | The nominal form and content hashing (design §5.2, §6).
--
-- A term's nominal form is its canonical byte encoding: one tag byte per
-- constructor, hints dropped, variables as de Bruijn indices, rationals in
-- lowest terms. The hash is SHA-256 of that encoding.
module Eval.Hash
  ( encodeTerm
  , hashTerm
  , placeholderHash
  , showHash
  , hashHasPrefix
  ) where

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder
import Data.ByteString.Lazy qualified as BL
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Eval.Core

-- | The canonical encoding of a closed term.
encodeTerm :: Term Z -> ByteString
encodeTerm = BL.toStrict . toLazyByteString . enc False 0

hashTerm :: Term Z -> Hash
hashTerm = Hash . SHA256.hash . encodeTerm

-- | The ordering hash used to fix member order inside a cycle (design
-- §6.2): the body is encoded with every free variable, which can only be a
-- cycle variable, replaced by one placeholder.
placeholderHash :: Term n -> Hash
placeholderHash = Hash . SHA256.hash . BL.toStrict . toLazyByteString . enc True 0

-- | Encoding. The 'Bool' says whether free variables become placeholders;
-- the 'Int' is the number of binders entered so far.
enc :: Bool -> Int -> Term n -> Builder
enc ph depth = \case
  Var i
    | ph, finToInt i >= depth -> word8 0x10
    | otherwise -> word8 0x00 <> varint (fromIntegral (finToInt i))
  Ref (Hash h) idx -> word8 0x01 <> byteString h <> varint (maybe 0 (fromIntegral . (+ 1)) idx)
  PrimApp p args -> word8 0x02 <> text p <> foldMap (enc ph depth) args
  Lit (LTensor dims rs) ->
    word8 0x03
      <> varint (fromIntegral (length dims))
      <> foldMap (varint . fromIntegral) dims
      <> foldMap (\r -> sint (numerator r) <> varint (denominator r)) rs
  Lit (LBool b) -> word8 0x04 <> word8 (if b then 1 else 0)
  Lam _ b -> word8 0x05 <> enc ph (depth + 1) b
  App f a -> word8 0x06 <> enc ph depth f <> enc ph depth a
  Let _ e b -> word8 0x07 <> enc ph depth e <> enc ph (depth + 1) b
  If c t e -> word8 0x08 <> enc ph depth c <> enc ph depth t <> enc ph depth e
  Pow t n -> word8 0x09 <> enc ph depth t <> sint n
  Noise k n -> word8 0x0A <> kind k <> varint n
  Uncertain k x e -> word8 0x0B <> kind k <> enc ph depth x <> enc ph depth e
  Pack ts -> word8 0x0C <> varint (fromIntegral (length ts)) <> foldMap (enc ph depth) ts
  Cycle _ bodies ->
    let k = vecLength bodies
     in word8 0x0E <> varint (fromIntegral k) <> foldMap (enc ph (depth + k)) (vecToList bodies)
  Proj t i -> word8 0x0F <> enc ph depth t <> varint (fromIntegral i)
  where
    kind = \case
      Bound -> word8 0
      Stat -> word8 1
    text t = let bs = TE.encodeUtf8 t in varint (fromIntegral (BS.length bs)) <> byteString bs

-- | Unsigned LEB128.
varint :: Integer -> Builder
varint n
  | n < 0 = error "varint: negative"
  | n < 0x80 = word8 (fromIntegral n)
  | otherwise = word8 (fromIntegral (n .&. 0x7F) .|. 0x80) <> varint (n `shiftR` 7)

-- | Sign byte, then the magnitude as a length-prefixed big-endian byte string.
sint :: Integer -> Builder
sint n =
  let mag = magnitude (abs n)
   in word8 (if n < 0 then 1 else 0) <> varint (fromIntegral (BS.length mag)) <> byteString mag
  where
    magnitude 0 = BS.empty
    magnitude m = BS.pack (reverse (go m))
    go 0 = []
    go m = fromIntegral (m .&. 0xFF) : go (m `shiftR` 8)

-- | A short, human-facing form: @#@ followed by the first five base32hex
-- characters of the digest.
showHash :: Hash -> Text
showHash h = "#" <> T.take 5 (base32hex h)

-- | Whether a hash's base32hex form starts with the given text (with or
-- without the leading @#@).
hashHasPrefix :: Text -> Hash -> Bool
hashHasPrefix prefix h = T.dropWhile (== '#') prefix `T.isPrefixOf` base32hex h

-- | RFC 4648 base32hex without padding.
base32hex :: Hash -> Text
base32hex (Hash bs) = T.pack (go (BS.unpack bs))
  where
    alphabet = "0123456789abcdefghijklmnopqrstuv"
    go [] = []
    go bytes =
      let (chunk, rest) = splitAt 5 bytes
          n = length chunk
          bits = foldl (\acc b -> (acc `shiftL` 8) .|. fromIntegral b) (0 :: Integer) chunk `shiftL` (8 * (5 - n))
          chars = (n * 8 + 4) `div` 5
          digits = [alphabet !! fromIntegral ((bits `shiftR` (40 - 5 * (i + 1))) .&. 31) | i <- [0 .. chars - 1]]
       in digits ++ go rest
