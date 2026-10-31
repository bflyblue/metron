{- | The byte-level pieces of the canonical encoding (design §6.1) and the
encoding of declared types. A type's hash is fixed by its declaration
alone, so it sits below "Eval.Builtin", which holds the built-in types as
declarations and needs their hashes, and below "Eval.Hash", which encodes
terms and re-exports 'encodeTypeDef' and 'hashTypeDef'.
-}
module Eval.Encode (
  -- * Primitives
  text,
  varint,
  sint,

  -- * Declared types
  encodeTypeDef,
  hashTypeDef,
  encType,
) where

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bits (shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder
import Data.ByteString.Lazy qualified as BL
import Data.Text (Text)
import Data.Text.Encoding qualified as TE
import Eval.Core (Hash (..), Label (..))
import Eval.Dimension
import Eval.Type.Base

-- | Length-prefixed UTF-8.
text :: Text -> Builder
text t =
  let bs = TE.encodeUtf8 t
   in varint (fromIntegral (BS.length bs)) <> byteString bs

-- | Unsigned LEB128.
varint :: Integer -> Builder
varint n
  | n < 0 = error "varint: negative"
  | n < 0x80 = word8 (fromIntegral n)
  | otherwise =
      word8 (fromIntegral (n .&. 0x7F) .|. 0x80) <> varint (n `shiftR` 7)

-- | Sign byte, then the magnitude as a length-prefixed big-endian byte string.
sint :: Integer -> Builder
sint n =
  let mag = magnitude (abs n)
   in word8 (if n < 0 then 1 else 0)
        <> varint (fromIntegral (BS.length mag))
        <> byteString mag
 where
  magnitude 0 = BS.empty
  magnitude m = BS.pack (reverse (go m))
  go 0 = []
  go m = fromIntegral (m .&. 0xFF) : go (m `shiftR` 8)

{- | The canonical encoding of a declared type (design §6.1): parameter kinds,
constructors' field types, label. Names are not part of it.
-}
encodeTypeDef :: TypeDef -> ByteString
encodeTypeDef def =
  BL.toStrict . toLazyByteString
    $ varint (fromIntegral (length def.params))
      <> foldMap (kindByte . snd) def.params
      <> varint (fromIntegral (length def.constructors))
      <> foldMap
        (\fs -> varint (fromIntegral (length fs)) <> foldMap encType fs)
        def.constructors
      <> labelEnc def.label
 where
  labelEnc = \case
    Owner t -> word8 0 <> text t
    Tag t -> word8 1 <> text t
    -- A chart's minted axis type (design §3.9): appended.
    Axes t -> word8 2 <> text t

hashTypeDef :: TypeDef -> Hash
hashTypeDef = Hash . SHA256.hash . encodeTypeDef

kindByte :: Kind -> Builder
kindByte = \case
  KType -> word8 0
  KLen -> word8 1
  KShape -> word8 2
  KDim -> word8 3
  -- An axis variable (design §3.9): appended.
  KAxis -> word8 4

encType :: Type -> Builder
-- 0x20 (Bool), 0x24 (tuple) and 0x25 (list) are retired: those types are
-- 0x28 on the built-in hashes (design §6.1), and no longer read either.
encType = \case
  TTensor sh d -> word8 0x21 <> encShape sh <> encDim d
  TPoint sh d -> word8 0x22 <> encShape sh <> encDim d
  -- A chart's root slot (design §3.9): anonymous keeps the old bytes; any
  -- other slot is the appended tag 0x29.
  TScale sh AAnon d -> word8 0x23 <> encShape sh <> encDim d
  TScale sh r d -> word8 0x29 <> encShape sh <> encAxis r <> encDim d
  TFun a b -> word8 0x26 <> encType a <> encType b
  TVar v -> word8 0x27 <> varint (fromIntegral v)
  TData (Hash h) as ->
    word8 0x28
      <> byteString h
      <> varint (fromIntegral (length as))
      <> foldMap encArg as

encArg :: Arg -> Builder
encArg = \case
  AType t -> word8 0 <> encType t
  ALen l -> word8 1 <> encLen l
  AShape sh -> word8 2 <> encShape sh
  ADim d -> word8 3 <> encDim d
  AAxis a -> word8 4 <> encAxis a

{- | A position with anonymous axes keeps the bytes of a bare length (design
§3.9, §6.1); a named or variable slot is the appended tag 3.
-}
encShape :: Shape -> Builder
encShape = \case
  SNil -> word8 0
  SCons l AAnon rest -> word8 1 <> encLen l <> encShape rest
  SCons l a rest -> word8 3 <> encLen l <> encAxis a <> encShape rest
  SVar v -> word8 2 <> varint (fromIntegral v)

-- | The name slot of a position: anonymous, a name's hash, or a variable.
encAxis :: Axis -> Builder
encAxis = \case
  AAnon -> word8 0
  ANamed (Hash h) -> word8 1 <> byteString h
  AVar v -> word8 2 <> varint (fromIntegral v)

encLen :: Len -> Builder
encLen = \case
  LLit k -> word8 0 <> varint (fromIntegral k)
  LVar v k -> word8 1 <> varint (fromIntegral v) <> varint (fromIntegral k)
  -- rank s + k (design §4.1): appended, so older encodings are unchanged.
  LRank v k -> word8 2 <> varint (fromIntegral v) <> varint (fromIntegral k)

encDim :: Dim -> Builder
encDim d =
  let atoms = dimAtoms d
   in varint (fromIntegral (length atoms))
        <> foldMap
          ( \(a, k) -> case a of
              Base b -> word8 0 <> word8 (fromIntegral (fromEnum b)) <> sint (fromIntegral k)
              DVar v -> word8 1 <> varint (fromIntegral v) <> sint (fromIntegral k)
          )
          atoms
