{- | The byte-level pieces of the canonical encoding (design §6.1) and the
encoding of declared types. A type's hash is fixed by its declaration
alone, so it sits below "Metron.Builtin", which holds the built-in types as
declarations and needs their hashes, and below "Metron.Hash", which encodes
terms and re-exports 'encodeTypeDef' and 'hashTypeDef'.
-}
module Metron.Encode (
  -- * Primitives
  text,
  varint,
  sint,

  -- * Declared types
  encodeTypeDef,
  hashTypeDef,
) where

import Crypto.Hash.SHA256 qualified as SHA256 (hash)
import Data.Bits (bit, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (length)
import Data.ByteString.Builder (
  Builder,
  byteString,
  toLazyByteString,
  word8,
 )
import Data.ByteString.Lazy qualified as BL (toStrict)
import Data.Text (Text)
import Data.Text.Encoding qualified as TE (encodeUtf8)
import GHC.Num (integerLog2)
import Metron.Core (Hash (..), Label (..))
import Metron.Dimension (Dim, DimAtom (Base, DVar), dimAtoms)
import Metron.Type.Base (
  Arg (..),
  Axis (..),
  Frame (axes, slot, space),
  FrameSlot (..),
  Kind (..),
  Len (..),
  Shape (..),
  Space (base, dim, shape, slot),
  SpaceSlot (..),
  Type (..),
  TypeDef (constructors, label, params),
 )

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
  let m = abs n
      len = if m == 0 then 0 else fromIntegral (integerLog2 m) `div` 8 + 1
   in word8 (if n < 0 then 1 else 0)
        <> varint (toInteger len)
        <> bigEndian len m

{- | The @len@ low bytes of a non-negative integer, most significant first.
A long integer is split in halves, so that it costs @n log n@: shifting
it by one byte at a time copied it once per byte, and the encoding of a
100000-digit operand (an exact @1e-99999@ in a nudge's identity) took a
gigabyte.
-}
bigEndian :: Int -> Integer -> Builder
bigEndian len m
  | len <= 32 =
      foldMap
        (\i -> word8 (fromIntegral (m `shiftR` (8 * i))))
        [len - 1, len - 2 .. 0]
  | otherwise =
      let low = len `div` 2
       in bigEndian (len - low) (m `shiftR` (8 * low))
            <> bigEndian low (m .&. (bit (8 * low) - 1))

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
    -- A chart's minted axis type (design §3.9).
    Axes t -> word8 2 <> text t
    -- A space and a frame (design §3.10, F9).
    SpaceLabel t -> word8 3 <> text t
    FrameLabel t moving -> word8 4 <> text t <> word8 (if moving then 1 else 0)

hashTypeDef :: TypeDef -> Hash
hashTypeDef = Hash . SHA256.hash . encodeTypeDef

kindByte :: Kind -> Builder
kindByte = \case
  KType -> word8 0
  KLen -> word8 1
  KShape -> word8 2
  KDim -> word8 3
  -- An axis variable (design §3.9).
  KAxis -> word8 4
  -- A frame and a space (design §3.10, F1).
  KFrame -> word8 5
  KSpace -> word8 6

encType :: Type -> Builder
-- @Bool@, tuples and lists are declared types, 0x28 on the built-in hashes
-- (design §6.1).
encType = \case
  TTensor sh d -> word8 0x21 <> encShape sh <> encDim d
  -- A unit (design §3.10, U1).
  TUnit d -> word8 0x2A <> encDim d
  -- Points, charts and amounts on frames (design §3.10, F4, F9).
  TPoint f -> word8 0x2B <> encFrame f
  TChart f -> word8 0x2C <> encFrame f
  TOver f md -> word8 0x2D <> encFrame f <> maybe (word8 0) ((word8 1 <>) . encDim) md
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
  AFrame f -> word8 5 <> encFrameSlot f
  ASpace sp -> word8 6 <> encSpaceSlot sp

{- | A frame (design §3.10, F9): its slot, its axes and its space, a
space its slot, shape, dimension and base axes.
-}
encFrame :: Frame -> Builder
encFrame f = encFrameSlot f.slot <> encAxis f.axes <> encSpace f.space

encSpace :: Space -> Builder
encSpace sp = encSpaceSlot sp.slot <> encShape sp.shape <> encDim sp.dim <> encAxis sp.base

encFrameSlot :: FrameSlot -> Builder
encFrameSlot = \case
  FrNamed (Hash h) -> word8 0 <> byteString h
  FrVar v -> word8 1 <> varint (fromIntegral v)

encSpaceSlot :: SpaceSlot -> Builder
encSpaceSlot = \case
  SpNamed (Hash h) -> word8 0 <> byteString h
  SpVar v -> word8 1 <> varint (fromIntegral v)

{- | A position with anonymous axes keeps the bytes of a bare length (design
§3.9, §6.1); a named or variable slot is tag 3.
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
  -- rank s + k (design §4.1).
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
