{- | The nominal form and content hashing (design §5.2, §6).

A term's nominal form is its canonical byte encoding: one tag byte per
constructor, hints dropped, variables as de Bruijn indices, rationals in
lowest terms. The hash is SHA-256 of that encoding.
-}
module Eval.Hash (
  encodeTerm,
  hashTerm,
  placeholderHash,
  showHash,
  hashHasPrefix,

  -- * Storage
  encodeStored,
  decodeStored,
  decodeStoredV,
  encodeTypeDef,
  decodeTypeDef,
  hashTypeDef,
  storageVersion,
  hashHex,
  hashFromHex,
) where

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder
import Data.ByteString.Lazy qualified as BL
import Data.Char (digitToInt, isHexDigit)
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Eval.Core
import Eval.Dimension
import Eval.Type

-- | The canonical encoding of a closed term.
encodeTerm :: Term Z -> ByteString
encodeTerm = BL.toStrict . toLazyByteString . enc False (const mempty) 0

{- | The storage encoding (design §7.4): the canonical encoding with each
binder's hint written after its tag, so that @:view@ of a loaded definition
shows the names the author used. Hints do not take part in the hash, so
'decodeStored' followed by 'hashTerm' recovers the stored hash.
-}
encodeStored :: Term Z -> ByteString
encodeStored = BL.toStrict . toLazyByteString . enc False (\(Hint h) -> text h) 0

hashTerm :: Term Z -> Hash
hashTerm = Hash . SHA256.hash . encodeTerm

{- | The ordering hash used to fix member order inside a cycle (design
§6.2): the body is encoded with every free variable, which can only be a
cycle variable, replaced by one placeholder.
-}
placeholderHash :: Term n -> Hash
placeholderHash =
  Hash . SHA256.hash . BL.toStrict . toLazyByteString . enc True (const mempty) 0

{- | Encoding. The 'Bool' says whether free variables become placeholders;
the function says what to write for a binder's hint (nothing, canonically);
the 'Int' is the number of binders entered so far.
-}
enc :: Bool -> (Hint -> Builder) -> Int -> Term n -> Builder
enc ph hint depth = \case
  Var i
    | ph, finToInt i >= depth -> word8 0x10
    | otherwise -> word8 0x00 <> varint (fromIntegral (finToInt i))
  Ref (Hash h) idx name ->
    word8 0x01
      <> byteString h
      <> varint (maybe 0 (fromIntegral . (+ 1)) idx)
      <> hint name
  PrimApp p args -> word8 0x02 <> text p <> foldMap (enc ph hint depth) args
  Lit (LTensor (dims, rs)) ->
    word8 0x03
      <> varint (fromIntegral (length dims))
      <> foldMap (varint . fromIntegral) dims
      <> foldMap (\r -> sint (numerator r) <> varint (denominator r)) rs
  Lam h b -> word8 0x05 <> hint h <> enc ph hint (depth + 1) b
  App f a -> word8 0x06 <> enc ph hint depth f <> enc ph hint depth a
  Let h e b -> word8 0x07 <> hint h <> enc ph hint depth e <> enc ph hint (depth + 1) b
  Pow t n -> word8 0x09 <> enc ph hint depth t <> sint n
  Con c as ->
    word8 0x11
      <> conRef c
      <> varint (fromIntegral (length as))
      <> foldMap (enc ph hint depth) as
  Case s alts ->
    word8 0x12
      <> enc ph hint depth s
      <> varint (fromIntegral (length alts))
      <> foldMap encAlt alts
   where
    encAlt (Alt c hs b) =
      conRef c
        <> varint (fromIntegral (vecLength hs))
        <> foldMap hint (vecToList hs)
        <> enc ph hint (depth + vecLength hs) b
  Noise k l n -> word8 0x0A <> kind k <> label l <> varint n
  Uncertain k l x e ->
    word8 0x0B <> kind k <> label l <> enc ph hint depth x <> enc ph hint depth e
  Pack ts ->
    word8 0x0C
      <> varint (fromIntegral (length ts))
      <> foldMap (enc ph hint depth) ts
  Cycle hs bodies ->
    let k = vecLength bodies
     in word8 0x0E
          <> varint (fromIntegral k)
          <> foldMap hint (vecToList hs)
          <> foldMap (enc ph hint (depth + k)) (vecToList bodies)
  Proj t i -> word8 0x0F <> enc ph hint depth t <> varint (fromIntegral i)
 where
  kind = \case
    Bound -> word8 0
    Stat -> word8 1
  label = \case
    Owner t -> word8 0 <> text t
    Tag t -> word8 1 <> text t
  -- A built-in constructor is its name; a declared one is an empty name,
  -- the type's hash and the index, so built-in encodings never changed.
  conRef = \case
    Builtin c -> text c
    UserCon (Hash h) i -> text "" <> byteString h <> varint (fromIntegral i)

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

-- Decoding ------------------------------------------------------------------------

{- | Read a term in the storage encoding. The scope is rebuilt as the binders
are entered, so the result is well-scoped by construction; an index that
escapes its scope, an unknown tag or a placeholder is an error.
-}

-- | The storage encoding version this build writes (design §7.4).
storageVersion :: Int
storageVersion = 3

decodeStored :: ByteString -> Either Text (Term Z)
decodeStored = decodeStoredV storageVersion

{- | Decode a term written by a given storage version. Version 1 wrote no
name hint after a reference.
-}
decodeStoredV :: Int -> ByteString -> Either Text (Term Z)
decodeStoredV version bs = do
  (t, end) <- runDec (term (version >= 2) DZ) bs 0
  if end == BS.length bs
    then Right t
    else Left ("trailing bytes after the term at offset " <> T.pack (show end))

-- | The number of binders in scope, as a singleton.
data Depth (n :: Nat) where
  DZ :: Depth Z
  DS :: Depth n -> Depth (S n)

finAt :: Depth n -> Int -> Maybe (Fin n)
finAt d i = case d of
  DZ -> Nothing
  DS d'
    | i == 0 -> Just FZ
    | otherwise -> FS <$> finAt d' (i - 1)

depthPlus :: Vec k a -> Depth n -> Depth (Plus k n)
depthPlus xs d = case xs of
  VNil -> d
  VCons _ rest -> DS (depthPlus rest d)

newtype Dec a = Dec (ByteString -> Int -> Either Text (a, Int))

runDec :: Dec a -> ByteString -> Int -> Either Text (a, Int)
runDec (Dec f) = f

instance Functor Dec where
  fmap f (Dec g) = Dec (\bs i -> (\(a, j) -> (f a, j)) <$> g bs i)

instance Applicative Dec where
  pure a = Dec (\_ i -> Right (a, i))
  Dec f <*> Dec g = Dec (\bs i -> f bs i >>= \(h, j) -> g bs j >>= \(a, k) -> Right (h a, k))

instance Monad Dec where
  Dec g >>= f = Dec (\bs i -> g bs i >>= \(a, j) -> runDec (f a) bs j)

failDec :: Text -> Dec a
failDec msg = Dec (\_ i -> Left (msg <> " at offset " <> T.pack (show i)))

byte :: Dec Int
byte =
  Dec
    ( \bs i ->
        maybe
          (Left "unexpected end of term")
          (\b -> Right (fromIntegral b, i + 1))
          (BS.indexMaybe bs i)
    )

bytes :: Int -> Dec ByteString
bytes n =
  Dec
    ( \bs i ->
        if i + n <= BS.length bs
          then Right (BS.take n (BS.drop i bs), i + n)
          else Left "unexpected end of term"
    )

decVarint :: Dec Integer
decVarint = go 0 0
 where
  go shift acc = do
    b <- byte
    let acc' = acc .|. (fromIntegral (b .&. 0x7F) `shiftL` shift)
    if b .&. 0x80 == 0 then pure acc' else go (shift + 7) acc'

decSint :: Dec Integer
decSint = do
  sign <- byte
  len <- decVarint
  mag <- bytes (fromIntegral len)
  let n = BS.foldl' (\acc b -> acc `shiftL` 8 .|. fromIntegral b) 0 mag
  pure (if sign == 1 then negate n else n)

decText :: Dec Text
decText = do
  len <- decVarint
  raw <- bytes (fromIntegral len)
  either (const (failDec "a name is not valid UTF-8")) pure (TE.decodeUtf8' raw)

decKind :: Dec NudgeKind
decKind =
  byte >>= \case
    0 -> pure Bound
    1 -> pure Stat
    k -> failDec ("unknown nudge kind " <> T.pack (show k))

decLabel :: Dec Label
decLabel =
  byte >>= \case
    0 -> Owner <$> decText
    1 -> Tag <$> decText
    k -> failDec ("unknown label kind " <> T.pack (show k))

decHint :: Dec Hint
decHint = Hint <$> decText

term :: Bool -> Depth n -> Dec (Term n)
term refHints d =
  byte >>= \case
    0x00 -> do
      i <- decVarint
      maybe
        (failDec ("variable " <> T.pack (show i) <> " escapes its scope"))
        (pure . Var)
        (finAt d (fromIntegral i))
    0x01 -> do
      h <- bytes 32
      idx <- decVarint
      name <- if refHints then decHint else pure (Hint "")
      pure
        (Ref (Hash h) (if idx == 0 then Nothing else Just (fromIntegral idx - 1)) name)
    0x02 -> do
      p <- decText
      case primArity p of
        Nothing -> failDec ("unknown primitive " <> p)
        Just n -> PrimApp p <$> traverse (const (term refHints d)) [1 .. n]
    0x03 -> do
      rank <- decVarint
      dims <- traverse (const (fromIntegral <$> decVarint)) [1 .. rank]
      rs <- traverse (const ((%) <$> decSint <*> decVarint)) [1 .. product dims]
      pure (Lit (LTensor (dims, rs)))
    -- Retired tags, read from stores of format 2 and before (design §6.1).
    0x04 -> (\b -> Con (Builtin (if b == 1 then "True" else "False")) []) <$> byte
    0x05 -> Lam <$> decHint <*> term refHints (DS d)
    0x06 -> App <$> term refHints d <*> term refHints d
    0x07 -> Let <$> decHint <*> term refHints d <*> term refHints (DS d)
    0x08 -> do
      c <- term refHints d
      t <- term refHints d
      e <- term refHints d
      pure (Case c [Alt (Builtin "False") VNil e, Alt (Builtin "True") VNil t])
    0x09 -> Pow <$> term refHints d <*> decSint
    0x0A -> Noise <$> decKind <*> decLabel <*> decVarint
    0x0B -> Uncertain <$> decKind <*> decLabel <*> term refHints d <*> term refHints d
    0x0C -> do
      n <- decVarint
      Pack <$> traverse (const (term refHints d)) [1 .. n]
    0x0E -> do
      k <- decVarint
      hints <- traverse (const decHint) [1 .. k]
      case vecFromList hints of
        SomeVec hs -> Cycle hs <$> vecTraverse (const (term refHints (depthPlus hs d))) hs
    0x0F -> Proj <$> term refHints d <*> (fromIntegral <$> decVarint)
    0x11 -> do
      c <- decConRef
      k <- decVarint
      Con c <$> traverse (const (term refHints d)) [1 .. k]
    0x12 -> do
      s <- term refHints d
      n <- decVarint
      alts <- traverse (const alt) [1 .. n]
      pure (Case s alts)
     where
      alt = do
        c <- decConRef
        k <- decVarint
        hints <- traverse (const decHint) [1 .. k]
        case vecFromList hints of
          SomeVec hs -> Alt c hs <$> term refHints (depthPlus hs d)
    0x10 -> failDec "a placeholder cannot be stored"
    tag -> failDec ("unknown term tag " <> T.pack (show tag))

-- Hex -------------------------------------------------------------------------------

-- | The full digest as lowercase hex: the file name of a stored term.
hashHex :: Hash -> Text
hashHex (Hash bs) = T.pack (concatMap hex (BS.unpack bs))
 where
  hex b = [digit (fromIntegral b `shiftR` 4), digit (fromIntegral b .&. 15)]
  digit i = "0123456789abcdef" !! i

hashFromHex :: Text -> Maybe Hash
hashFromHex t
  | T.length t == 64
  , all isHexDigit (T.unpack t) =
      Just (Hash (BS.pack (pairs (map digitToInt (T.unpack t)))))
  | otherwise = Nothing
 where
  pairs (a : b : rest) = fromIntegral (a * 16 + b) : pairs rest
  pairs _ = []

decConRef :: Dec ConRef
decConRef = do
  name <- decText
  if T.null name
    then UserCon . Hash <$> bytes 32 <*> (fromIntegral <$> decVarint)
    else pure (Builtin name)

-- Type definitions -------------------------------------------------------------------

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

hashTypeDef :: TypeDef -> Hash
hashTypeDef = Hash . SHA256.hash . encodeTypeDef

kindByte :: Kind -> Builder
kindByte = \case
  KType -> word8 0
  KLen -> word8 1
  KShape -> word8 2
  KDim -> word8 3

encType :: Type -> Builder
encType = \case
  TBool -> word8 0x20
  TTensor sh d -> word8 0x21 <> encShape sh <> encDim d
  TPoint sh d -> word8 0x22 <> encShape sh <> encDim d
  TScale sh d -> word8 0x23 <> encShape sh <> encDim d
  TTuple ts -> word8 0x24 <> varint (fromIntegral (length ts)) <> foldMap encType ts
  TList t -> word8 0x25 <> encType t
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

encShape :: Shape -> Builder
encShape = \case
  SNil -> word8 0
  SCons l rest -> word8 1 <> encLen l <> encShape rest
  SVar v -> word8 2 <> varint (fromIntegral v)

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

decodeTypeDef :: ByteString -> Either Text TypeDef
decodeTypeDef bs = do
  (def, end) <- runDec typeDef bs 0
  if end == BS.length bs
    then Right def
    else Left "trailing bytes after the type definition"
 where
  typeDef = do
    np <- decVarint
    kinds <- traverse (const decKindByte) [1 .. np]
    nc <- decVarint
    cons <-
      traverse
        (const (decVarint >>= \nf -> traverse (const decType) [1 .. nf]))
        [1 .. nc]
    TypeDef (zip [0 ..] kinds) cons <$> decLabel
  decKindByte =
    byte >>= \case
      0 -> pure KType
      1 -> pure KLen
      2 -> pure KShape
      3 -> pure KDim
      k -> failDec ("unknown kind " <> T.pack (show k))

decType :: Dec Type
decType =
  byte >>= \case
    0x20 -> pure TBool
    0x21 -> TTensor <$> decShape <*> decDim
    0x22 -> TPoint <$> decShape <*> decDim
    0x23 -> TScale <$> decShape <*> decDim
    0x24 -> decVarint >>= \n -> TTuple <$> traverse (const decType) [1 .. n]
    0x25 -> TList <$> decType
    0x26 -> TFun <$> decType <*> decType
    0x27 -> TVar . fromIntegral <$> decVarint
    0x28 -> do
      h <- bytes 32
      n <- decVarint
      TData (Hash h) <$> traverse (const decArg) [1 .. n]
    tag -> failDec ("unknown type tag " <> T.pack (show tag))
 where
  decArg =
    byte >>= \case
      0 -> AType <$> decType
      1 -> ALen <$> decLen
      2 -> AShape <$> decShape
      3 -> ADim <$> decDim
      k -> failDec ("unknown argument kind " <> T.pack (show k))
  decShape =
    byte >>= \case
      0 -> pure SNil
      1 -> SCons <$> decLen <*> decShape
      2 -> SVar . fromIntegral <$> decVarint
      k -> failDec ("unknown shape tag " <> T.pack (show k))
  decLen =
    byte >>= \case
      0 -> LLit . fromIntegral <$> decVarint
      1 -> LVar . fromIntegral <$> decVarint <*> (fromIntegral <$> decVarint)
      2 -> LRank . fromIntegral <$> decVarint <*> (fromIntegral <$> decVarint)
      k -> failDec ("unknown length tag " <> T.pack (show k))
  decDim = do
    n <- decVarint
    atoms <-
      traverse
        ( const
            ( byte >>= \case
                0 ->
                  (\b k -> (Base (toEnum (fromIntegral b)), fromIntegral k)) <$> byte <*> decSint
                1 -> (\v k -> (DVar (fromIntegral v), fromIntegral k)) <$> decVarint <*> decSint
                k -> failDec ("unknown dimension atom " <> T.pack (show k))
            )
        )
        [1 .. n]
    pure (dimFromAtoms atoms)
