{- | The nominal form and content hashing (design §5.2, §6).

A term's nominal form is its canonical byte encoding: one tag byte per
constructor, hints dropped, variables as de Bruijn indices, rationals in
lowest terms. The hash is SHA-256 of that encoding.
-}
module Metron.Hash (
  encodeTerm,
  hashTerm,
  placeholderHash,

  -- * Storage
  encodeStored,
  decodeStored,
  encodeTypeDef,
  decodeTypeDef,
  hashTypeDef,
  storageVersion,
  hashHex,
  hashFromHex,
) where

import Data.Bifunctor ( first )
import Data.Bits ( shiftL, shiftR, (.&.), (.|.) )
import Data.ByteString ( ByteString )
import Data.ByteString.Builder
    ( Builder, word8, byteString, toLazyByteString )
import Data.Char ( digitToInt, isHexDigit )
import Data.Ratio ( denominator, numerator, (%) )
import Data.Text ( Text )
import Metron.Core
    ( primArity,
      finToInt,
      vecFromList,
      vecLength,
      vecToList,
      vecTraverse,
      Alt(Alt),
      ConRef(..),
      Fin(..),
      Hash(..),
      Hint(..),
      Label(..),
      Lit(LTensor),
      Nat(..),
      NudgeKind(..),
      Plus,
      SomeVec(SomeVec),
      Term(..),
      Vec(..) )
import Metron.Dimension ( dimFromAtoms, DimAtom(DVar, Base) )
import Metron.Encode
    ( encodeTypeDef, hashTypeDef, sint, text, varint )
import Metron.Type
    ( Arg(ARole, AType, ALen, AShape, ADim, AAxis, AFrame, ASpace),
      Axis(AVar, AAnon, ANamed),
      Frame(Frame),
      FrameSlot(FrVar, FrNamed),
      Kind(KRole, KType, KLen, KShape, KDim, KAxis, KFrame, KSpace),
      Len(LRank, LLit, LVar),
      Role(RVar, RAmount, RUnit),
      Shape(SCons, SNil, SVar),
      Space(Space),
      SpaceSlot(SpVar, SpNamed),
      Type(..),
      TypeDef(TypeDef) )
import Data.ByteString.Lazy qualified as BL ( toStrict )
import Data.ByteString qualified as BS
    ( drop, foldl', indexMaybe, length, pack, take, unpack )
import Crypto.Hash.SHA256 qualified as SHA256 ( hash )
import Data.Text qualified as T ( length, pack, unpack )
import Data.Text.Encoding qualified as TE ( decodeUtf8' )

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
    Axes t -> word8 2 <> text t
    SpaceLabel t -> word8 3 <> text t
    FrameLabel t moving -> word8 4 <> text t <> word8 (if moving then 1 else 0)
  -- A constructor is its type's hash and its index (design §6.1).
  conRef (UserCon (Hash h) i) = byteString h <> varint (fromIntegral i)

-- Decoding ------------------------------------------------------------------------

{- | The storage encoding version this build writes and reads (design §7.4).
Only this version is read; a store written by another is refused by its
format.
-}
storageVersion :: Int
storageVersion = 5

{- | Read a term in the storage encoding. The scope is rebuilt as the
binders are entered, so the result is well-scoped by construction; an
index that escapes its scope, an unknown tag or a placeholder is an error.
-}
decodeStored :: ByteString -> Either Text (Term Z)
decodeStored bs = do
  (t, end) <- runDec (term DZ) bs 0
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
  fmap f (Dec g) = Dec (\bs i -> first f <$> g bs i)

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
    2 -> Axes <$> decText
    3 -> SpaceLabel <$> decText
    4 ->
      FrameLabel
        <$> decText
        <*> ( byte >>= \case
                0 -> pure False
                1 -> pure True
                k -> failDec ("unknown frame flag " <> T.pack (show k))
            )
    k -> failDec ("unknown label kind " <> T.pack (show k))

decHint :: Dec Hint
decHint = Hint <$> decText

term :: Depth n -> Dec (Term n)
term d =
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
      Ref (Hash h) (if idx == 0 then Nothing else Just (fromIntegral idx - 1))
        <$> decHint
    0x02 -> do
      p <- decText
      case primArity p of
        Nothing -> failDec ("unknown primitive " <> p)
        Just n -> PrimApp p <$> traverse (const sub) [1 .. n]
    0x03 -> do
      rank <- decVarint
      dims <- traverse (const (fromIntegral <$> decVarint)) [1 .. rank]
      rs <- traverse (const ((%) <$> decSint <*> decVarint)) [1 .. product dims]
      pure (Lit (LTensor (dims, rs)))
    0x05 -> Lam <$> decHint <*> term (DS d)
    0x06 -> App <$> sub <*> sub
    0x07 -> Let <$> decHint <*> sub <*> term (DS d)
    0x09 -> Pow <$> sub <*> decSint
    0x0A -> Noise <$> decKind <*> decLabel <*> decVarint
    0x0B -> Uncertain <$> decKind <*> decLabel <*> sub <*> sub
    0x0C -> do
      n <- decVarint
      Pack <$> traverse (const sub) [1 .. n]
    0x0E -> do
      k <- decVarint
      hints <- traverse (const decHint) [1 .. k]
      case vecFromList hints of
        SomeVec hs -> Cycle hs <$> vecTraverse (const (term (depthPlus hs d))) hs
    0x0F -> Proj <$> sub <*> (fromIntegral <$> decVarint)
    0x11 -> do
      c <- decConRef
      k <- decVarint
      Con c <$> traverse (const sub) [1 .. k]
    0x12 -> do
      s <- sub
      n <- decVarint
      alts <- traverse (const alt) [1 .. n]
      pure (Case s alts)
     where
      alt = do
        c <- decConRef
        k <- decVarint
        hints <- traverse (const decHint) [1 .. k]
        case vecFromList hints of
          SomeVec hs -> Alt c hs <$> term (depthPlus hs d)
    0x10 -> failDec "a placeholder cannot be stored"
    tag -> failDec ("unknown term tag " <> T.pack (show tag))
 where
  sub = term d

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

-- | A constructor reference: the type's hash and the index.
decConRef :: Dec ConRef
decConRef = UserCon . Hash <$> bytes 32 <*> (fromIntegral <$> decVarint)

-- | Read a declared type in the storage encoding.
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
      4 -> pure KAxis
      5 -> pure KFrame
      6 -> pure KSpace
      7 -> pure KRole
      k -> failDec ("unknown kind " <> T.pack (show k))

decType :: Dec Type
decType =
  byte >>= \case
    0x21 -> TTensor <$> decShape <*> decDim
    0x2A -> TUnit <$> decDim
    0x2E -> TQty <$> decRole <*> decShape <*> decDim
    0x2B -> TPoint <$> decFrame
    0x2C -> TChart <$> decFrame
    0x2D ->
      TOver
        <$> decFrame
        <*> ( byte >>= \case
                0 -> pure Nothing
                1 -> Just <$> decDim
                k -> failDec ("unknown dimension option " <> T.pack (show k))
            )
    0x26 -> TFun <$> ty <*> ty
    0x27 -> TVar . fromIntegral <$> decVarint
    0x28 -> do
      h <- bytes 32
      n <- decVarint
      TData (Hash h) <$> traverse (const decArg) [1 .. n]
    tag -> failDec ("unknown type tag " <> T.pack (show tag))
 where
  ty = decType
  decArg =
    byte >>= \case
      0 -> AType <$> ty
      1 -> ALen <$> decLen
      2 -> AShape <$> decShape
      3 -> ADim <$> decDim
      4 -> AAxis <$> decAxis
      5 -> AFrame <$> decFrameSlot
      6 -> ASpace <$> decSpaceSlot
      7 -> ARole <$> decRole
      k -> failDec ("unknown argument kind " <> T.pack (show k))
  decRole =
    byte >>= \case
      0 -> pure RAmount
      1 -> pure RUnit
      2 -> RVar . fromIntegral <$> decVarint
      k -> failDec ("unknown role " <> T.pack (show k))
  decShape =
    byte >>= \case
      0 -> pure SNil
      1 -> (`SCons` AAnon) <$> decLen <*> decShape
      2 -> SVar . fromIntegral <$> decVarint
      3 -> SCons <$> decLen <*> decAxis <*> decShape
      k -> failDec ("unknown shape tag " <> T.pack (show k))
  decFrame = Frame <$> decFrameSlot <*> decAxis <*> decSpace
  decSpace = Space <$> decSpaceSlot <*> decShape <*> decDim <*> decAxis
  decFrameSlot =
    byte >>= \case
      0 -> FrNamed . Hash <$> bytes 32
      1 -> FrVar . fromIntegral <$> decVarint
      k -> failDec ("unknown frame tag " <> T.pack (show k))
  decSpaceSlot =
    byte >>= \case
      0 -> SpNamed . Hash <$> bytes 32
      1 -> SpVar . fromIntegral <$> decVarint
      k -> failDec ("unknown space tag " <> T.pack (show k))
  decAxis =
    byte >>= \case
      0 -> pure AAnon
      1 -> ANamed . Hash <$> bytes 32
      2 -> AVar . fromIntegral <$> decVarint
      k -> failDec ("unknown axis tag " <> T.pack (show k))
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
                0 -> do
                  b <- byte
                  case lookup b (zip [0 ..] [minBound .. maxBound]) of
                    Just base -> (Base base,) <$> decSint
                    Nothing -> failDec ("unknown base dimension " <> T.pack (show b))
                1 -> (\v k -> (DVar (fromIntegral v), k)) <$> decVarint <*> decSint
                k -> failDec ("unknown dimension atom " <> T.pack (show k))
            )
        )
        [1 .. n]
    pure (dimFromAtoms atoms)
