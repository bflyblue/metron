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
  decodeTypeDefV,
  hashTypeDef,
  storageVersion,
  hashHex,
  hashFromHex,
) where

import Crypto.Hash.SHA256 qualified as SHA256
import Data.Bifunctor (first)
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
import Eval.Builtin
import Eval.Core
import Eval.Dimension
import Eval.Encode
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
  -- A constructor is an empty name, the type's hash and the index. The
  -- empty name is what is left of the built-in constructors, which were
  -- their names until storage version 4 (design §6.1).
  conRef (UserCon (Hash h) i) = text "" <> byteString h <> varint (fromIntegral i)

-- Decoding ------------------------------------------------------------------------

{- | The storage encoding version this build writes (design §7.4). Version
2 added the written name after a reference; version 4 retired the
built-in constructors' names and the types @Bool@, tuple and list, which
are declared types on the hashes of "Eval.Builtin".
-}
storageVersion :: Int
storageVersion = 4

decodeStored :: ByteString -> Either Text (Term Z)
decodeStored = decodeStoredV storageVersion

{- | Read a term in the storage encoding written by a given storage version.
The scope is rebuilt as the binders are entered, so the result is
well-scoped by construction; an index that escapes its scope, an unknown
tag or a placeholder is an error. Version 1 wrote no name hint after a
reference; versions up to 3 may hold the retired forms (the boolean
literal, @If@, the built-in constructors by name), which are read as the
constructors of the built-in declarations, so the term read back is a
current one, with a new hash where it held them.
-}
decodeStoredV :: Int -> ByteString -> Either Text (Term Z)
decodeStoredV version bs = do
  (t, end) <- runDec (term version DZ) bs 0
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
    k -> failDec ("unknown label kind " <> T.pack (show k))

decHint :: Dec Hint
decHint = Hint <$> decText

term :: Int -> Depth n -> Dec (Term n)
term version d =
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
      name <- if version >= 2 then decHint else pure (Hint "")
      pure
        (Ref (Hash h) (if idx == 0 then Nothing else Just (fromIntegral idx - 1)) name)
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
    -- Retired tags, read from stores of format 2 and before (design §6.1).
    0x04 | legacy -> (\b -> Con (boolC (b == 1)) []) <$> byte
    0x05 -> Lam <$> decHint <*> term version (DS d)
    0x06 -> App <$> sub <*> sub
    0x07 -> Let <$> decHint <*> sub <*> term version (DS d)
    0x08 | legacy -> do
      c <- sub
      t <- sub
      e <- sub
      pure (Case c [Alt falseC VNil e, Alt trueC VNil t])
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
        SomeVec hs -> Cycle hs <$> vecTraverse (const (term version (depthPlus hs d))) hs
    0x0F -> Proj <$> sub <*> (fromIntegral <$> decVarint)
    0x11 -> do
      con <- decConRef
      k <- decVarint
      c <- resolveCon con (fromIntegral k)
      Con c <$> traverse (const sub) [1 .. k]
    0x12 -> do
      s <- sub
      n <- decVarint
      alts <- traverse (const alt) [1 .. n]
      pure (Case s alts)
     where
      alt = do
        con <- decConRef
        k <- decVarint
        c <- resolveCon con (fromIntegral k)
        hints <- traverse (const decHint) [1 .. k]
        case vecFromList hints of
          SomeVec hs -> Alt c hs <$> term version (depthPlus hs d)
    0x10 -> failDec "a placeholder cannot be stored"
    tag -> failDec ("unknown term tag " <> T.pack (show tag))
 where
  sub = term version d
  legacy = version <= 3
  -- A built-in constructor by name (storage version 3 and before) is the
  -- built-in declaration's; a tuple's needs its number of fields.
  resolveCon con k = case con of
    Right c -> pure c
    Left name
      | legacy
      , Just c <- legacyCon name k ->
          pure c
      | otherwise -> failDec ("unknown constructor " <> name)

-- | A retired built-in constructor name with its number of fields.
legacyCon :: Text -> Int -> Maybe ConRef
legacyCon name k = case (name, k) of
  ("False", 0) -> Just falseC
  ("True", 0) -> Just trueC
  ("Nil", 0) -> Just nilC
  ("Cons", 2) -> Just consC
  ("Tuple", _) | k >= 2 && k <= maxTupleArity -> Just (tupleC k)
  _ -> Nothing

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

-- | A constructor reference: a declared one, or a retired built-in one by name.
decConRef :: Dec (Either Text ConRef)
decConRef = do
  name <- decText
  if T.null name
    then
      (\h i -> Right (UserCon (Hash h) i))
        <$> bytes 32
        <*> (fromIntegral <$> decVarint)
    else pure (Left name)

decodeTypeDef :: ByteString -> Either Text TypeDef
decodeTypeDef = decodeTypeDefV storageVersion

{- | Read a declared type written by a given storage version. Up to version
3 a field may use the retired types @Bool@, tuple and list (tags 0x20,
0x24, 0x25), read as the built-in declared types, so the definition read
back has a new hash where it used them.
-}
decodeTypeDefV :: Int -> ByteString -> Either Text TypeDef
decodeTypeDefV version bs = do
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
        (const (decVarint >>= \nf -> traverse (const (decType version)) [1 .. nf]))
        [1 .. nc]
    TypeDef (zip [0 ..] kinds) cons <$> decLabel
  decKindByte =
    byte >>= \case
      0 -> pure KType
      1 -> pure KLen
      2 -> pure KShape
      3 -> pure KDim
      k -> failDec ("unknown kind " <> T.pack (show k))

decType :: Int -> Dec Type
decType version =
  byte >>= \case
    -- Retired tags, read from storage version 3 and before (design §6.1).
    0x20 | legacy -> pure boolT
    0x24 | legacy -> decVarint >>= \n -> tupleT <$> traverse (const ty) [1 .. n]
    0x25 | legacy -> listT <$> ty
    0x21 -> TTensor <$> decShape <*> decDim
    0x22 -> TPoint <$> decShape <*> decDim
    0x23 -> TScale <$> decShape <*> decDim
    0x26 -> TFun <$> ty <*> ty
    0x27 -> TVar . fromIntegral <$> decVarint
    0x28 -> do
      h <- bytes 32
      n <- decVarint
      TData (Hash h) <$> traverse (const decArg) [1 .. n]
    tag -> failDec ("unknown type tag " <> T.pack (show tag))
 where
  ty = decType version
  legacy = version <= 3
  decArg =
    byte >>= \case
      0 -> AType <$> ty
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
