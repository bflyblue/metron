{-# LANGUAGE TypeFamilies #-}

{- | Core: the desugared, untyped, well-scoped term language (design §5.1).

Core is an abstract binding tree with de Bruijn indices, indexed by the
number of variables in scope: a @Term n@ may mention variables @0 .. n-1@
and nothing else, so a dangling variable is a Haskell type error. Binders
carry a 'Hint', the name the user wrote, for printing only: 'alphaEq' and
hashing ignore hints.

Primitives are saturated: @PrimApp p args@ always carries exactly
'primArity' arguments. Partial uses are eta-expanded by the desugarer.
-}
module Metron.Core (
  -- * Type-level naturals and scope-safe indices
  Nat (..),
  Fin (..),
  finToInt,
  Vec (..),
  SomeVec (..),
  vecFromList,
  vecToList,
  vecLength,
  vecMap,
  vecMapIndexed,
  vecZip3,
  vecZipWith,
  vecTraverse,
  vecIndex,
  vecAppend,
  Plus,

  -- * Terms
  Hash (..),
  showHash,
  showFullHash,
  hashHasPrefix,
  Hint (..),
  etaHint,
  Label (..),
  renderLabel,
  Lit (..),
  Term (..),
  Alt (..),
  ConRef (..),
  weakenBy,
  strengthen,
  alphaEq,
  refs,
  conTypes,
  refsWithIndex,
  directUses,
  rewriteRefs,
  rewriteRefsWritten,
  refsWritten,
  inlineRef,
  primArity,
  lengthLimit,

  -- * Traversal
  traverseChildren,
  mapChildren,
  foldChildren,
  foldTerm,
  Child (..),
  children,
) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (unpack)
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Set (Set)
import Data.Set qualified as Set (empty, map, singleton)
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T (
  dropWhile,
  isPrefixOf,
  pack,
  take,
 )
import Metron.Primitive (primArity)

-- Type-level naturals ------------------------------------------------------

data Nat = Z | S Nat

type family Plus (a :: Nat) (b :: Nat) :: Nat where
  Plus Z b = b
  Plus (S a) b = S (Plus a b)

-- | A number strictly below @n@: a scope-safe de Bruijn index.
data Fin :: Nat -> Type where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

deriving stock instance Show (Fin n)
deriving stock instance Eq (Fin n)
deriving stock instance Ord (Fin n)

finToInt :: Fin n -> Int
finToInt = \case
  FZ -> 0
  FS i -> 1 + finToInt i

-- | A length-indexed list.
data Vec (k :: Nat) a where
  VNil :: Vec Z a
  VCons :: a -> Vec k a -> Vec (S k) a

deriving stock instance (Show a) => Show (Vec k a)
deriving stock instance (Eq a) => Eq (Vec k a)

vecToList :: Vec k a -> [a]
vecToList = \case
  VNil -> []
  VCons x xs -> x : vecToList xs

vecLength :: Vec k a -> Int
vecLength = length . vecToList

-- | Lazy in the elements: only the spine is inspected.
vecMap :: (a -> b) -> Vec k a -> Vec k b
vecMap f = \case
  VNil -> VNil
  VCons x xs -> VCons (f x) (vecMap f xs)

vecIndex :: Int -> Vec k a -> Maybe a
vecIndex i = \case
  VNil -> Nothing
  VCons x xs
    | i == 0 -> Just x
    | i < 0 -> Nothing
    | otherwise -> vecIndex (i - 1) xs

vecTraverse :: (Applicative f) => (a -> f b) -> Vec k a -> f (Vec k b)
vecTraverse f = \case
  VNil -> pure VNil
  VCons x xs -> VCons <$> f x <*> vecTraverse f xs

vecAppend :: Vec k a -> Vec n a -> Vec (Plus k n) a
vecAppend xs ys = case xs of
  VNil -> ys
  VCons x rest -> VCons x (vecAppend rest ys)

vecMapIndexed :: forall a b k. (Int -> a -> b) -> Vec k a -> Vec k b
vecMapIndexed f = walk 0
 where
  walk :: forall m. Int -> Vec m a -> Vec m b
  walk _ VNil = VNil
  walk i (VCons x xs) = VCons (f i x) (walk (i + 1) xs)

vecZip3 :: Vec k a -> Vec k b -> Vec k c -> Vec k (a, b, c)
vecZip3 as bs cs = case (as, bs, cs) of
  (VNil, VNil, VNil) -> VNil
  (VCons a as', VCons b bs', VCons c cs') -> VCons (a, b, c) (vecZip3 as' bs' cs')

vecZipWith :: (a -> b -> c) -> Vec k a -> Vec k b -> Vec k c
vecZipWith f as bs = case (as, bs) of
  (VNil, VNil) -> VNil
  (VCons a as', VCons b bs') -> VCons (f a b) (vecZipWith f as' bs')

-- | A vector of statically unknown length.
data SomeVec a = forall k. SomeVec (Vec k a)

vecFromList :: [a] -> SomeVec a
vecFromList = \case
  [] -> SomeVec VNil
  x : xs -> case vecFromList xs of
    SomeVec v -> SomeVec (VCons x v)

-- Terms ---------------------------------------------------------------------

{- | A content hash of a Core term (design §6): the bytes of a SHA-256 digest.
Defined here so that 'Term' can refer to other terms; hashing itself lives
in "Metron.Hash".
-}
newtype Hash = Hash ByteString
  deriving stock (Eq, Ord, Show)

-- | A name hint on a binder. Ignored by 'alphaEq' and by hashing.
newtype Hint = Hint Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString)

{- | The hint on each binder of an eta-expansion the desugarer makes, for a
primitive used with fewer arguments than its arity (design §2.9). No
identifier spells it, so the printer can tell such a lambda from one the
user wrote, and print the primitive as it was written.
-}
etaHint :: Hint
etaHint = Hint "§eta"

{- | Who a declared uncertainty belongs to (design §3.2.4). The desugarer
stamps every @±@, @ and @ with the name of the definition it is
written in, so two definitions with identical bodies are different terms
and therefore different measurements; the nudge's identity is still the
definition hash and the path. A @#label@ written by the user is a global
identity instead: every @±@ with that label and midpoint is one unknown,
wherever it appears. Only a tag is printed; the owner stamp is implied by
the binding.

The third kind stamps the axis type a chart or a space declaration mints
(design §3.9, decision 1; §3.10, F2) with its full path: no source @data@
and no uncertainty carries it, so a user's @data Eci = Eci@ never equals
it. The last two stamp the nominal types a space and a chart declaration
mint (design §3.10, F2, F3): a space, and a frame, with whether its chart
takes parameters (F7).
-}
data Label
  = Owner Text
  | Tag Text
  | Axes Text
  | SpaceLabel Text
  | FrameLabel Text Bool
  deriving stock (Eq, Ord, Show)

renderLabel :: Label -> Text
renderLabel = \case
  Tag t -> " #" <> t
  _ -> ""

{- | A constant tensor: its shape and its values flat in row-major order; a
number is the rank-zero case. Booleans are data ('Con').
-}
newtype Lit = LTensor ([Int], [Rational])
  deriving stock (Eq, Ord, Show)

{- | Core terms in a scope of @n@ variables. @Var FZ@ is the innermost
binder. 'Lam' and 'Let' bind one variable in their body. 'Cycle' binds
@k@ variables in every body: inside body @i@, index @j < k@ (at depth 0) is
member @j@.
-}
data Term (n :: Nat) where
  Var :: Fin n -> Term n
  {- | Another definition by content hash, with a cycle index when the
  referenced term is a 'Cycle'.
  -}
  Ref :: Hash -> Maybe Int -> Hint -> Term n
  {- | A saturated primitive application: exactly 'primArity' arguments.
  Overloading is unresolved here: @PrimApp "add"@ is the overloaded
  addition.
  -}
  PrimApp :: Text -> [Term n] -> Term n
  Lit :: Lit -> Term n
  Lam :: Hint -> Term (S n) -> Term n
  App :: Term n -> Term n -> Term n
  -- | Non-recursive, generalising local binding: @Let h e b@ binds @e@ in @b@.
  Let :: Hint -> Term n -> Term (S n) -> Term n
  {- | A saturated data constructor (design §5.1): constructor @i@ of a
  declared type, @true@, @(a, b)@ and @x : xs@ among them.
  -}
  Con :: ConRef -> [Term n] -> Term n
  {- | Case analysis: one alternative per constructor of the scrutinee's type,
  in canonical (declaration) order, each binding the constructor's fields. Lazy in
  the bodies.
  -}
  Case :: Term n -> [Alt n] -> Term n
  -- | @e ^ n@ with a literal integer exponent.
  Pow :: Term n -> Integer -> Term n
  -- | Draw from a distribution, with a stable lexical owner or explicit tag.
  Sample :: Label -> Term n -> Term n
  {- | @[a, b, c]@: stack @k@ tensors of shape @s@ into one of shape @k : s@.
  A literal whose elements are all constants is folded into 'Lit' by the
  desugarer, so the two never describe the same value.
  -}
  Pack :: [Term n] -> Term n
  {- | @v.i@ or @m.i@: component or row at a literal position. The position
  is checked against the length statically (design §4.1).
  -}
  Proj :: Term n -> Int -> Term n
  -- | @k@ mutually recursive bodies, each in scope of the @k@ members.
  Cycle :: Vec k Hint -> Vec k (Term (Plus k n)) -> Term n

{- | A data constructor: constructor @i@ of a declared type, by the type's
hash (design §2.3). Names are labels. The constructors the syntax builds,
@true@, @(a, b)@, @x : xs@, are those of declarations the compiler holds
("Metron.Builtin"), so there are no others.
-}
data ConRef = UserCon Hash Int
  deriving stock (Eq, Ord, Show)

-- | An alternative of a 'Case': constructor, field hints, body in scope of the fields.
data Alt n = forall k. Alt ConRef (Vec k Hint) (Term (Plus k n))

{- | The largest length, count or index position a program may write, 2^40
(design §3.3). Lengths are machine integers: a larger one is refused,
never wrapped. It bounds what a type or a literal can name, so that a
definition checks the same in every session; how many components a
tensor may actually have is the session's @components@ setting (design
§8.1), checked when one is built.
-}
lengthLimit :: Integer
lengthLimit = 2 ^ (40 :: Int)

instance Show (Alt n) where
  show (Alt c hs b) = "Alt " ++ show c ++ " " ++ show (vecToList hs) ++ " (" ++ show b ++ ")"

deriving stock instance Show (Term n)

{- | Alpha-equivalence: structural equality ignoring hints. Because variables
are de Bruijn indices this is a plain structural walk. The scopes may
differ in type; only the indices are compared.
-}
alphaEq :: Term n -> Term m -> Bool
alphaEq = go
 where
  go :: Term a -> Term b -> Bool
  go (Var i) (Var j) = finToInt i == finToInt j
  go (Ref h i _) (Ref h' i' _) = h == h' && i == i'
  go (PrimApp p as) (PrimApp q bs) = p == q && goList as bs
  go (Lit l) (Lit l') = l == l'
  go (Lam _ b) (Lam _ b') = go b b'
  go (App f a) (App g b) = go f g && go a b
  go (Let _ e b) (Let _ e' b') = go e e' && go b b'
  go (Con c as) (Con c' bs) = c == c' && goList as bs
  go (Case s as) (Case s' bs) = go s s' && length as == length bs && and (zipWith goAlt as bs)
  go (Pow t n) (Pow t' n') = n == n' && go t t'
  go (Sample l x) (Sample l' x') = l == l' && go x x'
  go (Pack as) (Pack bs) = goList as bs
  go (Proj t i) (Proj t' i') = i == i' && go t t'
  go (Cycle _ bs) (Cycle _ bs') = goList (vecToList bs) (vecToList bs')
  go _ _ = False

  goList :: [Term a] -> [Term b] -> Bool
  goList as bs = length as == length bs && and (zipWith go as bs)
  goAlt :: Alt a -> Alt b -> Bool
  goAlt (Alt c hs b) (Alt c' hs' b') = c == c' && vecLength hs == vecLength hs' && go b b'

-- Traversal -----------------------------------------------------------------

{- | One layer of a term: the variable hook at a 'Var', and the child hook
on each immediate subterm, left to right, with the binders it sits under
(innermost first: a lambda's or a let's one hint, an alternative's fields,
a cycle's members). Everything else is rebuilt as it is. This is the one
place that knows where each constructor keeps its subterms and what each
binds; every walk over Core is built on it, so a new constructor is added
here and in the walks that give it a meaning of its own (core.md §7).
-}
traverseChildren ::
  forall f n m.
  (Applicative f) =>
  (Fin n -> f (Term m)) ->
  (forall k. Vec k Hint -> Term (Plus k n) -> f (Term (Plus k m))) ->
  Term n ->
  f (Term m)
traverseChildren var child = \case
  Var i -> var i
  Ref h i hint -> pure (Ref h i hint)
  PrimApp p as -> PrimApp p <$> traverse plain as
  Lit l -> pure (Lit l)
  Lam h b -> Lam h <$> child (VCons h VNil) b
  App f a -> App <$> plain f <*> plain a
  Let h e b -> Let h <$> plain e <*> child (VCons h VNil) b
  Con c as -> Con c <$> traverse plain as
  Case s alts ->
    Case <$> plain s <*> traverse (\(Alt c hs b) -> Alt c hs <$> child hs b) alts
  Pow t n -> (`Pow` n) <$> plain t
  Sample l x -> Sample l <$> plain x
  Pack ts -> Pack <$> traverse plain ts
  Proj t i -> (`Proj` i) <$> plain t
  Cycle hs bs -> Cycle hs <$> vecTraverse (child hs) bs
 where
  plain :: Term n -> f (Term m)
  plain = child VNil
{-# INLINE traverseChildren #-}

-- | Rebuild a term with a function applied to each immediate subterm.
mapChildren :: (forall m. Term m -> Term m) -> Term n -> Term n
mapChildren f = runIdentity . traverseChildren (Identity . Var) (\_ -> Identity . f)

-- | Combine what a function makes of each immediate subterm.
foldChildren :: (Monoid r) => (forall m. Term m -> r) -> Term n -> r
foldChildren f = getConst . traverseChildren @_ @_ @Z (\_ -> Const mempty) (\_ -> Const . f)

{- | Combine what a function makes of every node of a term, the term itself
first: a fold in which each node says only what it contributes itself.
-}
foldTerm :: (Monoid r) => (forall m. Term m -> r) -> Term n -> r
foldTerm here t = here t <> foldChildren (foldTerm here) t

-- | An immediate subterm with the binders it sits under, innermost first.
data Child n = forall k. Child (Vec k Hint) (Term (Plus k n))

-- | The immediate subterms of a term, in order ('traverseChildren').
children :: forall n. Term n -> [Child n]
children =
  getConst
    . traverseChildren @_ @n @n (\_ -> Const []) (\hs b -> Const [Child hs b])

-- | The hashes a term refers to.
refs :: Term n -> Set Hash
refs = Set.map fst . refsWithIndex

-- | The declared types whose constructors a term builds or matches.
conTypes :: Term n -> Set Hash
conTypes = foldTerm $ \case
  Con c _ -> conType c
  Case _ alts -> foldMap (\(Alt c _ _) -> conType c) alts
  _ -> Set.empty
 where
  conType (UserCon h _) = Set.singleton h

-- | The references a term makes, with their cycle indices.
refsWithIndex :: Term n -> Set (Hash, Maybe Int)
refsWithIndex = fst . directUses (const False)

{- | What a term uses directly, in one walk: the references it makes, with
their cycle indices, and the operations it names that the test picks out,
the built-ins only one backend has (design §8.2). An uncertainty form is
named as it is written: @±@, @±σ@, @noise@, @gauss@.
-}
directUses :: (Text -> Bool) -> Term n -> (Set (Hash, Maybe Int), Set Text)
directUses picked = foldTerm $ \case
  Ref h i _ -> (Set.singleton (h, i), Set.empty)
  PrimApp p _ -> named p
  Sample _ _ -> named "sample"
  _ -> mempty
 where
  named p = (Set.empty, if picked p then Set.singleton p else Set.empty)

{- | Replace references according to a function; 'Nothing' keeps a reference
as it is. Used to upgrade dependents to a new version (design §7.5).
-}
rewriteRefs ::
  (Hash -> Maybe Int -> Maybe (Hash, Maybe Int)) -> Term n -> Term n
rewriteRefs f = rewriteRefsWritten (\h i _ -> f h i)

{- | Every reference with the name it was written under (the storage hint;
empty for a term loaded from a format-1 store). Propagation follows a
rebinding only through references written under the rebound name (design
§7.5): a user's @meter = m@ and the library's @metre = m@ are one term, but
@km = kilo * metre@ depends on @metre@, not on @meter@.
-}
refsWritten :: Term n -> Set (Hash, Maybe Int, Text)
refsWritten = foldTerm $ \case
  Ref h i (Hint w) -> Set.singleton (h, i, w)
  _ -> Set.empty

-- | 'rewriteRefs' that also sees the written name, which it keeps.
rewriteRefsWritten ::
  (Hash -> Maybe Int -> Text -> Maybe (Hash, Maybe Int)) -> Term n -> Term n
rewriteRefsWritten f = go
 where
  go :: Term m -> Term m
  go = \case
    Ref h i hint@(Hint w) -> maybe (Ref h i hint) (\(h', i') -> Ref h' i' hint) (f h i w)
    t -> mapChildren go t

{- | Replace every reference to a hash (with no cycle index) by a closed
term: how @it@ absorbs the expression before it, so that @:view it@ shows
the whole expression rather than a reference to one that has no name.
-}
inlineRef :: Hash -> Term Z -> Term n -> Term n
inlineRef target replacement = go
 where
  go :: Term m -> Term m
  go = \case
    Ref h Nothing _ | h == target -> closedIn replacement
    t -> mapChildren go t

-- Renaming and weakening ------------------------------------------------------

{- | Apply a renaming of free variables, lifting it under binders, in an
applicative: weakening moves a term under new binders it does not
mention, and strengthening, which can fail, moves it out from under one.
-}
renameTermA :: (Applicative f) => (Fin n -> f (Fin m)) -> Term n -> f (Term m)
renameTermA f =
  traverseChildren (fmap Var . f) (\hs -> renameTermA (liftFinBy hs f))

renameTerm :: (Fin n -> Fin m) -> Term n -> Term m
renameTerm f = runIdentity . renameTermA (Identity . f)

liftFin ::
  (Applicative f) => (Fin n -> f (Fin m)) -> Fin (S n) -> f (Fin (S m))
liftFin f = \case
  FZ -> pure FZ
  FS i -> FS <$> f i

liftFinBy ::
  (Applicative f) =>
  Vec k a ->
  (Fin n -> f (Fin m)) ->
  Fin (Plus k n) ->
  f (Fin (Plus k m))
liftFinBy ks f = case ks of
  VNil -> f
  VCons _ rest -> liftFin (liftFinBy rest f)

{- | A term moved out from under its innermost binder, when it does not
mention it: the inverse of weakening by one.
-}
strengthen :: Term (S n) -> Maybe (Term n)
strengthen = renameTermA (\case FZ -> Nothing; FS i -> Just i)

-- | Move a term under @k@ new innermost binders it does not mention.
weakenBy :: Vec k a -> Term n -> Term (Plus k n)
weakenBy ks = renameTerm (shiftFin ks)
 where
  shiftFin :: Vec j a -> Fin n -> Fin (Plus j n)
  shiftFin js i = case js of
    VNil -> i
    VCons _ rest -> FS (shiftFin rest i)

-- | A closed term is a term in any scope: it has no variables to rename.
closedIn :: Term Z -> Term n
closedIn = renameTerm (\case {})

-- Hash display ----------------------------------------------------------------------

{- | A short, human-facing form: @#@ followed by the first five base32hex
characters of the digest.
-}
showHash :: Hash -> Text
showHash h = "#" <> T.take 5 (base32hex h)

-- | An unabridged reference, for resolving ambiguous short prefixes.
showFullHash :: Hash -> Text
showFullHash h = "#" <> base32hex h

{- | Whether a hash's base32hex form starts with the given text (with or
without the leading @#@).
-}
hashHasPrefix :: Text -> Hash -> Bool
hashHasPrefix prefix h = T.dropWhile (== '#') prefix `T.isPrefixOf` base32hex h

-- | RFC 4648 base32hex without padding.
base32hex :: Hash -> Text
base32hex (Hash bs) = T.pack (go (BS.unpack bs))
 where
  alphabet = "0123456789abcdefghijklmnopqrstuv"
  go [] = []
  go chunkBytes =
    let (chunk, rest) = splitAt 5 chunkBytes
        n = length chunk
        bits =
          foldl (\acc b -> (acc `shiftL` 8) .|. fromIntegral b) (0 :: Integer) chunk
            `shiftL` (8 * (5 - n))
        chars = (n * 8 + 4) `div` 5
        digits =
          [ alphabet !! fromIntegral ((bits `shiftR` (40 - 5 * (i + 1))) .&. 31)
          | i <- [0 .. chars - 1]
          ]
     in digits ++ go rest
