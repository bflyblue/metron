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
module Eval.Core (
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
  vecTraverse,
  vecIndex,
  vecAppend,
  Plus,

  -- * Terms
  Hash (..),
  showHash,
  hashHasPrefix,
  Hint (..),
  NudgeKind (..),
  Label (..),
  renderLabel,
  Lit (..),
  Term (..),
  Alt (..),
  ConRef (..),
  weakenBy,
  alphaEq,
  refs,
  conTypes,
  refsWithIndex,
  rewriteRefs,
  rewriteRefsWritten,
  refsWritten,
  inlineRef,
  primArity,
) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T

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
in "Eval.Hash".
-}
newtype Hash = Hash ByteString
  deriving stock (Eq, Ord, Show)

-- | A name hint on a binder. Ignored by 'alphaEq' and by hashing.
newtype Hint = Hint Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString)

{- | The kind of a nudge (design §3.2): a rigorous bound, or a 1σ standard
uncertainty.
-}
data NudgeKind = Bound | Stat
  deriving stock (Eq, Ord, Show)

{- | Who a declared uncertainty belongs to (design §3.2.4). The desugarer
stamps every @±@, @ and @ with the name of the definition it is
written in, so two definitions with identical bodies are different terms
and therefore different measurements; the nudge's identity is still the
definition hash and the path. A @#label@ written by the user is a global
identity instead: every @±@ with that label and midpoint is one unknown,
wherever it appears. Only a tag is printed; the owner stamp is implied by
the binding.

The third kind stamps the axis type a chart declaration mints (design
§3.9, decision 1) with the chart's full path: no source @data@ and no
uncertainty carries it, so a user's @data Eci = Eci@ never equals it.
-}
data Label
  = Owner Text
  | Tag Text
  | Axes Text
  deriving stock (Eq, Ord, Show)

renderLabel :: Label -> Text
renderLabel = \case
  Owner _ -> ""
  Tag t -> " #" <> t
  Axes _ -> ""

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
  -- | @noise n@ or @gauss n@: @n@ fresh unit nudges as a dimensionless vector.
  Noise :: NudgeKind -> Label -> Integer -> Term n
  -- | @x ± err@ or @x ±σ err@, with its owner or tag.
  Uncertain :: NudgeKind -> Label -> Term n -> Term n -> Term n
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
("Eval.Builtin"), so there are no others.
-}
data ConRef = UserCon Hash Int
  deriving stock (Eq, Ord, Show)

-- | An alternative of a 'Case': constructor, field hints, body in scope of the fields.
data Alt n = forall k. Alt ConRef (Vec k Hint) (Term (Plus k n))

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
  go (Noise k l n) (Noise k' l' n') = k == k' && l == l' && n == n'
  go (Uncertain k l x e) (Uncertain k' l' x' e') = k == k' && l == l' && go x x' && go e e'
  go (Pack as) (Pack bs) = goList as bs
  go (Proj t i) (Proj t' i') = i == i' && go t t'
  go (Cycle _ bs) (Cycle _ bs') = goList (vecToList bs) (vecToList bs')
  go _ _ = False

  goList :: [Term a] -> [Term b] -> Bool
  goList as bs = length as == length bs && and (zipWith go as bs)
  goAlt :: Alt a -> Alt b -> Bool
  goAlt (Alt c hs b) (Alt c' hs' b') = c == c' && vecLength hs == vecLength hs' && go b b'

-- | The hashes a term refers to.
refs :: Term n -> Set Hash
refs = \case
  Var _ -> Set.empty
  Ref h _ _ -> Set.singleton h
  PrimApp _ as -> foldMap refs as
  Lit _ -> Set.empty
  Lam _ b -> refs b
  App f a -> refs f <> refs a
  Let _ e b -> refs e <> refs b
  Con _ as -> foldMap refs as
  Case s alts -> refs s <> foldMap (\(Alt _ _ b) -> refs b) alts
  Pow t _ -> refs t
  Noise{} -> Set.empty
  Uncertain _ _ x e -> refs x <> refs e
  Pack ts -> foldMap refs ts
  Proj t _ -> refs t
  Cycle _ bs -> foldMap refs (vecToList bs)

-- | The declared types whose constructors a term builds or matches.
conTypes :: Term n -> Set Hash
conTypes = \case
  Con c as -> conType c <> foldMap conTypes as
  Case s alts -> conTypes s <> foldMap (\(Alt c _ b) -> conType c <> conTypes b) alts
  PrimApp _ as -> foldMap conTypes as
  Lam _ b -> conTypes b
  App a b -> conTypes a <> conTypes b
  Let _ e b -> conTypes e <> conTypes b
  Pow t _ -> conTypes t
  Uncertain _ _ x e -> conTypes x <> conTypes e
  Pack ts -> foldMap conTypes ts
  Proj t _ -> conTypes t
  Cycle _ bs -> foldMap conTypes (vecToList bs)
  Var _ -> Set.empty
  Ref{} -> Set.empty
  Lit _ -> Set.empty
  Noise{} -> Set.empty
 where
  conType = \case
    UserCon h _ -> Set.singleton h

-- | The references a term makes, with their cycle indices.
refsWithIndex :: Term n -> Set (Hash, Maybe Int)
refsWithIndex = \case
  Var _ -> Set.empty
  Ref h i _ -> Set.singleton (h, i)
  PrimApp _ as -> foldMap refsWithIndex as
  Lit _ -> Set.empty
  Lam _ b -> refsWithIndex b
  App f a -> refsWithIndex f <> refsWithIndex a
  Let _ e b -> refsWithIndex e <> refsWithIndex b
  Con _ as -> foldMap refsWithIndex as
  Case s alts -> refsWithIndex s <> foldMap (\(Alt _ _ b) -> refsWithIndex b) alts
  Pow t _ -> refsWithIndex t
  Noise{} -> Set.empty
  Uncertain _ _ x e -> refsWithIndex x <> refsWithIndex e
  Pack ts -> foldMap refsWithIndex ts
  Proj t _ -> refsWithIndex t
  Cycle _ bs -> foldMap refsWithIndex (vecToList bs)

{- | Replace references according to a function; 'Nothing' keeps a reference
as it is. Used to upgrade dependents to a new version (design §7.5).
-}
rewriteRefs ::
  (Hash -> Maybe Int -> Maybe (Hash, Maybe Int)) -> Term n -> Term n
rewriteRefs f = go
 where
  go :: Term m -> Term m
  go = \case
    Var i -> Var i
    Ref h i hint -> maybe (Ref h i hint) (\(h', i') -> Ref h' i' hint) (f h i)
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam h b -> Lam h (go b)
    App a b -> App (go a) (go b)
    Let h e b -> Let h (go e) (go b)
    Con c as -> Con c (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt c hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k l n
    Uncertain k l x e -> Uncertain k l (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle hs (vecMap go bs)

{- | The number of arguments each primitive takes. The desugarer uses this to
eta-expand partial applications; the evaluator and type checker rely on
'PrimApp' nodes being saturated.
-}
primArity :: Text -> Maybe Int
primArity = \case
  "add" -> Just 2
  "sub" -> Just 2
  "outer" -> Just 2
  "emul" -> Just 2
  "ediv" -> Just 2
  "div" -> Just 2
  "eq" -> Just 2
  "ne" -> Just 2
  "lt" -> Just 2
  "le" -> Just 2
  "gt" -> Just 2
  "ge" -> Just 2
  "and" -> Just 2
  "or" -> Just 2
  "neg" -> Just 1
  "not" -> Just 1
  "abs" -> Just 1
  "floor" -> Just 1
  "ceil" -> Just 1
  "round" -> Just 1
  -- Known to the desugarer and type checker now; implemented in the
  -- evaluator with affine arithmetic and linear algebra (roadmap 3 and 4).
  "sqrt" -> Just 1
  "sin" -> Just 1
  "cos" -> Just 1
  "tan" -> Just 1
  "asin" -> Just 1
  "acos" -> Just 1
  "atan" -> Just 1
  "sinh" -> Just 1
  "cosh" -> Just 1
  "tanh" -> Just 1
  "exp" -> Just 1
  "log" -> Just 1
  "atan2" -> Just 2
  "to" -> Just 2
  "dot" -> Just 2
  "wedge" -> Just 2
  "star" -> Just 1
  "norm" -> Just 1
  "transpose" -> Just 1
  -- Contraction and index permutation (design §4.2): the leading arguments
  -- are literal index positions, and the type is computed from them.
  "contract" -> Just 3
  "permute" -> Just 2
  -- A slice along axis k at position i (design §2.10): both literal.
  "slice" -> Just 3
  "inverse" -> Just 1
  "det" -> Just 1
  "vmap" -> Just 2
  "indices" -> Just 1
  "vzipWith" -> Just 3
  "timap" -> Just 2
  "pi" -> Just 0
  -- The seven SI base units (design §3.2.11).
  "m" -> Just 0
  "kg" -> Just 0
  "s" -> Just 0
  "A" -> Just 0
  "K" -> Just 0
  "mol" -> Just 0
  "cd" -> Just 0
  "rad" -> Just 0
  -- A root chart, a turned one and a spinning one take the constructor of
  -- their minted axis type first (design §3.9); a translated one does not.
  "mkScale" -> Just 3
  "mkChart3" -> Just 3
  "mkChart4" -> Just 5
  -- A spinning chart (design §3.8): turned by a list of generators, perhaps
  -- empty, with its angular velocity along its own axes.
  "mkChart5" -> Just 6
  "pointOn" -> Just 2
  "pointAdd" -> Just 2
  "pointSub" -> Just 2
  "toScale" -> Just 2
  -- Units (design §3.10): the quantity rule after a unit, and a unit's
  -- declaration. Both names are keywords, so no source names them.
  "scale" -> Just 2
  "unit" -> Just 1
  "cholesky" -> Just 1
  "covariance" -> Just 1
  "crossCovariance" -> Just 2
  -- The parts of an enclosure (design §3.2.9), to write a comparison policy.
  "mid" -> Just 1
  "bound" -> Just 1
  "sd" -> Just 1
  -- Rotations (design §3.3, §3.8): the matrix exponential, a matrix
  -- applied along every axis of a tensor, and the rotation of a chart.
  "expm" -> Just 1
  "transformBy" -> Just 2
  "rotationOf" -> Just 1
  "withAxes" -> Just 2
  -- A chart's kinematics (design §3.8): its absolute angular velocity and
  -- the velocity of its origin, both along the base axes.
  "spinOf" -> Just 1
  "originVelocityOf" -> Just 1
  _ -> Nothing

-- Renaming and weakening ------------------------------------------------------

{- | Apply a renaming of free variables, lifting it under binders. The one use
is weakening: moving a term under new binders it does not mention.
-}
renameTerm :: forall n m. (Fin n -> Fin m) -> Term n -> Term m
renameTerm f = \case
  Var i -> Var (f i)
  Ref h i hint -> Ref h i hint
  PrimApp p as -> PrimApp p (map (renameTerm f) as)
  Lit l -> Lit l
  Lam h b -> Lam h (renameTerm (liftFin f) b)
  App a b -> App (renameTerm f a) (renameTerm f b)
  Let h e b -> Let h (renameTerm f e) (renameTerm (liftFin f) b)
  Con c as -> Con c (map (renameTerm f) as)
  Case s alts -> Case (renameTerm f s) (map renameAlt alts)
  Pow t k -> Pow (renameTerm f t) k
  Noise k l n -> Noise k l n
  Uncertain k l x e -> Uncertain k l (renameTerm f x) (renameTerm f e)
  Pack ts -> Pack (map (renameTerm f) ts)
  Proj t i -> Proj (renameTerm f t) i
  Cycle hs bs -> Cycle hs (vecMap (renameTerm (liftFinBy hs f)) bs)
 where
  renameAlt (Alt c hs b) = Alt c hs (renameTerm (liftFinBy hs f) b)

liftFin :: (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
liftFin f = \case
  FZ -> FZ
  FS i -> FS (f i)

liftFinBy :: Vec k a -> (Fin n -> Fin m) -> Fin (Plus k n) -> Fin (Plus k m)
liftFinBy ks f = case ks of
  VNil -> f
  VCons _ rest -> liftFin (liftFinBy rest f)

-- | Move a term under @k@ new innermost binders it does not mention.
weakenBy :: Vec k a -> Term n -> Term (Plus k n)
weakenBy ks = renameTerm (shiftFin ks)
 where
  shiftFin :: Vec j a -> Fin n -> Fin (Plus j n)
  shiftFin js i = case js of
    VNil -> i
    VCons _ rest -> FS (shiftFin rest i)

-- Hash display ----------------------------------------------------------------------

{- | A short, human-facing form: @#@ followed by the first five base32hex
characters of the digest.
-}
showHash :: Hash -> Text
showHash h = "#" <> T.take 5 (base32hex h)

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

{- | Replace every reference to a hash (with no cycle index) by a closed
term: how @it@ absorbs the expression before it, so that @:view it@ shows
the whole expression rather than a reference to one that has no name.
-}
inlineRef :: Hash -> Term Z -> Term n -> Term n
inlineRef target replacement = go
 where
  go :: Term m -> Term m
  go = \case
    Var i -> Var i
    Ref h Nothing _ | h == target -> closedIn replacement
    r@Ref{} -> r
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam h b -> Lam h (go b)
    App a b -> App (go a) (go b)
    Let h e b -> Let h (go e) (go b)
    Con c as -> Con c (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt c hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k l n
    Uncertain k l x e -> Uncertain k l (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle hs (vecMap go bs)

-- | A closed term is a term in any scope: it has no variables to rename.
closedIn :: Term Z -> Term n
closedIn = renameTerm (\case {})

{- | Every reference with the name it was written under (the storage hint;
empty for a term loaded from a format-1 store). Propagation follows a
rebinding only through references written under the rebound name (design
§7.5): a user's @meter = m@ and the library's @metre = m@ are one term, but
@km = kilo * metre@ depends on @metre@, not on @meter@.
-}
refsWritten :: Term n -> Set (Hash, Maybe Int, Text)
refsWritten = \case
  Var _ -> Set.empty
  Ref h i (Hint w) -> Set.singleton (h, i, w)
  PrimApp _ as -> foldMap refsWritten as
  Lit _ -> Set.empty
  Lam _ b -> refsWritten b
  App f a -> refsWritten f <> refsWritten a
  Let _ e b -> refsWritten e <> refsWritten b
  Con _ as -> foldMap refsWritten as
  Case s alts -> refsWritten s <> foldMap (\(Alt _ _ b) -> refsWritten b) alts
  Pow t _ -> refsWritten t
  Noise{} -> Set.empty
  Uncertain _ _ x e -> refsWritten x <> refsWritten e
  Pack ts -> foldMap refsWritten ts
  Proj t _ -> refsWritten t
  Cycle _ bs -> foldMap refsWritten (vecToList bs)

-- | 'rewriteRefs' that also sees the written name, which it keeps.
rewriteRefsWritten ::
  (Hash -> Maybe Int -> Text -> Maybe (Hash, Maybe Int)) -> Term n -> Term n
rewriteRefsWritten f = go
 where
  go :: Term m -> Term m
  go = \case
    Var i -> Var i
    Ref h i hint@(Hint w) -> maybe (Ref h i hint) (\(h', i') -> Ref h' i' hint) (f h i w)
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam h b -> Lam h (go b)
    App a b -> App (go a) (go b)
    Let h e b -> Let h (go e) (go b)
    Con c as -> Con c (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt c hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k l n
    Uncertain k l x e -> Uncertain k l (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle hs (vecMap go bs)
