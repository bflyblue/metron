{-# LANGUAGE TypeFamilies #-}

-- | Core: the desugared, untyped, well-scoped term language (design §5.1).
--
-- Core is an abstract binding tree with de Bruijn indices, indexed by the
-- number of variables in scope: a @Term n@ may mention variables @0 .. n-1@
-- and nothing else, so a dangling variable is a Haskell type error. Binders
-- carry a 'Hint', the name the user wrote, for printing only: 'alphaEq' and
-- hashing ignore hints.
--
-- Primitives are saturated: @PrimApp p args@ always carries exactly
-- 'primArity' arguments. Partial uses are eta-expanded by the desugarer.
module Eval.Core
  ( -- * Type-level naturals and scope-safe indices
    Nat (..)
  , Fin (..)
  , finToInt
  , Vec (..)
  , SomeVec (..)
  , vecFromList
  , vecToList
  , vecLength
  , vecMap
  , vecTraverse
  , vecIndex
  , vecAppend
  , Plus

    -- * Terms
  , Hash (..)
  , Hint (..)
  , NudgeKind (..)
  , Lit (..)
  , Term (..)
  , alphaEq
  , refs
  , refsWithIndex
  , rewriteRefs
  , primArity
  ) where

import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)

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

-- | A content hash of a Core term (design §6): the bytes of a SHA-256 digest.
-- Defined here so that 'Term' can refer to other terms; hashing itself lives
-- in "Eval.Hash".
newtype Hash = Hash ByteString
  deriving stock (Eq, Ord, Show)

-- | A name hint on a binder. Ignored by 'alphaEq' and by hashing.
newtype Hint = Hint Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString)

-- | The kind of a nudge (design §3.2): a rigorous bound, or a 1σ standard
-- uncertainty.
data NudgeKind = Bound | Stat
  deriving stock (Eq, Ord, Show)

-- | A constant. A tensor literal carries its shape and its values flat in
-- row-major order; a number is the rank-zero case. The boolean alternative is
-- the last special-cased constant (core.md §5).
data Lit
  = LTensor [Int] [Rational]
  | LBool Bool
  deriving stock (Eq, Ord, Show)

-- | Core terms in a scope of @n@ variables. @Var FZ@ is the innermost
-- binder. 'Lam' and 'Let' bind one variable in their body. 'Cycle' binds
-- @k@ variables in every body: inside body @i@, index @j < k@ (at depth 0) is
-- member @j@.
data Term (n :: Nat) where
  Var :: Fin n -> Term n
  -- | Another definition by content hash, with a cycle index when the
  -- referenced term is a 'Cycle'.
  Ref :: Hash -> Maybe Int -> Term n
  -- | A saturated primitive application: exactly 'primArity' arguments.
  -- Overloading is unresolved here: @PrimApp "add"@ is the overloaded
  -- addition.
  PrimApp :: Text -> [Term n] -> Term n
  Lit :: Lit -> Term n
  Lam :: Hint -> Term (S n) -> Term n
  App :: Term n -> Term n -> Term n
  -- | Non-recursive, generalising local binding: @Let h e b@ binds @e@ in @b@.
  Let :: Hint -> Term n -> Term (S n) -> Term n
  -- | Lazy in both branches.
  If :: Term n -> Term n -> Term n -> Term n
  -- | @e ^ n@ with a literal integer exponent.
  Pow :: Term n -> Integer -> Term n
  -- | @noise n@ or @gauss n@: @n@ fresh unit nudges as a dimensionless vector.
  Noise :: NudgeKind -> Integer -> Term n
  -- | @x ± err@ or @x ±σ err@.
  Uncertain :: NudgeKind -> Term n -> Term n -> Term n
  -- | @[a, b, c]@: stack @k@ tensors of shape @s@ into one of shape @k : s@.
  -- A literal whose elements are all constants is folded into 'Lit' by the
  -- desugarer, so the two never describe the same value.
  Pack :: [Term n] -> Term n
  -- | @v.i@ or @m.i@: component or row at a literal position. The position
  -- is checked against the length statically (design §4.1).
  Proj :: Term n -> Int -> Term n
  -- | @k@ mutually recursive bodies, each in scope of the @k@ members.
  Cycle :: Vec k Hint -> Vec k (Term (Plus k n)) -> Term n

deriving stock instance Show (Term n)

-- | Alpha-equivalence: structural equality ignoring hints. Because variables
-- are de Bruijn indices this is a plain structural walk. The scopes may
-- differ in type; only the indices are compared.
alphaEq :: Term n -> Term m -> Bool
alphaEq = go
  where
    go :: Term a -> Term b -> Bool
    go (Var i) (Var j) = finToInt i == finToInt j
    go (Ref h i) (Ref h' i') = h == h' && i == i'
    go (PrimApp p as) (PrimApp q bs) = p == q && goList as bs
    go (Lit l) (Lit l') = l == l'
    go (Lam _ b) (Lam _ b') = go b b'
    go (App f a) (App g b) = go f g && go a b
    go (Let _ e b) (Let _ e' b') = go e e' && go b b'
    go (If c t e) (If c' t' e') = go c c' && go t t' && go e e'
    go (Pow t n) (Pow t' n') = n == n' && go t t'
    go (Noise k n) (Noise k' n') = k == k' && n == n'
    go (Uncertain k x e) (Uncertain k' x' e') = k == k' && go x x' && go e e'
    go (Pack as) (Pack bs) = goList as bs
    go (Proj t i) (Proj t' i') = i == i' && go t t'
    go (Cycle _ bs) (Cycle _ bs') = goList (vecToList bs) (vecToList bs')
    go _ _ = False

    goList :: [Term a] -> [Term b] -> Bool
    goList as bs = length as == length bs && and (zipWith go as bs)

-- | The hashes a term refers to.
refs :: Term n -> Set Hash
refs = \case
  Var _ -> Set.empty
  Ref h _ -> Set.singleton h
  PrimApp _ as -> foldMap refs as
  Lit _ -> Set.empty
  Lam _ b -> refs b
  App f a -> refs f <> refs a
  Let _ e b -> refs e <> refs b
  If c t e -> refs c <> refs t <> refs e
  Pow t _ -> refs t
  Noise _ _ -> Set.empty
  Uncertain _ x e -> refs x <> refs e
  Pack ts -> foldMap refs ts
  Proj t _ -> refs t
  Cycle _ bs -> foldMap refs (vecToList bs)

-- | The references a term makes, with their cycle indices.
refsWithIndex :: Term n -> Set (Hash, Maybe Int)
refsWithIndex = \case
  Var _ -> Set.empty
  Ref h i -> Set.singleton (h, i)
  PrimApp _ as -> foldMap refsWithIndex as
  Lit _ -> Set.empty
  Lam _ b -> refsWithIndex b
  App f a -> refsWithIndex f <> refsWithIndex a
  Let _ e b -> refsWithIndex e <> refsWithIndex b
  If c t e -> refsWithIndex c <> refsWithIndex t <> refsWithIndex e
  Pow t _ -> refsWithIndex t
  Noise _ _ -> Set.empty
  Uncertain _ x e -> refsWithIndex x <> refsWithIndex e
  Pack ts -> foldMap refsWithIndex ts
  Proj t _ -> refsWithIndex t
  Cycle _ bs -> foldMap refsWithIndex (vecToList bs)

-- | Replace references according to a function; 'Nothing' keeps a reference
-- as it is. Used to upgrade dependents to a new version (design §7.5).
rewriteRefs :: (Hash -> Maybe Int -> Maybe (Hash, Maybe Int)) -> Term n -> Term n
rewriteRefs f = go
  where
    go :: Term m -> Term m
    go = \case
      Var i -> Var i
      Ref h i -> maybe (Ref h i) (uncurry Ref) (f h i)
      PrimApp p as -> PrimApp p (map go as)
      Lit l -> Lit l
      Lam h b -> Lam h (go b)
      App a b -> App (go a) (go b)
      Let h e b -> Let h (go e) (go b)
      If c t e -> If (go c) (go t) (go e)
      Pow t n -> Pow (go t) n
      Noise k n -> Noise k n
      Uncertain k x e -> Uncertain k (go x) (go e)
      Pack ts -> Pack (map go ts)
      Proj t i -> Proj (go t) i
      Cycle hs bs -> Cycle hs (vecMap go bs)

-- | The number of arguments each primitive takes. The desugarer uses this to
-- eta-expand partial applications; the evaluator and type checker rely on
-- 'PrimApp' nodes being saturated.
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
  "cross" -> Just 2
  "norm" -> Just 1
  "transpose" -> Just 1
  "inverse" -> Just 1
  "det" -> Just 1
  "vmap" -> Just 2
  "pi" -> Just 0
  -- The seven SI base units (design §3.2.11).
  "m" -> Just 0
  "kg" -> Just 0
  "s" -> Just 0
  "A" -> Just 0
  "K" -> Just 0
  "mol" -> Just 0
  "cd" -> Just 0
  _ -> Nothing
