{- | The type language's data (design §4.1): kinds, types, lengths, shapes,
schemes, substitution, and declared data types. "Eval.Type" re-exports all
of it with the renderers and the constructor tables; this module sits
below "Eval.Encode" and "Eval.Builtin", which hash declarations, so that
"Eval.Type" can know the built-in types by their hashes.
-}
module Eval.Type.Base (
  Kind (..),
  VarId,
  Type (..),
  TypeDef (..),
  TypeLookup (..),
  selfType,
  structuralLabel,
  Len (..),
  rankLen,
  Axis (..),
  Shape (..),
  Arg (..),
  varArg,
  Scheme (..),
  Subst,
  emptySubst,
  applyType,
  applyLen,
  applyShape,
  applyDim,
  applyAxis,
  applyArg,
  applyScheme,
  substOnce,
  freeVars,
  numT,
  numD,
  vecT,
  vecD,
  shapeOfDims,
) where

import Data.ByteString qualified as BS
import Data.List (nubBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Eval.Core (Hash (..), Label (..))
import Eval.Dimension

{- | The kinds of variables. 'KAxis' is the kind of the name slot of a
shape position (design §3.9, §4.1): an axis variable.
-}
data Kind = KType | KLen | KShape | KDim | KAxis
  deriving stock (Eq, Ord, Show)

type VarId = Int

data Type
  = TTensor Shape Dim
  | -- | a point of the affine space over  d@ (design §3.6)
    TPoint Shape Dim
  | {- | a chart for writing and printing points (design §3.6, §3.8): its
    shape, along its own axes, and dimension, and the name slot of its
    root's axes (design §3.9), along which its points lie and its
    rotation's rows are: named for a chart a declaration made, anonymous
    for a scalar chart and a written one without a root, printed after a
    vector chart's type, @Chart (Vec lvlh [m]) eci@
    -}
    TScale Shape Axis Dim
  | -- | a declared data type applied to its parameters (design §2.3); a definition refers to itself as 'selfType'. @Bool@, tuples and lists are declared types too, on the hashes of "Eval.Builtin".
    TData Hash [Arg]
  | TFun Type Type
  | TVar VarId
  deriving stock (Eq, Ord, Show)

{- | A literal length, or a length variable plus a literal offset: @n + k@
means "at least @k@ long" (design §4.1); or the rank of a shape variable
plus a literal offset, @rank s + k@, the one type-level function. It is
kept in normal form by 'rankLen', so it only ever names a shape variable
that is not bound.
-}
data Len
  = LLit Int
  | LVar VarId Int
  | LRank VarId Int
  deriving stock (Eq, Ord, Show)

{- | The rank of a shape as a length, normalised: @rank [] = 0@, @rank (l :
s) = rank s + 1@, and the rank of a shape variable stays a residual.
-}
rankLen :: Shape -> Len
rankLen = go 0
 where
  go k = \case
    SNil -> LLit k
    SCons _ _ rest -> go (k + 1) rest
    SVar v -> LRank v k

{- | The name slot of a shape position (design §3.9): an axis set is a
length and a name. Anonymous axes are what a literal length means
(@Vec 3@); a named set is a static name, the hash of what declares it;
an axis variable, of kind 'KAxis', stands for either. The slot unifies
syntactically: anonymous with anonymous, a name with itself, a variable
with anything.
-}
data Axis
  = AAnon
  | ANamed Hash
  | AVar VarId
  deriving stock (Eq, Ord, Show)

{- | A list of positions, each a length and the name slot of its axes,
possibly ending in a shape variable.
-}
data Shape
  = SNil
  | SCons Len Axis Shape
  | SVar VarId
  deriving stock (Eq, Ord, Show)

-- | What a kinded variable stands for.
data Arg
  = AType Type
  | ALen Len
  | AShape Shape
  | ADim Dim
  | AAxis Axis
  deriving stock (Eq, Ord, Show)

-- | A variable of a kind, as an argument.
varArg :: Kind -> VarId -> Arg
varArg k v = case k of
  KType -> AType (TVar v)
  KLen -> ALen (LVar v 0)
  KShape -> AShape (SVar v)
  KDim -> ADim (dimVar v)
  KAxis -> AAxis (AVar v)

-- | @forall (v : kind)…. type@.
data Scheme = Forall [(VarId, Kind)] Type
  deriving stock (Eq, Ord, Show)

type Subst = Map VarId Arg

emptySubst :: Subst
emptySubst = Map.empty

-- | A dimensionless number.
numT :: Type
numT = TTensor SNil dimOne

numD :: Dim -> Type
numD = TTensor SNil

vecT :: Len -> Type
vecT n = TTensor (SCons n AAnon SNil) dimOne

vecD :: Len -> Dim -> Type
vecD n = TTensor (SCons n AAnon SNil)

-- | A closed shape of literal lengths, anonymous axes: what a literal has.
shapeOfDims :: [Int] -> Shape
shapeOfDims = foldr (\k -> SCons (LLit k) AAnon) SNil

-- Substitution -------------------------------------------------------------------

applyType :: Subst -> Type -> Type
applyType s = \case
  TTensor sh d -> TTensor (applyShape s sh) (applyDim s d)
  TPoint sh d -> TPoint (applyShape s sh) (applyDim s d)
  TScale sh r d -> TScale (applyShape s sh) (applyAxis s r) (applyDim s d)
  TData h as -> TData h (map (applyArg s) as)
  TFun a b -> TFun (applyType s a) (applyType s b)
  TVar v -> case Map.lookup v s of
    Just (AType t) -> applyType s t
    _ -> TVar v

applyLen :: Subst -> Len -> Len
applyLen s = \case
  LLit k -> LLit k
  LVar v k -> case Map.lookup v s of
    Just (ALen l) -> shiftLen k (applyLen s l)
    _ -> LVar v k
  -- The rank of a bound shape variable is normalised again.
  LRank v k -> case Map.lookup v s of
    Just (AShape sh) -> shiftLen k (rankLen (applyShape s sh))
    _ -> LRank v k

shiftLen :: Int -> Len -> Len
shiftLen k = \case
  LLit j -> LLit (j + k)
  LVar w j -> LVar w (j + k)
  LRank w j -> LRank w (j + k)

applyShape :: Subst -> Shape -> Shape
applyShape s = \case
  SNil -> SNil
  SCons l a sh -> SCons (applyLen s l) (applyAxis s a) (applyShape s sh)
  SVar v -> case Map.lookup v s of
    Just (AShape sh) -> applyShape s sh
    _ -> SVar v

applyAxis :: Subst -> Axis -> Axis
applyAxis s = \case
  AVar v | Just (AAxis a) <- Map.lookup v s -> applyAxis s a
  a -> a

{- | Substitute every bound dimension variable, renormalising. A binding may
itself mention variables, so iterate until no bound variable remains.
-}
applyDim :: Subst -> Dim -> Dim
applyDim s d = case [(v, bound) | v <- dimVars d, Just (ADim bound) <- [Map.lookup v s]] of
  [] -> d
  bindings -> applyDim s (foldr (\(v, bound) acc -> substDimVar v bound acc) d bindings)

applyArg :: Subst -> Arg -> Arg
applyArg s = \case
  AType t -> AType (applyType s t)
  ALen l -> ALen (applyLen s l)
  AShape sh -> AShape (applyShape s sh)
  ADim d -> ADim (applyDim s d)
  AAxis a -> AAxis (applyAxis s a)

{- | Apply to the body of a scheme; quantified variables are never in the
substitution's domain.
-}
applyScheme :: Subst -> Scheme -> Scheme
applyScheme s (Forall vs t) = Forall vs (applyType s t)

{- | A one-shot simultaneous substitution: each variable is replaced once and
the replacements are not themselves substituted into. This is what
instantiation and lint need, where the variables being replaced (a
scheme's quantified ids) and the variables in the replacements (another
inference run's ids) are different namespaces that may share numbers;
'applyType' chases bindings and would conflate them.
-}
substOnce :: Map VarId Arg -> Type -> Type
substOnce m = go
 where
  go = \case
    TTensor sh d -> TTensor (shape sh) (dim d)
    TPoint sh d -> TPoint (shape sh) (dim d)
    TScale sh r d -> TScale (shape sh) (axis r) (dim d)
    TData h as -> TData h (map arg as)
    TFun a b -> TFun (go a) (go b)
    TVar v -> case Map.lookup v m of
      Just (AType t) -> t
      _ -> TVar v
  shape = \case
    SNil -> SNil
    SCons l a sh -> SCons (len l) (axis a) (shape sh)
    SVar v -> case Map.lookup v m of
      Just (AShape sh) -> sh
      _ -> SVar v
  axis = \case
    AVar v | Just (AAxis a) <- Map.lookup v m -> a
    a -> a
  len = \case
    LLit k -> LLit k
    LVar v k -> case Map.lookup v m of
      Just (ALen l) -> shiftLen k l
      _ -> LVar v k
    LRank v k -> case Map.lookup v m of
      Just (AShape sh) -> shiftLen k (rankLen sh)
      _ -> LRank v k
  arg = \case
    AType t -> AType (go t)
    ALen l -> ALen (len l)
    AShape sh -> AShape (shape sh)
    ADim d -> ADim (dim d)
    AAxis a -> AAxis (axis a)
  dim d =
    foldr
      dimMul
      dimOne
      [ case a of
          DVar v | Just (ADim d') <- Map.lookup v m -> dimPow k d'
          _ -> dimFromAtoms [(a, k)]
      | (a, k) <- dimAtoms d
      ]

-- | Free variables with their kinds, in order of first appearance.
freeVars :: Type -> [(VarId, Kind)]
freeVars = nubBy (\a b -> fst a == fst b) . go
 where
  go = \case
    TTensor sh d -> shape sh ++ [(v, KDim) | v <- dimVars d]
    TPoint sh d -> shape sh ++ [(v, KDim) | v <- dimVars d]
    TScale sh r d -> shape sh ++ axis r ++ [(v, KDim) | v <- dimVars d]
    TData _ as -> concatMap argVars as
    TFun a b -> go a ++ go b
    TVar v -> [(v, KType)]
  shape = \case
    SNil -> []
    SCons l a sh -> len l ++ axis a ++ shape sh
    SVar v -> [(v, KShape)]
  axis = \case
    AVar v -> [(v, KAxis)]
    _ -> []
  len = \case
    LLit _ -> []
    LVar v _ -> [(v, KLen)]
    LRank v _ -> [(v, KShape)]
  argVars = \case
    AType t -> go t
    ALen l -> len l
    AShape sh -> shape sh
    ADim d -> [(v, KDim) | v <- dimVars d]
    AAxis a -> axis a

{- | A declared data type (design §2.3): its parameters by kind (variables
0 .. k-1 in the field types), its constructors' field types in declaration
order, and its owner stamp or structural label. Constructor and type names
are labels in the codebase, not part of the definition. A recursive
occurrence of the type inside its own fields is 'selfType'.
-}
data TypeDef = TypeDef
  { params :: [(VarId, Kind)]
  , constructors :: [[Type]]
  , label :: Label
  }
  deriving stock (Eq, Show)

-- | The hash a definition uses for itself inside its own fields.
selfType :: Hash
selfType = Hash (BS.replicate 32 0)

{- | What inference and lint need from the codebase: the schemes of a stored
definition, and the declaration of a data type.
-}
data TypeLookup = TypeLookup
  { schemesOf :: Hash -> Maybe [Scheme]
  , typeDefOf :: Hash -> Maybe TypeDef
  }

{- | The label of a @structural data@ declaration: no owner, so two
declarations of the same shape are one type.
-}
structuralLabel :: Label
structuralLabel = Tag ""
