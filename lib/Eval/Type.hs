{- | Types, kinds and schemes (design §4.1).

There is one namespace of variables, each with a 'Kind'. Every kind is an
index domain with its own equational theory: types unify syntactically,
lengths by the offset rule, shapes element-wise, dimensions by Kennedy's
algorithm. No term ever appears in a type, which keeps this on the
indexed-types side of the line.
-}
module Eval.Type (
  Kind (..),
  VarId,
  Type (..),
  dataConstructors,
  Len (..),
  Shape (..),
  Arg (..),
  Scheme (..),
  Subst,
  emptySubst,
  applyType,
  applyLen,
  applyShape,
  applyDim,
  applyArg,
  applyScheme,
  substOnce,
  freeVars,
  numT,
  numD,
  vecT,
  vecD,
  shapeOfDims,
  renderType,
  renderScheme,
  renderTypeIds,
  renderSchemeIds,
  renderArg,
) where

import Data.List (nubBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Dimension

data Kind = KType | KLen | KShape | KDim
  deriving stock (Eq, Ord, Show)

type VarId = Int

data Type
  = TBool
  | TTensor Shape Dim
  | -- | a point of the affine space over  d@ (design §3.6)
    TPoint Shape Dim
  | -- | a scale for writing and printing points (design §3.6)
    TScale Shape Dim
  | -- | a tuple of two or more components (design §2.3)
    TTuple [Type]
  | -- | a list
    TList Type
  | TFun Type Type
  | TVar VarId
  deriving stock (Eq, Ord, Show)

{- | A literal length, or a length variable plus a literal offset: @n + k@
means "at least @k@ long" (design §4.1).
-}
data Len
  = LLit Int
  | LVar VarId Int
  deriving stock (Eq, Ord, Show)

-- | A list of lengths, possibly ending in a shape variable.
data Shape
  = SNil
  | SCons Len Shape
  | SVar VarId
  deriving stock (Eq, Ord, Show)

-- | What a kinded variable stands for.
data Arg
  = AType Type
  | ALen Len
  | AShape Shape
  | ADim Dim
  deriving stock (Eq, Ord, Show)

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
vecT n = TTensor (SCons n SNil) dimOne

vecD :: Len -> Dim -> Type
vecD n = TTensor (SCons n SNil)

shapeOfDims :: [Int] -> Shape
shapeOfDims = foldr (SCons . LLit) SNil

-- Substitution -------------------------------------------------------------------

applyType :: Subst -> Type -> Type
applyType s = \case
  TBool -> TBool
  TTensor sh d -> TTensor (applyShape s sh) (applyDim s d)
  TPoint sh d -> TPoint (applyShape s sh) (applyDim s d)
  TScale sh d -> TScale (applyShape s sh) (applyDim s d)
  TTuple ts -> TTuple (map (applyType s) ts)
  TList t -> TList (applyType s t)
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

shiftLen :: Int -> Len -> Len
shiftLen k = \case
  LLit j -> LLit (j + k)
  LVar w j -> LVar w (j + k)

applyShape :: Subst -> Shape -> Shape
applyShape s = \case
  SNil -> SNil
  SCons l sh -> SCons (applyLen s l) (applyShape s sh)
  SVar v -> case Map.lookup v s of
    Just (AShape sh) -> applyShape s sh
    _ -> SVar v

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
    TBool -> TBool
    TTensor sh d -> TTensor (shape sh) (dim d)
    TPoint sh d -> TPoint (shape sh) (dim d)
    TScale sh d -> TScale (shape sh) (dim d)
    TTuple ts -> TTuple (map go ts)
    TList t -> TList (go t)
    TFun a b -> TFun (go a) (go b)
    TVar v -> case Map.lookup v m of
      Just (AType t) -> t
      _ -> TVar v
  shape = \case
    SNil -> SNil
    SCons l sh -> SCons (len l) (shape sh)
    SVar v -> case Map.lookup v m of
      Just (AShape sh) -> sh
      _ -> SVar v
  len = \case
    LLit k -> LLit k
    LVar v k -> case Map.lookup v m of
      Just (ALen l) -> shiftLen k l
      _ -> LVar v k
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
    TBool -> []
    TTensor sh d -> shape sh ++ [(v, KDim) | v <- dimVars d]
    TPoint sh d -> shape sh ++ [(v, KDim) | v <- dimVars d]
    TScale sh d -> shape sh ++ [(v, KDim) | v <- dimVars d]
    TTuple ts -> concatMap go ts
    TList t -> go t
    TFun a b -> go a ++ go b
    TVar v -> [(v, KType)]
  shape = \case
    SNil -> []
    SCons l sh -> len l ++ shape sh
    SVar v -> [(v, KShape)]
  len = \case
    LLit _ -> []
    LVar v _ -> [(v, KLen)]

-- Rendering ---------------------------------------------------------------------

{- | Print a type with variables named by kind in order of appearance: @a b c@
for types, @n m k@ for lengths, @s s1 s2@ for shapes, @d d1 d2@ for
dimensions (design §4.5). Rank zero, one and two tensors print as @Num@,
@Vec@ and @Mat@; a dimension follows in brackets unless it is @1@.
-}
renderType :: Type -> Text
renderType t = renderWith (prettyNames (freeVars t)) 0 t

renderScheme :: Scheme -> Text
renderScheme (Forall _ t) = renderType t

{- | Print naming variables by their ids (@t0@, @n1@, @s2@, @d3@), so that
binders and uses in Typed Core line up (design §5.3).
-}
renderTypeIds :: Type -> Text
renderTypeIds t = renderWith (idNames (freeVars t)) 0 t

renderSchemeIds :: Scheme -> Text
renderSchemeIds (Forall _ t) = renderTypeIds t

renderArg :: Arg -> Text
renderArg = \case
  AType t -> renderTypeIds t
  ALen l -> renderLen (idNames [(v, KLen) | LVar v _ <- [l]]) l
  AShape sh -> renderShapeList (idNames (shapeVars sh)) sh
  ADim d -> renderDimWith (\v -> "d" <> T.pack (show v)) d
 where
  shapeVars = \case
    SNil -> []
    SCons (LVar v _) rest -> (v, KLen) : shapeVars rest
    SCons _ rest -> shapeVars rest
    SVar v -> [(v, KShape)]

renderWith :: Map VarId Text -> Int -> Type -> Text
renderWith names prec = \case
  TBool -> "Bool"
  TTensor sh d -> tensor sh <> dim d
  -- A scalar point is `Point [K]`; a point over a vector space, `Point (Vec 3 [m])`.
  TPoint SNil d -> "Point" <> dim d
  TPoint sh d -> "Point (" <> tensor sh <> dim d <> ")"
  TScale SNil d -> "Scale" <> dim d
  TScale sh d -> "Scale (" <> tensor sh <> dim d <> ")"
  TTuple ts -> "(" <> T.intercalate ", " (map (renderWith names 0) ts) <> ")"
  TList t -> "{" <> renderWith names 0 t <> "}"
  TFun a b -> paren (prec > 0) (renderWith names 1 a <> " -> " <> renderWith names 0 b)
  TVar v -> Map.findWithDefault ("t" <> T.pack (show v)) v names
 where
  paren b s = if b then "(" <> s <> ")" else s
  tensor = \case
    SNil -> "Num"
    SCons n SNil -> "Vec " <> renderLen names n
    SCons m (SCons n SNil) -> "Mat " <> renderLen names m <> " " <> renderLen names n
    sh -> "Tensor " <> renderShapeList names sh
  -- A lone dimension variable prints bare (@Num d@); anything else in
  -- brackets (@Num [m s^-2]@, @Num [d d1]@).
  dim d
    | isDimOne d = ""
    | [(DVar v, 1)] <- dimAtoms d = " " <> dimName v
    | otherwise = " " <> renderDimWith dimName d
  dimName v = Map.findWithDefault ("d" <> T.pack (show v)) v names

-- | A length on its own: an offset form is parenthesised, @Vec (n + 1)@.
renderLen :: Map VarId Text -> Len -> Text
renderLen names = \case
  l@(LVar _ k) | k /= 0 -> "(" <> renderLenBare names l <> ")"
  l -> renderLenBare names l

-- | A length inside a list or a cons chain, where no parentheses are needed.
renderLenBare :: Map VarId Text -> Len -> Text
renderLenBare names = \case
  LLit k -> T.pack (show k)
  LVar v 0 -> name v
  LVar v k -> name v <> " + " <> T.pack (show k)
 where
  name v = Map.findWithDefault ("n" <> T.pack (show v)) v names

-- | @[2, 3]@ for a closed shape, @(n + 1 : s)@ when it ends in a variable.
renderShapeList :: Map VarId Text -> Shape -> Text
renderShapeList names sh = case (tailVar sh, lens sh) of
  (Nothing, ls) -> "[" <> T.intercalate ", " (map (renderLenBare names) ls) <> "]"
  (Just v, []) -> shapeName v
  (Just v, ls) ->
    "("
      <> T.intercalate " : " (map (renderLenBare names) ls ++ [shapeName v])
      <> ")"
 where
  lens = \case
    SNil -> []
    SCons l rest -> l : lens rest
    SVar _ -> []
  tailVar = \case
    SNil -> Nothing
    SCons _ rest -> tailVar rest
    SVar v -> Just v
  shapeName v = Map.findWithDefault ("s" <> T.pack (show v)) v names

prettyNames :: [(VarId, Kind)] -> Map VarId Text
prettyNames vs =
  Map.fromList
    $ zip
      [v | (v, KType) <- vs]
      (map T.singleton ['a' .. 'm'] ++ ["t" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip
        [v | (v, KLen) <- vs]
        (["n", "m", "k", "l", "p", "q"] ++ ["n" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip
        [v | (v, KShape) <- vs]
        ("s" : ["s" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip [v | (v, KDim) <- vs] ("d" : ["d" <> T.pack (show i) | i <- [1 :: Int ..]])

idNames :: [(VarId, Kind)] -> Map VarId Text
idNames vs = Map.fromList [(v, prefix k <> T.pack (show v)) | (v, k) <- vs]
 where
  prefix = \case
    KType -> "t"
    KLen -> "n"
    KShape -> "s"
    KDim -> "d"

-- Data ----------------------------------------------------------------------------

{- | The constructors of a data type with their field types, in canonical
(declaration) order: the one table 'Con' and 'Case' are checked against
(design §5.1).
-}
dataConstructors :: Type -> Maybe [(Text, [Type])]
dataConstructors = \case
  TBool -> Just [("False", []), ("True", [])]
  TTuple ts -> Just [("Tuple", ts)]
  TList t -> Just [("Nil", []), ("Cons", [t, TList t])]
  _ -> Nothing
