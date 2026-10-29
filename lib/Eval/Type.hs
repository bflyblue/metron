-- | Types, kinds and schemes (design §4.1), without dimensions yet.
--
-- There is one namespace of variables, each with a 'Kind'. Every kind is an
-- index domain with its own equational theory: types unify syntactically,
-- lengths by the offset rule, shapes element-wise. No term ever appears in
-- a type, which keeps this on the indexed-types side of the line.
module Eval.Type
  ( Kind (..)
  , VarId
  , Type (..)
  , Len (..)
  , Shape (..)
  , Arg (..)
  , Scheme (..)
  , Subst
  , emptySubst
  , applyType
  , applyLen
  , applyShape
  , applyArg
  , applyScheme
  , freeVars
  , numT
  , vecT
  , shapeOfDims
  , renderType
  , renderScheme
  , renderTypeIds
  , renderSchemeIds
  , renderArg
  ) where

import Data.List (nubBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

data Kind = KType | KLen | KShape
  deriving stock (Eq, Ord, Show)

type VarId = Int

data Type
  = TBool
  | TTensor Shape
  | TFun Type Type
  | TVar VarId
  deriving stock (Eq, Ord, Show)

-- | A literal length, or a length variable plus a literal offset: @n + k@
-- means "at least @k@ long" (design §4.1).
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
  deriving stock (Eq, Ord, Show)

-- | @forall (v : kind)…. type@.
data Scheme = Forall [(VarId, Kind)] Type
  deriving stock (Eq, Ord, Show)

type Subst = Map VarId Arg

emptySubst :: Subst
emptySubst = Map.empty

numT :: Type
numT = TTensor SNil

vecT :: Len -> Type
vecT n = TTensor (SCons n SNil)

shapeOfDims :: [Int] -> Shape
shapeOfDims = foldr (SCons . LLit) SNil

-- Substitution -------------------------------------------------------------------

applyType :: Subst -> Type -> Type
applyType s = \case
  TBool -> TBool
  TTensor sh -> TTensor (applyShape s sh)
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

applyArg :: Subst -> Arg -> Arg
applyArg s = \case
  AType t -> AType (applyType s t)
  ALen l -> ALen (applyLen s l)
  AShape sh -> AShape (applyShape s sh)

-- | Apply to the body of a scheme; quantified variables are never in the
-- substitution's domain.
applyScheme :: Subst -> Scheme -> Scheme
applyScheme s (Forall vs t) = Forall vs (applyType s t)

-- | Free variables with their kinds, in order of first appearance.
freeVars :: Type -> [(VarId, Kind)]
freeVars = nubBy (\a b -> fst a == fst b) . go
  where
    go = \case
      TBool -> []
      TTensor sh -> shape sh
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

-- | Print a type with variables named by kind in order of appearance: @a b c@
-- for types, @n m k@ for lengths, @s s1 s2@ for shapes (design §4.5). Rank
-- zero, one and two tensors print as @Num@, @Vec@ and @Mat@.
renderType :: Type -> Text
renderType t = renderWith (prettyNames (freeVars t)) 0 t

renderScheme :: Scheme -> Text
renderScheme (Forall _ t) = renderType t

-- | Print naming variables by their ids (@t0@, @n1@, @s2@), so that binders
-- and uses in Typed Core line up (design §5.3).
renderTypeIds :: Type -> Text
renderTypeIds t = renderWith (idNames (freeVars t)) 0 t

renderSchemeIds :: Scheme -> Text
renderSchemeIds (Forall _ t) = renderTypeIds t

renderArg :: Arg -> Text
renderArg = \case
  AType t -> renderTypeIds t
  ALen l -> renderLen (idNames [(v, KLen) | LVar v _ <- [l]]) l
  AShape sh -> renderShapeList (idNames (shapeVars sh)) sh
  where
    shapeVars = \case
      SNil -> []
      SCons (LVar v _) rest -> (v, KLen) : shapeVars rest
      SCons _ rest -> shapeVars rest
      SVar v -> [(v, KShape)]

renderWith :: Map VarId Text -> Int -> Type -> Text
renderWith names prec = \case
  TBool -> "Bool"
  TTensor SNil -> "Num"
  TTensor (SCons n SNil) -> "Vec " <> renderLen names n
  TTensor (SCons m (SCons n SNil)) -> "Mat " <> renderLen names m <> " " <> renderLen names n
  TTensor sh -> "Tensor " <> renderShapeList names sh
  TFun a b -> paren (prec > 0) (renderWith names 1 a <> " -> " <> renderWith names 0 b)
  TVar v -> Map.findWithDefault ("t" <> T.pack (show v)) v names
  where
    paren b s = if b then "(" <> s <> ")" else s

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
  (Just v, ls) -> "(" <> T.intercalate " : " (map (renderLenBare names) ls ++ [shapeName v]) <> ")"
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
  Map.fromList $
    zip [v | (v, KType) <- vs] (map T.singleton ['a' .. 'm'] ++ ["t" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip [v | (v, KLen) <- vs] (["n", "m", "k", "l", "p", "q"] ++ ["n" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip [v | (v, KShape) <- vs] ("s" : ["s" <> T.pack (show i) | i <- [1 :: Int ..]])

idNames :: [(VarId, Kind)] -> Map VarId Text
idNames vs = Map.fromList [(v, prefix k <> T.pack (show v)) | (v, k) <- vs]
  where
    prefix = \case
      KType -> "t"
      KLen -> "n"
      KShape -> "s"
