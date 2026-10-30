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
  equalityArgs,
  TypeDef (..),
  TypeLookup (..),
  noLookup,
  conText,
  selfType,
  structuralLabel,
  renderTypeDef,
  Len (..),
  rankLen,
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
  renderTypeIn,
  renderSchemeIn,
  renderTypeIds,
  renderSchemeIds,
  renderSignature,
  canonicalScheme,
  renderArg,
) where

import Data.ByteString qualified as BS
import Data.List (nubBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core (ConRef (..), Hash (..), Label (..), showHash)
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
  | -- | a declared data type applied to its parameters (design §2.3); a definition refers to itself as 'selfType'
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
    SCons _ rest -> go (k + 1) rest
    SVar v -> LRank v k

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
    TData h as -> TData h (map arg as)
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
    LRank v k -> case Map.lookup v m of
      Just (AShape sh) -> shiftLen k (rankLen sh)
      _ -> LRank v k
  arg = \case
    AType t -> AType (go t)
    ALen l -> ALen (len l)
    AShape sh -> AShape (shape sh)
    ADim d -> ADim (dim d)
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
    TData _ as -> concatMap argVars as
    TFun a b -> go a ++ go b
    TVar v -> [(v, KType)]
  shape = \case
    SNil -> []
    SCons l sh -> len l ++ shape sh
    SVar v -> [(v, KShape)]
  len = \case
    LLit _ -> []
    LVar v _ -> [(v, KLen)]
    LRank v _ -> [(v, KShape)]
  argVars = \case
    AType t -> go t
    ALen l -> len l
    AShape sh -> shape sh
    ADim d -> [(v, KDim) | v <- dimVars d]

-- Rendering ---------------------------------------------------------------------

{- | Print a type with variables named by kind in order of appearance: @a b c@
for types, @n m k@ for lengths, @s s1 s2@ for shapes, @d d1 d2@ for
dimensions (design §4.5). Rank zero, one and two tensors print as @Num@,
@Vec@ and @Mat@; a dimension follows in brackets unless it is @1@.
-}
renderType :: Type -> Text
renderType = renderTypeIn Ascii

renderScheme :: Scheme -> Text
renderScheme (Forall _ t) = renderType t

-- | 'renderType' in a chosen spelling: @Num [m s⁻²] → Num [m]@ in unicode.
renderTypeIn :: Spelling -> Type -> Text
renderTypeIn spelling t = renderWith spelling (prettyNames (freeVars t)) 0 t

renderSchemeIn :: Spelling -> Scheme -> Text
renderSchemeIn spelling (Forall _ t) = renderTypeIn spelling t

{- | Print naming variables by their ids (@t0@, @n1@, @s2@, @d3@), so that
binders and uses in Typed Core line up (design §5.3).
-}
renderTypeIds :: Type -> Text
renderTypeIds t = renderWith Ascii (idNames (freeVars t)) 0 t

renderSchemeIds :: Scheme -> Text
renderSchemeIds (Forall _ t) = renderTypeIds t

{- | A signature as it is written back (design §4.8): in a spelling, with
declared types named by the given function, and with variables named by
kind as 'renderScheme' names them but skipping every name the test
rejects (one that would not read back as a variable, such as @m@ or @s@,
the metre and the second) and every name already given, so that the text
parses back to the same scheme.
-}
renderSignature ::
  Spelling -> (Text -> Bool) -> (Hash -> Text) -> Scheme -> Text
renderSignature spelling usable typeName (Forall _ t) =
  renderWithNamed typeName spelling (namesAvoiding (freeVars t)) 0 t
 where
  namesAvoiding vs = snd (foldl pick (Set.empty, Map.empty) vs)
  pick (used, acc) (v, k) =
    case [c | c <- candidates k, usable c, Set.notMember c used] of
      c : _ -> (Set.insert c used, Map.insert v c acc)
      [] -> (used, acc)
  candidates = \case
    KType -> map T.singleton ['a' .. 'z'] ++ numbered "t"
    KLen -> ["n", "m", "k", "l", "p", "q"] ++ numbered "n"
    KShape -> "s" : numbered "s"
    KDim -> "d" : numbered "d"
  numbered p = [p <> T.pack (show i) | i <- [1 :: Int ..]]

{- | A scheme with its variables renumbered from 0 in order of appearance,
so that two schemes that differ only in their variables' ids are equal.
-}
canonicalScheme :: Scheme -> Scheme
canonicalScheme (Forall _ t) =
  let vs = freeVars t
      fresh v k = case k of
        KType -> AType (TVar v)
        KLen -> ALen (LVar v 0)
        KShape -> AShape (SVar v)
        KDim -> ADim (dimVar v)
      renaming = Map.fromList [(v, fresh i k) | (i, (v, k)) <- zip [0 ..] vs]
   in Forall [(i, k) | (i, (_, k)) <- zip [0 ..] vs] (substOnce renaming t)

renderWith :: Spelling -> Map VarId Text -> Int -> Type -> Text
renderWith = renderWithNamed showHash

renderArg :: Arg -> Text
renderArg = \case
  AType t -> renderTypeIds t
  ALen l -> renderLen (idNames (lenVars l)) l
  AShape sh -> renderShapeList (idNames (shapeVars sh)) sh
  ADim d -> renderDimWith (\v -> "d" <> T.pack (show v)) d
 where
  shapeVars = \case
    SNil -> []
    SCons l rest -> lenVars l ++ shapeVars rest
    SVar v -> [(v, KShape)]
  lenVars = \case
    LLit _ -> []
    LVar v _ -> [(v, KLen)]
    LRank v _ -> [(v, KShape)]

renderWithNamed ::
  (Hash -> Text) -> Spelling -> Map VarId Text -> Int -> Type -> Text
renderWithNamed typeName spelling names prec = \case
  TBool -> "Bool"
  -- As an argument of a declared type, a tensor with a shape or dimension is parenthesised.
  TTensor sh d
    | prec > 10
    , not (T.null (dim d)) || sh /= SNil ->
        "(" <> tensor sh <> dim d <> ")"
  TTensor sh d -> tensor sh <> dim d
  -- A scalar point is `Point [K]`; a point over a vector space, `Point (Vec 3 [m])`.
  TPoint SNil d -> "Point" <> dim d
  TPoint sh d -> "Point (" <> tensor sh <> dim d <> ")"
  TScale SNil d -> "Scale" <> dim d
  TScale sh d -> "Scale (" <> tensor sh <> dim d <> ")"
  TTuple ts ->
    "("
      <> T.intercalate ", " (map (renderWithNamed typeName spelling names 0) ts)
      <> ")"
  TList t -> "{" <> renderWithNamed typeName spelling names 0 t <> "}"
  -- A declared type prints by its short hash here; the driver replaces that
  -- with the current name (design §7.2), so inference needs no name table.
  TData h as ->
    paren
      (prec > 10 && not (null as))
      (T.unwords (typeName h : map (argWith names) as))
  TFun a b ->
    paren
      (prec > 0)
      ( renderWithNamed typeName spelling names 1 a
          <> arrowText spelling
          <> renderWithNamed typeName spelling names 0 b
      )
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
    | otherwise = " " <> renderDimIn spelling dimName d
  dimName v = Map.findWithDefault ("d" <> T.pack (show v)) v names
  argWith ns = \case
    AType t -> renderWithNamed typeName spelling ns 11 t
    ALen l -> renderLen ns l
    AShape sh -> renderShapeList ns sh
    ADim d
      | [(DVar v, 1)] <- dimAtoms d -> dimName v
      | otherwise -> renderDimIn spelling dimName d

{- | A length on its own: an offset form or a rank is parenthesised, @Vec (n +
1)@, @Vec (rank s)@.
-}
renderLen :: Map VarId Text -> Len -> Text
renderLen names = \case
  l@(LVar _ k) | k /= 0 -> "(" <> renderLenBare names l <> ")"
  l@(LRank _ _) -> "(" <> renderLenBare names l <> ")"
  l -> renderLenBare names l

-- | A length inside a list or a cons chain, where no parentheses are needed.
renderLenBare :: Map VarId Text -> Len -> Text
renderLenBare names = \case
  LLit k -> T.pack (show k)
  LVar v 0 -> name v
  LVar v k -> name v <> " + " <> T.pack (show k)
  LRank v 0 -> "rank " <> shapeName v
  LRank v k -> "rank " <> shapeName v <> " + " <> T.pack (show k)
 where
  name v = Map.findWithDefault ("n" <> T.pack (show v)) v names
  shapeName v = Map.findWithDefault ("s" <> T.pack (show v)) v names

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

{- | The constructors of a data type with their field types, in canonical
(declaration) order: the one table 'Con' and 'Case' are checked against
(design §5.1). Declared types come from the lookup, with their parameters
instantiated at the type's arguments.
-}
dataConstructors :: (Hash -> Maybe TypeDef) -> Type -> Maybe [(ConRef, [Type])]
dataConstructors defs = \case
  TBool -> Just [(Builtin "False", []), (Builtin "True", [])]
  TTuple ts -> Just [(Builtin "Tuple", ts)]
  TList t -> Just [(Builtin "Nil", []), (Builtin "Cons", [t, TList t])]
  TData h as -> do
    def <- defs h
    let sub = Map.fromList (zip (map fst def.params) as)
    pure
      [ (UserCon h i, map (substOnce sub . unself h) fields)
      | (i, fields) <- zip [0 ..] def.constructors
      ]
  _ -> Nothing
 where
  -- The definition's own type, written with its parameters, becomes the
  -- applied type.
  unself h = go
   where
    go = \case
      TData h' as' | h' == selfType -> TData h (map goArg as')
      TData h' as' -> TData h' (map goArg as')
      TTuple ts -> TTuple (map go ts)
      TList t -> TList (go t)
      TFun a b -> TFun (go a) (go b)
      t -> t
    goArg = \case
      AType t -> AType (go t)
      a -> a

{- | What the equality of a declared type rests on (design §4.2): the type
arguments that must themselves have equality, or 'Nothing' when no
arguments would do, because a field is a function or a scale, or the type
is unknown. Equality on @T as@ is derived structurally: it holds when every
field of every constructor, at @as@, has equality.

A recursive occurrence of the type is assumed to have equality, as the
instance being derived (coinductively), and asks only for its own
arguments at the parameters that need it. Which parameters need it is a
least fixed point over the fields, so a nested type such as
@data N a = Z a | S (N (a, a))@ is decided without unfolding: @N τ@ needs
equality on @τ@ alone.
-}
equalityArgs :: (Hash -> Maybe TypeDef) -> Hash -> [Arg] -> Maybe [Type]
equalityArgs defs h as = do
  def <- defs h
  need <- equalityParams defs def
  Just [t | (True, AType t) <- zip need as]

{- | For each parameter of a declaration, whether its equality depends on
that parameter's: the least solution, from "none", of the fields'
requirements. 'Nothing' when a field can never have equality.
-}
equalityParams :: (Hash -> Maybe TypeDef) -> TypeDef -> Maybe [Bool]
equalityParams defs def = go (map (const False) def.params)
 where
  go need = do
    vs <- concat <$> mapM (needs need) (concat def.constructors)
    let need' = [v `elem` vs | (v, _) <- def.params]
    if need' == need then Just need else go need'
  -- The parameters a field's equality rests on, given what the type's own
  -- parameters are assumed to need.
  needs need = \case
    TTensor _ _ -> Just []
    TBool -> Just []
    TPoint _ _ -> Just []
    TVar v -> Just [v]
    TTuple ts -> concat <$> mapM (needs need) ts
    TList t -> needs need t
    TData h' as'
      | h' == selfType -> picked need as'
      | otherwise -> do
          d <- defs h'
          need' <- equalityParams defs d
          picked need' as'
    _ -> Nothing
   where
    picked which as' = concat <$> sequence [needs need t | (True, AType t) <- zip which as']

{- | What inference and lint need from the codebase: the schemes of a stored
definition, and the declaration of a data type.
-}
data TypeLookup = TypeLookup
  { schemesOf :: Hash -> Maybe [Scheme]
  , typeDefOf :: Hash -> Maybe TypeDef
  }

-- | A lookup that knows nothing: for closed terms over built-in types.
noLookup :: TypeLookup
noLookup = TypeLookup (const Nothing) (const Nothing)

{- | A constructor's name as it prints without a codebase: built-in names
as they are, a declared one as @#hash.i@ for the driver to name.
-}
conText :: ConRef -> Text
conText = \case
  Builtin c -> c
  UserCon h i -> showHash h <> "." <> T.pack (show i)

{- | The label of a @structural data@ declaration: no owner, so two
declarations of the same shape are one type.
-}
structuralLabel :: Label
structuralLabel = Tag ""

{- | A declaration as it could be written again: @data Name a = Con fields |
…@, with the type's own hash standing for recursive occurrences (the
driver names it) and parameters named by kind as in 'renderType'.
-}
renderTypeDef ::
  Spelling -> Hash -> Text -> [Text] -> [[Maybe Text]] -> TypeDef -> Text
renderTypeDef spelling h name conNames fieldNames def =
  (if def.label == structuralLabel then "structural " else "")
    <> "data "
    <> T.unwords (name : map (\(v, _) -> Map.findWithDefault "?" v names) def.params)
    <> " = "
    <> T.intercalate
      " | "
      ( zipWith3
          constructor
          (conNames ++ repeat "?")
          (fieldNames ++ repeat [])
          def.constructors
      )
 where
  names = prettyNames def.params
  -- A record, when every field is named; else positional.
  constructor c labels fields = case sequence (take (length fields) (labels ++ repeat Nothing)) of
    Just ls
      | not (null fields) ->
          c
            <> " {"
            <> T.intercalate
              ", "
              ( zipWith
                  (\l t -> l <> " :: " <> renderWith spelling names 0 (unself t))
                  ls
                  fields
              )
            <> "}"
    _ -> T.unwords (c : map (field . unself) fields)
  -- A field is an atom: a compound type goes in parentheses.
  field t =
    let s = renderWith spelling names 11 t
     in if " " `T.isInfixOf` s && not (T.isPrefixOf "(" s || T.isPrefixOf "{" s)
          then "(" <> s <> ")"
          else s
  unself = \case
    TData h' as | h' == selfType -> TData h (map unselfArg as)
    TData h' as -> TData h' (map unselfArg as)
    TTuple ts -> TTuple (map unself ts)
    TList t -> TList (unself t)
    TFun a b -> TFun (unself a) (unself b)
    t -> t
  unselfArg = \case
    AType t -> AType (unself t)
    a -> a
