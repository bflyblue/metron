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
  withBuiltins,
  conText,
  selfType,
  structuralLabel,
  renderTypeDef,
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
  renderType,
  renderScheme,
  renderTypeIn,
  renderSchemeIn,
  renderTypeIds,
  renderSchemeIds,
  renderSignature,
  renderForallWith,
  renderForallIn,
  canonicalScheme,
  defaultAxes,
  renderArg,
) where

import Control.Applicative ((<|>))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Builtin
import Eval.Core (ConRef (..), Hash (..), showHash)
import Eval.Dimension
import Eval.Type.Base

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

{- | A scheme as @:type@ and @:ls@ print it and a signature is written
back (@:edit@, @:export@, the @sig@ log line; design §4.8, §3.9 decision
6): headed by @forall@ and its variables in the order they are named, when
it has any, so that the text reads back as the same scheme. Declared types
are named by the given function. Variables are named by kind as
'renderType' names them, each name used once, but a bound variable shadows
a unit of its name within its type, so a name the type prints otherwise
is skipped: the base symbols of its dimensions
(@forall s1 d. Tensor s1 d -> Tensor s1 [s d]@). An axis variable prints
as nothing (§3.9, stage 1) and is not bound.
-}
renderForallWith :: (Hash -> Text) -> Spelling -> Scheme -> Text
renderForallWith typeName spelling (Forall _ t) =
  let vs = [(v, k) | (v, k) <- freeVars t, k /= KAxis]
      names = forallNames (baseSymbolsOf t) vs
      body = renderWithNamed typeName spelling names 0 t
   in if null vs
        then body
        else
          "forall "
            <> T.unwords [Map.findWithDefault "?" v names | (v, _) <- vs]
            <> ". "
            <> body

-- | 'renderForallWith', declared types by their short hashes.
renderForallIn :: Spelling -> Scheme -> Text
renderForallIn = renderForallWith showHash

{- | A signature as it is written back (design §4.8): 'renderForallWith'.
A bound variable shadows a unit of its name, so no name is avoided.
-}
renderSignature ::
  Spelling -> (Hash -> Text) -> Scheme -> Text
renderSignature spelling typeName = renderForallWith typeName spelling

{- | Names for the variables of a @forall@, by kind as 'prettyNames' gives
them, each skipping the names taken and every name already given.
-}
forallNames :: Set.Set Text -> [(VarId, Kind)] -> Map VarId Text
forallNames taken vs = snd (foldl pick (taken, Map.empty) vs)
 where
  pick (used, acc) (v, k) =
    case [c | c <- candidates k, Set.notMember c used] of
      c : _ -> (Set.insert c used, Map.insert v c acc)
      [] -> (used, acc)
  candidates = \case
    KType -> map T.singleton ['a' .. 'm'] ++ numbered "t"
    KLen -> ["n", "m", "k", "l", "p", "q"] ++ numbered "n"
    KShape -> "s" : numbered "s"
    KDim -> "d" : numbered "d"
    KAxis -> []
  numbered p = [p <> T.pack (show i) | i <- [1 :: Int ..]]

-- | The base symbols a type's dimensions print with.
baseSymbolsOf :: Type -> Set.Set Text
baseSymbolsOf = \case
  TTensor _ d -> dim d
  TPoint _ d -> dim d
  TScale _ _ d -> dim d
  TData _ as -> foldMap arg as
  TFun a b -> baseSymbolsOf a <> baseSymbolsOf b
  TVar _ -> Set.empty
 where
  dim d = Set.fromList [baseSymbol b | (Base b, _) <- dimAtoms d]
  arg = \case
    AType t -> baseSymbolsOf t
    ADim d -> dim d
    _ -> Set.empty

{- | The scheme a named value is used at (design §3.9, decision 5): a
definition whose type is not a function keeps no free axis variable, so
its quantified axes are anonymous; a function's are left as they are. A
stored scheme is its Core's alone and stays general, so that a signature
can keep a value's axes polymorphic (@off :: forall (a : 3). Vec a [m]@);
this default is what an unsigned name means where it is used.
-}
defaultAxes :: Scheme -> Scheme
defaultAxes sc@(Forall vs t) = case t of
  TFun _ _ -> sc
  _
    | null axes -> sc
    | otherwise ->
        Forall
          [(v, k) | (v, k) <- vs, k /= KAxis]
          (substOnce (Map.fromList [(v, AAxis AAnon) | v <- axes]) t)
 where
  axes = [v | (v, KAxis) <- vs]

{- | A scheme with its variables renumbered from 0 in order of appearance,
so that two schemes that differ only in their variables' ids are equal.
-}
canonicalScheme :: Scheme -> Scheme
canonicalScheme (Forall _ t) =
  let vs = freeVars t
      renaming = Map.fromList [(v, varArg k i) | (i, (v, k)) <- zip [0 ..] vs]
   in Forall [(i, k) | (i, (_, k)) <- zip [0 ..] vs] (substOnce renaming t)

renderWith :: Spelling -> Map VarId Text -> Int -> Type -> Text
renderWith = renderWithNamed showHash

renderArg :: Arg -> Text
renderArg = \case
  AType t -> renderTypeIds t
  ALen l -> renderLen (idNames (lenVars l)) l
  AShape sh -> renderShapeList (idNames (shapeVars sh)) sh
  ADim d -> renderDimWith (\v -> "d" <> T.pack (show v)) d
  -- The name slot prints as nothing until named axes exist (design §3.9).
  AAxis _ -> ""
 where
  shapeVars = \case
    SNil -> []
    SCons l _ rest -> lenVars l ++ shapeVars rest
    SVar v -> [(v, KShape)]
  lenVars = \case
    LLit _ -> []
    LVar v _ -> [(v, KLen)]
    LRank v _ -> [(v, KShape)]

renderWithNamed ::
  (Hash -> Text) -> Spelling -> Map VarId Text -> Int -> Type -> Text
renderWithNamed typeName spelling names prec = \case
  -- The built-in types print by their hash, whatever names them (design §4.1).
  BoolT -> "Bool"
  TupleT ts ->
    "("
      <> T.intercalate ", " (map (renderWithNamed typeName spelling names 0) ts)
      <> ")"
  ListT t -> "{" <> renderWithNamed typeName spelling names 0 t <> "}"
  -- As an argument of a declared type, a tensor with a shape or dimension is parenthesised.
  TTensor sh d
    | prec > 10
    , not (T.null (dim d)) || sh /= SNil ->
        "(" <> tensor sh <> dim d <> ")"
  TTensor sh d -> tensor sh <> dim d
  -- A scalar point is `Point [K]`; a point over a vector space, `Point (Vec 3 [m])`.
  TPoint SNil d -> "Point" <> dim d
  TPoint sh d -> "Point (" <> tensor sh <> dim d <> ")"
  TScale SNil _ d -> "Chart" <> dim d
  TScale sh _ d -> "Chart (" <> tensor sh <> dim d <> ")"
  -- A declared type prints by its short hash here; the driver replaces that
  -- with the current name (design §7.2), so inference needs no name table.
  -- An axis argument, a length's companion, prints as nothing (design §3.9).
  TData h as0 ->
    let as = filter (not . isAxisArg) as0
     in paren
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
  -- The axes of a position print as nothing in stage 1 (design §3.9).
  tensor = \case
    SNil -> "Num"
    SCons n _ SNil -> "Vec " <> renderLen names n
    SCons m _ (SCons n _ SNil) -> "Mat " <> renderLen names m <> " " <> renderLen names n
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
    AAxis _ -> ""

-- | An argument that fills an axis parameter, a length's companion.
isAxisArg :: Arg -> Bool
isAxisArg = \case
  AAxis _ -> True
  _ -> False

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
    SCons l _ rest -> l : lens rest
    SVar _ -> []
  tailVar = \case
    SNil -> Nothing
    SCons _ _ rest -> tailVar rest
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
      ++ zip [v | (v, KAxis) <- vs] ["x" <> T.pack (show i) | i <- [1 :: Int ..]]

idNames :: [(VarId, Kind)] -> Map VarId Text
idNames vs = Map.fromList [(v, prefix k <> T.pack (show v)) | (v, k) <- vs]
 where
  prefix = \case
    KType -> "t"
    KLen -> "n"
    KShape -> "s"
    KDim -> "d"
    KAxis -> "x"

-- Data ----------------------------------------------------------------------------

{- | The constructors of a data type with their field types, in canonical
(declaration) order: the one table 'Con' and 'Case' are checked against
(design §5.1). Declared types come from the lookup, or are the built-in
ones ("Eval.Builtin"), with their parameters instantiated at the type's
arguments.
-}
dataConstructors :: (Hash -> Maybe TypeDef) -> Type -> Maybe [(ConRef, [Type])]
dataConstructors defs = \case
  TData h as -> do
    def <- withBuiltins defs h
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
      TFun a b -> TFun (go a) (go b)
      t -> t
    goArg = \case
      AType t -> AType (go t)
      a -> a

-- | A lookup of declarations that also knows the built-in ones.
withBuiltins :: (Hash -> Maybe TypeDef) -> Hash -> Maybe TypeDef
withBuiltins defs h = builtinDefs h <|> defs h

{- | What the equality of a declared type rests on (design §4.2): the type
arguments that must themselves have equality, or 'Nothing' when no
arguments would do, because a field is a function or a scale, or the type
is unknown. Equality on @T as@ is derived structurally: it holds when every
field of every constructor, at @as@, has equality. @Bool@, tuples and lists
are declared types like any other here.

A recursive occurrence of the type is assumed to have equality, as the
instance being derived (coinductively), and asks only for its own
arguments at the parameters that need it. Which parameters need it is a
least fixed point over the fields, so a nested type such as
@data N a = Z a | S (N (a, a))@ is decided without unfolding: @N τ@ needs
equality on @τ@ alone.
-}
equalityArgs :: (Hash -> Maybe TypeDef) -> Hash -> [Arg] -> Maybe [Type]
equalityArgs defs0 h as = do
  def <- defs h
  need <- equalityParams defs def
  Just [t | (True, AType t) <- zip need as]
 where
  defs = withBuiltins defs0

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
    TPoint _ _ -> Just []
    TVar v -> Just [v]
    TData h' as'
      | h' == selfType -> picked need as'
      | otherwise -> do
          d <- defs h'
          need' <- equalityParams defs d
          picked need' as'
    _ -> Nothing
   where
    picked which as' = concat <$> sequence [needs need t | (True, AType t) <- zip which as']

{- | A lookup that knows nothing but the built-in declarations: for closed
terms over built-in types.
-}
noLookup :: TypeLookup
noLookup = TypeLookup (const Nothing) builtinDefs

{- | A constructor's name as it prints without a codebase: a built-in one
by the name its declaration gives it (@True@, @Cons@), a declared one as
@#hash.i@ for the driver to name.
-}
conText :: ConRef -> Text
conText c@(UserCon h i) =
  fromMaybe (showHash h <> "." <> T.pack (show i)) (builtinConName c)

{- | A declaration as it could be written again: @data Name a = Con fields |
…@, with the type's own name for recursive occurrences and parameters
named by kind as in 'renderType'.
-}
renderTypeDef ::
  Spelling -> Text -> [Text] -> [[Maybe Text]] -> TypeDef -> Text
renderTypeDef spelling name conNames fieldNames def =
  (if def.label == structuralLabel then "structural " else "")
    <> "data "
    -- An axis parameter, a length's companion, is not written (design §3.9).
    <> T.unwords
      (name : [Map.findWithDefault "?" v names | (v, k) <- def.params, k /= KAxis])
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
  render =
    renderWithNamed
      (\h -> if h == selfType then name else showHash h)
      spelling
      names
  -- A record, when every field is named; else positional.
  constructor c labels fields = case sequence (take (length fields) (labels ++ repeat Nothing)) of
    Just ls
      | not (null fields) ->
          c
            <> " {"
            <> T.intercalate
              ", "
              (zipWith (\l t -> l <> " :: " <> render 0 t) ls fields)
            <> "}"
    _ -> T.unwords (c : map field fields)
  -- A field is an atom: a compound type goes in parentheses.
  field t =
    let s = render 11 t
     in if " " `T.isInfixOf` s && not (T.isPrefixOf "(" s || T.isPrefixOf "{" s)
          then "(" <> s <> ")"
          else s
