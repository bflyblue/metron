{-# LANGUAGE PatternSynonyms #-}

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
  Role (..),
  Frame (..),
  FrameSlot (..),
  Space (..),
  SpaceSlot (..),
  overType,
  spaceLens,
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
  applyRole,
  applyFrame,
  applySpace,
  applyArg,
  applyScheme,
  substOnce,
  freeVars,
  typeRefs,
  numT,
  numD,
  vecT,
  vecD,
  shapeOfDims,
  closedLens,
  appendShape,
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
  writtenParams,
  renderArg,
) where

import Control.Applicative ( (<|>) )
import Data.List ( nubBy )
import Data.Map.Strict ( Map )
import Data.Maybe ( fromMaybe )
import Data.Text ( Text )
import Eval.Builtin
    ( pattern BoolT,
      pattern ListT,
      pattern TupleT,
      builtinConName,
      builtinDefs,
      frameDefMoving,
      isAxesDef )
import Eval.Core ( ConRef(..), Hash(..), Label(..), showHash )
import Eval.Dimension
    ( arrowText,
      baseSymbol,
      dimAtoms,
      dimOne,
      dimVars,
      isDimOne,
      renderDimArgIn,
      DimAtom(Base, DVar),
      Spelling(Ascii) )
import Eval.Type.Base
    ( appendShape,
      applyArg,
      applyAxis,
      applyDim,
      applyFrame,
      applyLen,
      applyRole,
      applyScheme,
      applyShape,
      applySpace,
      applyType,
      closedLens,
      emptySubst,
      freeVars,
      numD,
      numT,
      overType,
      rankLen,
      selfType,
      shapeOfDims,
      spaceLens,
      structuralLabel,
      substOnce,
      varArg,
      vecD,
      vecT,
      Arg(..),
      Axis(..),
      Frame(..),
      FrameSlot(..),
      Kind(..),
      Len(..),
      Role(..),
      Scheme(..),
      Shape(..),
      Space(..),
      SpaceSlot(..),
      Subst,
      Type(..),
      TypeDef(..),
      TypeLookup(..),
      VarId,
      typeRefs )
import Data.Map.Strict qualified as Map
    ( insertWith,
      elems,
      empty,
      keysSet,
      lookup,
      member,
      notMember,
      restrictKeys,
      toList,
      union,
      withoutKeys,
      findWithDefault,
      fromList,
      insert,
      mapMaybe )
import Data.Set qualified as Set
    ( Set,
      member,
      notMember,
      union,
      empty,
      fromList,
      insert,
      singleton,
      size )
import Data.Text qualified as T
    ( intercalate,
      isInfixOf,
      isPrefixOf,
      null,
      unwords,
      pack,
      singleton )

-- Rendering ---------------------------------------------------------------------

{- | Print a type with variables named by kind in order of appearance: @a b c@
for types, @n m k@ for lengths, @s s1 s2@ for shapes, @d d1 d2@ for
dimensions (design §4.5), as @:type@ names them ('forallNames'): each name
used once, and a name the type prints as a base symbol skipped, so that an
error's @Mat n k m@ never reads a length as metres. Rank zero, one and two
tensors print as @Num@, @Vec@ and @Mat@; a dimension follows as their last
argument unless it is @1@, bare when it is one name and in parentheses
otherwise (design §4.1).
-}
renderType :: Type -> Text
renderType = renderTypeIn Ascii

renderScheme :: Scheme -> Text
renderScheme = renderSchemeIn Ascii

-- | 'renderType' in a chosen spelling: @Num (m/s²) → Num m@ in unicode.
renderTypeIn :: Spelling -> Type -> Text
renderTypeIn spelling t =
  renderWith spelling (forallNames (baseSymbolsOf t) (freeVars t)) 0 t

renderSchemeIn :: Spelling -> Scheme -> Text
renderSchemeIn spelling sc@(Forall _ t)
  | any
      (\f -> case f.space.slot of SpVar _ -> restrictedSpace t f; _ -> False)
      (framesOf t) =
      renderForallWith showHash spelling sc
  | otherwise = renderTypeIn spelling t

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
(@forall s1 d. Tensor s1 d -> Tensor s1 (s*d)@).

An axis variable (§3.9, decision 6) beside a length variable is one
binder with it and prints as that length (@forall n d. Vec n d -> …@);
beside a literal length it is a sized binder and prints by its name,
@forall (a : 3) d. Vec a d -> …@; otherwise, as a chart's root or as a
second axis set beside a length that already has one, it is a binder of
its own and prints by its name.
-}
renderForallWith :: (Hash -> Text) -> Spelling -> Scheme -> Text
renderForallWith typeName spelling (Forall _ t) =
  let (absorbed, sized) = axisRoles t
      owners = ownersOf t
      spaceConstraints =
        Map.fromList
          [ (s, TTensor sp.shape sp.dim)
          | f <- framesOf t
          , restrictedSpace t f
          , let sp = f.space
          , SpVar s <- [sp.slot]
          ]
      printed = Set.fromList [x | AVar x <- map snd (positionsOf t)]
      standing =
        Set.fromList
          (map fst (standingVars t ++ concatMap freeVars (Map.elems spaceConstraints)))
      printedLens =
        Set.fromList
          [ v
          | (l, a) <- positionsOf t ++ concatMap positionsOf (Map.elems spaceConstraints)
          , case a of
              ANamed _ -> False
              AVar x -> Map.notMember x owners.axisOwner
              AAnon -> True
          , v <- case l of
              LVar v _ -> [v]
              _ -> []
          ]
      -- A space prints when it is two frames', stands on its own, or its
      -- base axes are written, @Mat s c@.
      spacePrinted =
        Map.keysSet spaceConstraints
          <> printedSpaces owners standing
          <> Set.fromList
            [ s
            | AVar b <- map snd (positionsOf t)
            , Just s <- [Map.lookup b owners.axisOwner]
            , Map.member s owners.spaceFrames
            ]
      vs =
        orderSpaces
          owners
          [ (v, k)
          | (v, k) <- freeVars t
          , case k of
              KAxis ->
                Set.member v standing
                  && Map.notMember v absorbed
                  && Set.member v printed
                  && Map.notMember v owners.axisOwner
              KSpace -> Set.member v spacePrinted
              -- A length prints unless its axes print by a name instead.
              KLen -> Set.member v standing && Set.member v printedLens
              _ -> Set.member v standing
          ]
      names = forallNames (baseSymbolsOf t) vs
      axes =
        ownedNames
          owners
          names
          (Map.restrictKeys names (Set.fromList [v | (v, KAxis) <- vs]))
          absorbed
      body = renderWithNamed typeName spelling axes names 0 t
      bareLengths =
        Set.fromList
          [ v
          | amount <- Map.elems spaceConstraints
          , (v, KLen) <- freeVars amount
          , all
              (\(l, a) -> l /= LVar v 0 || a == AAnon || frameOwned a)
              (positionsOf t)
          ]
      frameOwned = \case AVar v -> Map.member v owners.axisOwner; _ -> False
      binder v k = case (k, Map.lookup v sized) of
        (KLen, _) | Set.member v bareLengths -> "(" <> name v <> " : Len)"
        (KSpace, _)
          | Just amount <- Map.lookup v spaceConstraints ->
              "("
                <> name v
                <> " : Space ("
                <> renderWithNamed typeName spelling axes names 0 amount
                <> "))"
        (_, Just n) -> "(" <> name v <> " : " <> T.pack (show n) <> ")"
        (KFrame, _) -> case Map.lookup v owners.frameSpace of
          Just (SpNamed h) -> "(" <> name v <> " : " <> typeName h <> ")"
          Just (SpVar s)
            | Set.member s spacePrinted -> "(" <> name v <> " : " <> name s <> ")"
          _ -> name v
        _ -> name v
      name v = Map.findWithDefault "?" v names
   in if null vs
        then body
        else "forall " <> T.unwords [binder v k | (v, k) <- vs] <> ". " <> body

{- | Companions can be hidden only when the written uses reconstruct them.
In particular, Point c alone says nothing about the rank or dimension.
-}
restrictedSpace :: Type -> Frame -> Bool
restrictedSpace t f = dimensionRestricted || shapeRestricted || shared
 where
  sp = f.space
  dimensionRestricted = case dimAtoms sp.dim of
    [(DVar _, 1)] -> False
    _ -> True
  shapeRestricted = case sp.shape of
    SVar _ -> False
    SCons (LVar _ 0) _ SNil ->
      not (any (\(_, a) -> a == f.axes || a == sp.base) (positionsOf t))
    _ -> True
  -- A length occurring only under c's or s's axes is reconstructed by
  -- those axis names. An anonymous axis of the same length is not.
  companions =
    dimVars sp.dim
      ++ [ v
         | (v, k) <- freeVars (TTensor sp.shape dimOne)
         , k == KShape
             || any (\(l, a) -> a /= f.axes && a /= sp.base && l == LVar v 0) (positionsOf t)
         ]
  shared = any (`elem` map fst (standingVars t)) companions

{- | The frames and spaces of a type (design §3.10, F1): each frame
variable's space, the frames on each space variable, and the axis
variables that are companions, each with the variable it prints as: a
frame's axes as the frame, and a space's base axes as the space.
-}
data Owners = Owners
  { frameSpace :: Map VarId SpaceSlot
  , axisOwner :: Map VarId VarId
  , spaceFrames :: Map VarId (Set.Set FrameSlot)
  }

ownersOf :: Type -> Owners
ownersOf t0 = foldl add (Owners Map.empty Map.empty Map.empty) (framesOf t0)
 where
  first _ old = old
  add o (Frame sl a sp) =
    Owners
      { frameSpace = case sl of
          FrVar c -> Map.insertWith first c sp.slot o.frameSpace
          _ -> o.frameSpace
      , axisOwner =
          let byFrame = case (sl, a) of
                (FrVar c, AVar x) -> Map.insertWith first x c o.axisOwner
                _ -> o.axisOwner
           in case (sp.slot, sp.base) of
                (SpVar s, AVar b) -> Map.insertWith first b s byFrame
                _ -> byFrame
      , spaceFrames = case sp.slot of
          SpVar s -> Map.insertWith Set.union s (Set.singleton sl) o.spaceFrames
          _ -> o.spaceFrames
      }

-- | Every frame a type mentions, in order.
framesOf :: Type -> [Frame]
framesOf = \case
  TPoint f -> [f]
  TChart f -> [f]
  TOver f _ -> [f]
  TData _ as -> concat [framesOf t | AType t <- as]
  TFun a b -> framesOf a ++ framesOf b
  _ -> []

{- | The space variables printed as binders: the space of two frames, or
one that stands on its own, as a declared type's argument.
-}
printedSpaces :: Owners -> Set.Set VarId -> Set.Set VarId
printedSpaces owners standing =
  Set.fromList
    [ s
    | (s, frames) <- Map.toList owners.spaceFrames
    , Set.size frames > 1 || Set.member s standing
    ]

-- | The binders, each printed space before the first frame on it.
orderSpaces :: Owners -> [(VarId, Kind)] -> [(VarId, Kind)]
orderSpaces owners vs = go Set.empty vs
 where
  spaces = Set.fromList [v | (v, KSpace) <- vs]
  go _ [] = []
  go seen ((v, k) : rest) = case k of
    KSpace
      | Set.member v seen -> go seen rest
      | otherwise -> (v, k) : go (Set.insert v seen) rest
    KFrame
      | Just (SpVar s) <- Map.lookup v owners.frameSpace
      , Set.member s spaces
      , Set.notMember s seen ->
          (s, KSpace) : (v, k) : go (Set.insert s seen) rest
    _ -> (v, k) : go seen rest

{- | The variables of a type outside the companions of its frames and
spaces (design §3.10): a frame stands for its slot alone and a space for
nothing, so that a companion that also stands elsewhere is still bound.
-}
standingVars :: Type -> [(VarId, Kind)]
standingVars = nubBy (\a b -> fst a == fst b) . go
 where
  go = \case
    TPoint f -> frame f
    TChart f -> frame f
    TOver f md -> frame f ++ maybe [] dims md
    -- A declared type's companion arguments do not print, but a length's
    -- axes print with it.
    TData _ as ->
      concat
        [ arg a ++ maybe [] (\x -> freeVars (TData selfType [AAxis x])) ax
        | (a, ax) <- withCompanions as
        ]
    TFun a b -> go a ++ go b
    t -> freeVars t
  frame f = case f.slot of
    FrVar v -> [(v, KFrame)]
    FrNamed _ -> []
  dims d = [(v, KDim) | v <- dimVars d]
  arg = \case
    AType t -> go t
    a -> freeVars (TData selfType [a])

{- | The axis variables that print as their owner's name, a frame's or a
space's (design §3.10, F4: a frame's name in an axis position means its
axes), added to those that print by a name of their own.
-}
ownedNames ::
  Owners -> Map VarId Text -> Map VarId Text -> Map VarId VarId -> AxisNames
ownedNames owners names own absorbed =
  AxisNames
    (Map.union own (Map.mapMaybe (`Map.lookup` names) owners.axisOwner))
    (Map.withoutKeys absorbed (Map.keysSet owners.axisOwner))

{- | The part each axis variable of a type plays in its printing (design
§3.9, decision 6), from the first position it appears at: one binder with
the length variable beside it, when that length has no axis variable of
its own yet; a sized binder, of the literal length beside it; or, left out
of both, a binder of its own.
-}
axisRoles :: Type -> (Map VarId VarId, Map VarId Int)
axisRoles t =
  fst
    (foldl step ((Map.empty, Map.empty), (Set.empty, Set.empty)) (positionsOf t))
 where
  step acc@((absorbed, sized), (decided, partnered)) = \case
    (l, AVar x)
      | Set.member x decided -> acc
      | LVar v _ <- l
      , Set.notMember v partnered ->
          ( (Map.insert x v absorbed, sized)
          , (Set.insert x decided, Set.insert v partnered)
          )
      | LLit k <- l ->
          ((absorbed, Map.insert x k sized), (Set.insert x decided, partnered))
      | otherwise -> ((absorbed, sized), (Set.insert x decided, partnered))
    _ -> acc

-- | Every position of a type, a length and its axes, in order.
positionsOf :: Type -> [(Len, Axis)]
positionsOf = \case
  TQty _ sh _ -> shape sh
  TData _ as -> concatMap arg as ++ [(l, x) | (ALen l, Just x) <- withCompanions as]
  TFun a b -> positionsOf a ++ positionsOf b
  _ -> []
 where
  shape = \case
    SCons l a rest -> (l, a) : shape rest
    _ -> []
  arg = \case
    AType t -> positionsOf t
    AShape sh -> shape sh
    _ -> []

{- | A declared type's arguments as written, the companion arguments left
out, each length with its companion's axes (design §3.9): a declaration's
companion parameters follow its written ones, an axis set for each length
and then, for each frame, its axes and its space's slot, shape, dimension
and base axes (design §3.10), so the @j@-th axis argument goes with the
@j@-th length.
-}
withCompanions :: [Arg] -> [(Arg, Maybe Axis)]
withCompanions as =
  let lens = length [() | ALen _ <- as]
      frames = length [() | AFrame _ <- as]
      written = take (length as - lens - companionsPerFrame * frames) as
      companions = drop (length written) as
   in go written [x | AAxis x <- take lens companions]
 where
  go (ALen l : rest) (x : xs) = (ALen l, Just x) : go rest xs
  go (a : rest) xs = (a, Nothing) : go rest xs
  go [] _ = []

{- | How many companion parameters a declared type's frame parameter has
(design §3.10): its axes, and its space's slot, shape, dimension and base.
-}
companionsPerFrame :: Int
companionsPerFrame = 5

{- | A declaration's written parameters, its companions left out (design
§3.9, §3.10): they follow the written ones, an axis set for each length
and the companions of each frame.
-}
writtenParams :: [(VarId, Kind)] -> [(VarId, Kind)]
writtenParams ps =
  take
    ( length ps
        - length [() | (_, KLen) <- ps]
        - companionsPerFrame * length [() | (_, KFrame) <- ps]
    )
    ps

{- | How the name slots of positions print (design §3.9): the axis
variables that print by a name of their own, and those that are one
binder with a length variable. A named set prints as its type's name,
in place of the length.
-}
data AxisNames = AxisNames
  { own :: Map VarId Text
  , absorbed :: Map VarId VarId
  }

-- | No axis variable prints: every slot but a named one prints its length.
noAxisNames :: AxisNames
noAxisNames = AxisNames Map.empty Map.empty

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
    KAxis -> ["a", "b", "c", "e", "f", "g", "h"] ++ numbered "a"
    KFrame -> "c" : numbered "c"
    KSpace -> "s" : numbered "s"
    KRole -> "r" : numbered "r"
  numbered p = [p <> T.pack (show i) | i <- [1 :: Int ..]]

-- | The base symbols a type's dimensions print with.
baseSymbolsOf :: Type -> Set.Set Text
baseSymbolsOf = \case
  TQty _ _ d -> dim d
  TPoint _ -> Set.empty
  TChart _ -> Set.empty
  TOver _ md -> foldMap dim md
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
can keep a value's axes polymorphic (@off :: forall (a : 3). Vec a m@);
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
renderWith spelling names prec t =
  renderWithNamed
    showHash
    spelling
    (ownedNames (ownersOf t) names Map.empty Map.empty)
    names
    prec
    t

renderArg :: Arg -> Text
renderArg = \case
  AType t -> renderTypeIds t
  ALen l -> renderLen (idNames (lenVars l)) l
  AShape sh -> renderShapeList (idNames (shapeVars sh)) sh
  ADim d -> renderDimArgIn Ascii (\v -> "d" <> T.pack (show v)) d
  -- A type application's name slot prints as nothing (design §3.9).
  AAxis _ -> ""
  AFrame (FrNamed h) -> showHash h
  AFrame (FrVar v) -> "f" <> T.pack (show v)
  ASpace (SpNamed h) -> showHash h
  ASpace (SpVar v) -> "sp" <> T.pack (show v)
  ARole r -> roleText (\v -> "r" <> T.pack (show v)) r
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
  (Hash -> Text) -> Spelling -> AxisNames -> Map VarId Text -> Int -> Type -> Text
renderWithNamed typeName spelling axes names prec = \case
  -- The built-in types print by their hash, whatever names them (design §4.1).
  BoolT -> "Bool"
  TupleT ts ->
    "("
      <> T.intercalate ", " (map (renderWithNamed typeName spelling axes names 0) ts)
      <> ")"
  ListT t -> "{" <> renderWithNamed typeName spelling axes names 0 t <> "}"
  -- As an argument of a declared type, a tensor with a shape or dimension is parenthesised.
  TTensor sh d
    | prec > 10
    , not (T.null (dim d)) || sh /= SNil ->
        "(" <> tensor sh <> dim d <> ")"
  TTensor sh d -> tensor sh <> dim d
  -- A point and a chart take a frame (design §3.10, F4): `Point degC`,
  -- `Chart lvlh`, `Point c`; so do the amounts between its points, `Diff
  -- c`, and the coordinates they are written with, `Coords c`, while
  -- the frame's space is not known.
  TPoint f -> paren (prec > 10) ("Point " <> frameName f)
  TChart f -> paren (prec > 10) ("Chart " <> frameName f)
  TOver f Nothing -> paren (prec > 10) ("Diff " <> frameName f)
  TOver f (Just _) -> paren (prec > 10) ("Coords " <> frameName f)
  -- A unit (design §3.10, U1) takes its dimension as `Num` does: `Unit m`,
  -- `Unit (m/s)`, and `Unit` alone when dimensionless.
  TUnit d -> paren (prec > 10 && not (isDimOne d)) ("Unit" <> dim d)
  -- A quantity of a role variable (design §3.10, U9): `Quantity r d`, and
  -- `Quantity r` when dimensionless. A role variable's shape is `[]` once
  -- it is generalised; before, in an error, one of another shape prints
  -- as the amount it can only be.
  TQty r SNil d -> paren (prec > 10) ("Quantity " <> roleText varName r <> dim d)
  TQty _ sh d
    | prec > 10 -> "(" <> tensor sh <> dim d <> ")"
    | otherwise -> tensor sh <> dim d
  -- A declared type prints by its short hash here; the driver replaces that
  -- with the current name (design §7.2), so inference needs no name table.
  -- An axis argument, a length's companion, prints with its length (design
  -- §3.9).
  TData h as0 ->
    let as = withCompanions as0
     in paren
          (prec > 10 && not (null as))
          (T.unwords (typeName h : map argWith as))
  TFun a b ->
    paren
      (prec > 0)
      ( renderWithNamed typeName spelling axes names 1 a
          <> arrowText spelling
          <> renderWithNamed typeName spelling axes names 0 b
      )
  TVar v -> Map.findWithDefault ("t" <> T.pack (show v)) v names
 where
  paren b s = if b then "(" <> s <> ")" else s
  -- A position prints its length, unless its axes are named or print by
  -- a binder's name (design §3.9, decision 6).
  position bare (l, a) = case a of
    ANamed h -> typeName h
    AVar x
      | Map.notMember x axes.absorbed
      , Just n <- Map.lookup x axes.own ->
          n
    _ -> (if bare then renderLenBare else renderLen) names l
  frameName f = case f.slot of
    FrNamed h -> typeName h
    FrVar v -> Map.findWithDefault ("f" <> T.pack (show v)) v names
  tensor = \case
    SNil -> "Num"
    SCons n a SNil -> "Vec " <> position False (n, a)
    SCons m a (SCons n b SNil) -> "Mat " <> position False (m, a) <> " " <> position False (n, b)
    sh -> "Tensor " <> renderShapeWith (position True) names sh
  -- A dimension is a type argument (design §4.1): one name to the first
  -- power bare (@Num m@, @Num d@), anything else parenthesised (@Num
  -- (m/s^2)@, @Num (d·d1)@).
  dim d
    | isDimOne d = ""
    | otherwise = " " <> renderDimArgIn spelling dimName d
  dimName v = Map.findWithDefault ("d" <> T.pack (show v)) v names
  varName v = Map.findWithDefault ("r" <> T.pack (show v)) v names
  argWith = \case
    (ARole r, _) -> roleText varName r
    (AType t, _) -> renderWithNamed typeName spelling axes names 11 t
    (ALen l, Just x) -> position False (l, x)
    (ALen l, Nothing) -> renderLen names l
    (AShape sh, _) -> renderShapeWith (position True) names sh
    (ADim d, _) -> renderDimArgIn spelling dimName d
    (AAxis _, _) -> ""
    (AFrame (FrNamed h), _) -> typeName h
    (AFrame (FrVar v), _) -> Map.findWithDefault ("f" <> T.pack (show v)) v names
    (ASpace (SpNamed h), _) -> typeName h
    (ASpace (SpVar v), _) -> Map.findWithDefault ("sp" <> T.pack (show v)) v names

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
renderShapeList names = renderShapeWith (renderLenBare names . fst) names

-- | 'renderShapeList', each position printed by the given function.
renderShapeWith :: ((Len, Axis) -> Text) -> Map VarId Text -> Shape -> Text
renderShapeWith position names sh = case (tailVar sh, lens sh) of
  (Nothing, ls) -> "[" <> T.intercalate ", " (map position ls) <> "]"
  (Just v, []) -> shapeName v
  (Just v, ls) ->
    "("
      <> T.intercalate " : " (map position ls ++ [shapeName v])
      <> ")"
 where
  lens = \case
    SNil -> []
    SCons l a rest -> (l, a) : lens rest
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
      ++ zip
        [v | (v, KFrame) <- vs]
        ("c" : ["c" <> T.pack (show i) | i <- [1 :: Int ..]])
      ++ zip [v | (v, KSpace) <- vs] ["sp" <> T.pack (show i) | i <- [1 :: Int ..]]
      ++ zip [v | (v, KRole) <- vs] ("r" : ["r" <> T.pack (show i) | i <- [1 :: Int ..]])

idNames :: [(VarId, Kind)] -> Map VarId Text
idNames vs = Map.fromList [(v, prefix k <> T.pack (show v)) | (v, k) <- vs]
 where
  prefix = \case
    KType -> "t"
    KLen -> "n"
    KShape -> "s"
    KDim -> "d"
    KAxis -> "x"
    KFrame -> "f"
    KSpace -> "sp"
    KRole -> "r"

{- | A role as it is written (design §3.10, U9): @Amount@, @Unit@, or its
variable's name.
-}
roleText :: (VarId -> Text) -> Role -> Text
roleText name = \case
  RAmount -> "Amount"
  RUnit -> "Unit"
  RVar v -> name v

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
arguments would do, because a field is a function or a chart, or the type
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
  -- A role parameter that needs equality asks for an amount (design §3.10,
  -- U9): equality takes amounts.
  Just
    ( [t | (True, AType t) <- zip need as]
        ++ [TQty r SNil dimOne | (True, ARole r) <- zip need as]
    )
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
    -- A quantity whose role is a parameter has equality when that role is
    -- an amount's (design §3.10, U9).
    TQty (RVar v) _ _ -> Just [v]
    TPoint _ -> Just []
    TOver _ _ -> Just []
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
renderTypeDef _ name _ _ def
  -- A chart's minted axis type (design §3.9) is no declaration: its chart
  -- is, and lists as the axes of that chart.
  | isAxesDef def = "axes " <> name
  -- A chart's frame (design §3.10, F3) lists as the frame of that chart.
  | Just _ <- frameDefMoving def = "frame " <> name
-- A space (design §3.10, F2) reads back as its declaration.
renderTypeDef spelling name _ _ def
  | SpaceLabel _ <- def.label
  , [[], [TTensor sh d]] <- def.constructors =
      "space "
        <> name
        <> " = "
        <> renderWithNamed
          showHash
          spelling
          noAxisNames
          Map.empty
          0
          (TTensor (anonymous sh) d)
 where
  anonymous = \case
    SCons l _ rest -> SCons l AAnon (anonymous rest)
    sh -> sh
renderTypeDef spelling name conNames fieldNames def =
  (if def.label == structuralLabel then "structural " else "")
    <> "data "
    -- An axis parameter, a length's companion, is not written (design §3.9).
    <> T.unwords
      (name : [Map.findWithDefault "?" v names | (v, _) <- writtenParams def.params])
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
      noAxisNames
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
