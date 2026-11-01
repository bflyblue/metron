-- | Check kinds and resolve surface type syntax in declarations, signatures, and queries.
module Metron.Type.Syntax (
  enterData,
  enterSpace,
  queryScheme,
  signatureScheme,
  explicitScheme,
  Bound,
  BoundVar,
  renumberBound,
  tyNames,
) where

import Control.Monad (when, zipWithM)
import Control.Monad.State.Strict (
  StateT,
  gets,
  lift,
  modify,
  runStateT,
 )
import Data.Bifunctor (bimap)
import Data.Char (isLower)
import Data.Foldable (foldlM)
import Data.Map.Strict qualified as Map (
  Map,
  elems,
  empty,
  findWithDefault,
  fromList,
  insert,
  keys,
  lookup,
  map,
  mapMaybe,
  member,
  notMember,
  toList,
  withoutKeys,
 )
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as Set (
  empty,
  filter,
  fromList,
  insert,
  member,
  toList,
 )
import Data.Text (Text)
import Data.Text qualified as T (intercalate, pack, uncons)
import Metron.Builtin (
  axesDef,
  axesHash,
  boolHash,
  boolT,
  frameDefMoving,
  isSpaceDef,
  listT,
  mintedPath,
  spaceDef,
  spaceOf,
  tupleT,
 )
import Metron.Codebase (
  Codebase (uses),
  addTypeDef,
  bindConName,
  bindFieldName,
  bindTypeName,
  isChartName,
  isUnitName,
  lookupName,
  lookupTypeDef,
  lookupTypeName,
  typeNameOf,
  typeOf,
 )
import Metron.Core (Hash, Label (Owner), lengthLimit, showHash)
import Metron.Dimension (
  Dim,
  baseSymbol,
  dimBase,
  dimMul,
  dimOne,
  dimPow,
  dimVar,
 )
import Metron.Hash (hashTypeDef)
import Metron.NameResolution (
  LabelKind (TermLabel, TypeLabel),
  Qualified (..),
  isLabel,
  qualifyName,
  qualifyWith,
  shortestNameOf,
 )
import Metron.Resolve.Error (ResolveError (DataError))
import Metron.Syntax qualified as S (
  DataDecl (constructors, name, params, structural),
  FieldDecl (FieldDecl, ty),
  Name (..),
  Scope,
  TyBinder (name, over, size, space),
  TyExpr (node, span),
  TyNode (
    TyApp,
    TyDim,
    TyForall,
    TyFun,
    TyInt,
    TyList,
    TyName,
    TyShape,
    TyShapeCons,
    TyTuple
  ),
  juxtaposedHint,
  lastSegment,
 )
import Metron.Type (
  Arg (..),
  Axis (AAnon, AVar),
  Frame (..),
  FrameSlot (FrNamed, FrVar),
  Kind (..),
  Len (LLit, LVar),
  Scheme (..),
  Shape (..),
  Space (..),
  SpaceSlot (SpVar),
  Type (TChart, TData, TFun, TPoint, TTensor, TUnit, TVar),
  TypeDef (TypeDef, params),
  VarId,
  freeVars,
  numT,
  overType,
  rankLen,
  selfType,
  structuralLabel,
  substOnce,
  varArg,
  writtenParams,
 )

{- | A written lowercase name that names nothing a type can name (design
§7.3, §4.8): not @rank@, a built-in or declared type, a base unit or a
unit, in the scope. A @:ls@ query reads it as a variable; a signature or
an ascription refuses it unless a @forall@ binds it.
-}
typeVariable :: S.Scope -> Codebase -> Text -> Bool
typeVariable scope cb n =
  maybe False (isLower . fst) (T.uncons n)
    && n `notElem` ("rank" : builtinTypeNames)
    && qualifyName TypeLabel scope cb n == NotFound
    && n `notElem` [baseSymbol b | b <- [minBound .. maxBound]]
    && not isUnit
 where
  -- A chart's name is a unit's kin: a rescaling, whose frame is its
  -- parent's, is refused as such where a frame goes (design §3.10, F3).
  isUnit = case qualifyName TermLabel scope cb n of
    Found u -> isUnitName u cb || isChartName u cb
    _ -> False

-- Data declarations ----------------------------------------------------------------

{- | Enter a @data@ declaration (design §2.3). The parameters take their
kinds from the positions the fields use them in; the field types are
checked against the types in scope; the definition is hashed and stored,
and the type's and constructors' names bound to it.
-}
enterData :: S.Scope -> Codebase -> S.DataDecl -> Either ResolveError Codebase
enterData scope cb decl = do
  distinct "parameter" decl.params
  case [p | p <- decl.params, p.text == "rank"] of
    p : _ ->
      Left
        ( DataError
            p.span
            "`rank` is the type function on shapes and cannot be a parameter"
        )
    [] -> pure ()
  distinct "constructor" (map fst decl.constructors)
  distinct "field" (map fst fieldLabels)
  -- Field names make a record: a type of one constructor, so that @r.f@ is total.
  case (decl.constructors, fieldLabels) of
    (_ : _ : _, (n, _) : _) ->
      Left (DataError n.span "field names need a type with one constructor")
    _ -> pure ()
  -- Two passes: the first learns the parameters' kinds from where they
  -- appear, the second converts with the kinds known, so that the
  -- arguments of a recursive occurrence can be read by their kinds, and
  -- each length parameter with its companion axis parameter (design §3.9),
  -- each frame parameter with its axes and space (design §3.10).
  let preset =
        Map.fromList
          [ (p, KFrame)
          | p <- concatMap (framesNamed . (.ty)) (concatMap snd decl.constructors)
          , p `elem` env.paramNames
          ]
  (_, kinds1) <- runStateT (convertAll env) preset
  case [p | p <- decl.params, Map.member (vectorKey p.text) kinds1] of
    p : _ ->
      Left
        ( DataError
            p.span
            ( "the axes of the frame parameter `"
                <> p.text
                <> "` cannot be written in a declaration: no type says how many it has"
            )
        )
    [] -> pure ()
  let written = [(p, Map.findWithDefault KType p kinds1) | p <- env.paramNames]
      comps = companionsOf (length written) written Map.empty Set.empty env.params
  (fieldss, kinds) <-
    runStateT
      (convertAll (env :: DataEnv){axisOf = comps.compAxes, frames = comps.compFrames})
      kinds1
  let params =
        [(i, Map.findWithDefault KType p.text kinds) | (i, p) <- zip [0 ..] decl.params]
          ++ comps.compVars
      def =
        TypeDef
          params
          fieldss
          -- The declared full path (design §2.3, §7.6): @a.Body@ and
          -- @b.Body@ with the same fields are two types.
          ( if decl.structural
              then structuralLabel
              else Owner decl.name.text
          )
      h = hashTypeDef def
      cb' = bindTypeName decl.name.text h (addTypeDef h def cb)
  -- A built-in type's name is reserved, except that @Bool@ may name the
  -- declaration it is (design §7.7): the library's, or an equal one.
  when (S.lastSegment decl.name.text `elem` builtinTypeNames && h /= boolHash)
    $ Left
      ( DataError
          decl.name.span
          ("`" <> S.lastSegment decl.name.text <> "` is a built-in type")
      )
  let
    withCons =
      foldl
        (\acc (i, (c, _)) -> bindConName c.text h i acc)
        cb'
        (zip [0 ..] decl.constructors)
  pure
    (foldl (\acc (n, j) -> bindFieldName n.text h 0 j acc) withCons fieldLabels)
 where
  env = emptyEnv cb scope decl.name (map (.text) decl.params)
  convertAll e = mapM (mapM (tyType e . (.ty)) . snd) decl.constructors
  fieldLabels =
    [ (n, j)
    | (_, fs) <- decl.constructors
    , (j, S.FieldDecl (Just n) _) <- zip [0 :: Int ..] fs
    ]
  distinct what = go Set.empty
   where
    go _ [] = Right ()
    go seen (n : ns)
      | n.text `Set.member` seen =
          Left (DataError n.span (what <> " `" <> n.text <> "` appears twice"))
      | otherwise = go (Set.insert n.text seen) ns

{- | Enter a space's declaration (design §3.10, F2): a nominal space of the
amounts of a type, a number or a vector of literal length, minted as a
type stamped with its full path, beside its base axes for a vector space,
and named as declared.
-}
enterSpace ::
  S.Scope -> Codebase -> S.Name -> S.TyExpr -> Either ResolveError Codebase
enterSpace scope cb n t = do
  ty <- fst <$> runStateT (tyType (emptyEnv cb scope n []) t) Map.empty
  (lens, d) <- case ty of
    TTensor SNil d -> Right ([], d)
    TTensor (SCons (LLit k) AAnon SNil) d -> Right ([k], d)
    _ ->
      Left
        (DataError t.span "a space is of numbers or of vectors, as in Num K or Vec 3 m")
  when (S.lastSegment n.text `elem` builtinTypeNames)
    $ Left (DataError n.span ("`" <> S.lastSegment n.text <> "` is a built-in type"))
  let def = spaceDef n.text lens d
      h = hashTypeDef def
      withBase =
        if null lens
          then id
          else addTypeDef (axesHash n.text) (axesDef n.text)
  pure (bindTypeName n.text h (withBase (addTypeDef h def cb)))

builtinTypeNames :: [Text]
builtinTypeNames =
  [ "Bool"
  , "Num"
  , "Unit"
  , "Quantity"
  , "Amount"
  , "Vec"
  , "Mat"
  , "Tensor"
  , "Point"
  , "Chart"
  , "Diff"
  , "Coords"
  ]

data DataEnv = DataEnv
  { codebase :: Codebase
  , scope :: S.Scope
  -- ^ where the type is written: its names resolve through this (design §7.6)
  , self :: S.Name
  -- ^ the type being declared, by its full path
  , params :: Map.Map Text VarId
  , paramNames :: [Text]
  , axisOf :: Map.Map Text VarId
  -- ^ each length parameter's companion axis parameter (design §3.9)
  , sized :: Map.Map Text Int
  -- ^ the length of each sized @forall@ binder, @(a : 3)@ (design §3.9)
  , frames :: Map.Map Text Frame
  -- ^ each frame variable's frame, with its companions (design §3.10, F1)
  , spaces :: Map.Map Text Space
  -- ^ each space variable's space, with its companions
  }

-- | An environment for a type with the given parameters, numbered in order.
emptyEnv :: Codebase -> S.Scope -> S.Name -> [Text] -> DataEnv
emptyEnv cb scope self ps =
  DataEnv
    { codebase = cb
    , scope = scope
    , self = self
    , params = Map.fromList (zip ps [0 ..])
    , paramNames = ps
    , axisOf = Map.empty
    , sized = Map.empty
    , frames = Map.empty
    , spaces = Map.empty
    }

{- | The companions of written variables with their kinds (design §3.9,
§3.10), numbered on from the given id: an axis set for each length; for
each space its shape, dimension and base axes; and for each frame its
axes and its space, the one its binder names (a declared one, or a space
variable) or one of its own. A frame or space whose axes are written as a
length has a space of one axis set, of a length of its own.
-}
data Companions = Companions
  { compAxes :: Map.Map Text VarId
  , compFrames :: Map.Map Text Frame
  , compSpaces :: Map.Map Text Space
  , compVars :: [(VarId, Kind)]
  }

companionsOf ::
  Int ->
  [(Text, Kind)] ->
  Map.Map Text (Either Space Text) ->
  Set Text ->
  Map.Map Text VarId ->
  Companions
companionsOf next written annotated vector ids = Companions axes frameMap spaceMap (reverse vs3)
 where
  idOf n = Map.findWithDefault 0 n ids
  -- Lengths' axes first, in order, then spaces', then frames'.
  (axes, k1, vs1) =
    foldl
      (\(m, k, vs) n -> (Map.insert n k m, k + 1, (k, KAxis) : vs))
      (Map.empty, next, [])
      [n | (n, KLen) <- written]
  (spaceMap, k2, vs2) =
    foldl
      ( \(m, k, vs) n ->
          let (sp, k', new) = freshSpace (SpVar (idOf n)) (Set.member n vector) k
           in (Map.insert n sp m, k', reverse new ++ vs)
      )
      (Map.empty, k1, vs1)
      [n | (n, KSpace) <- written]
  (frameMap, _, vs3) =
    foldl
      ( \(m, k, vs) n ->
          let (sp, k', new) = case Map.lookup n annotated of
                Just (Left named) -> (named, k + 1, [])
                Just (Right s) | Just sp' <- Map.lookup s spaceMap -> (sp', k + 1, [])
                _ -> freshSpace (SpVar (k + 1)) (Set.member n vector) (k + 2)
              spVars = case Map.lookup n annotated of
                Just _ -> []
                Nothing -> [(k + 1, KSpace)]
           in ( Map.insert n (Frame (FrVar (idOf n)) (AVar k) sp) m
              , k'
              , reverse new ++ reverse spVars ++ (k, KAxis) : vs
              )
      )
      (Map.empty, k2, vs2)
      [n | (n, KFrame) <- written]
  -- A space of its own: its shape (one axis set of a length of its own, if
  -- its axes are written), dimension and base axes.
  freshSpace slot isVector k =
    let (shape, shapeVar, k')
          | isVector = (SCons (LVar k 0) AAnon SNil, (k, KLen), k + 1)
          | otherwise = (SVar k, (k, KShape), k + 1)
     in ( Space slot shape (dimVar k') (AVar (k' + 1))
        , k' + 2
        , [shapeVar, (k', KDim), (k' + 1, KAxis)]
        )

-- | Conversion of written types, learning the parameters' kinds.
type Kinds = StateT (Map.Map Text Kind) (Either ResolveError)

{- | Where a variable's axes are written as a length (design §3.10, F4):
recorded beside the kinds, so that its space is one of one axis set.
-}
vectorKey :: Text -> Text
vectorKey = ("§vec:" <>)

bad :: S.TyExpr -> Text -> Kinds a
bad t msg = lift (Left (DataError t.span msg))

kindNoun :: Kind -> Text
kindNoun = \case
  KType -> "a type"
  KLen -> "a length"
  KShape -> "a shape"
  KDim -> "a dimension"
  KAxis -> "an axis set"
  KFrame -> "a frame"
  KSpace -> "a space"

-- | A parameter used at a kind: record it, or report the clash.
useParam :: DataEnv -> S.TyExpr -> Text -> Kind -> Kinds VarId
useParam env t p k = do
  known <- gets (Map.lookup p)
  case known of
    Just k'
      | k' /= k ->
          bad
            t
            ( "parameter `"
                <> p
                <> "` is used both as "
                <> kindNoun k'
                <> " and as "
                <> kindNoun k
            )
    _ -> do
      modify (Map.insert p k)
      pure (Map.findWithDefault 0 p env.params)

{- | The names a written type uses where a frame goes (design §3.10, F4):
after @Point@, @Chart@, @Diff@ and @Coords@.
-}
framesNamed :: S.TyExpr -> [Text]
framesNamed e = case e.node of
  S.TyApp hd [a]
    | hd.text `elem` ["Point", "Chart", "Diff", "Coords"]
    , S.TyName n <- a.node ->
        [n]
  S.TyApp _ args -> concatMap framesNamed args
  S.TyTuple ts -> concatMap framesNamed ts
  S.TyList a -> framesNamed a
  S.TyFun a b -> framesNamed a ++ framesNamed b
  S.TyForall _ a -> framesNamed a
  _ -> []

tyType :: DataEnv -> S.TyExpr -> Kinds Type
tyType env t = case t.node of
  S.TyName n
    | Map.member n env.params -> TVar <$> useParam env t n KType
    | n == "Bool" -> pure boolT
    | n == "Num" -> pure numT
    | n == "Unit" ->
        bad t "units are syntax, not value types; pass an amount such as 1 km"
    | n == "Amount" ->
        bad t "Amount is not a type: an amount is Num d, or Tensor s d"
    | n `elem` builtinTypeNames -> bad t ("`" <> n <> "` needs its arguments")
    | otherwise -> applied env t n []
  S.TyApp hd args
    | hd.text == "rank" ->
        bad
          t
          "rank s is a length, not a type; write it where a length goes, as in Vec (rank s)"
    | Map.member hd.text env.params ->
        bad t ("parameter `" <> hd.text <> "` takes no arguments")
    | otherwise -> case (hd.text, args) of
        ("Num", [d]) -> TTensor SNil <$> tyDim env d
        -- A unit takes its dimension as Num does (design §3.10, U1).
        ("Unit", _) -> bad t "units are syntax, not value types; pass an amount such as 1 km"
        -- No written type names a unit, or ranges over units and amounts
        -- (design §3.10, U9).
        ("Quantity", _) -> bad t "quantities are amounts: use Num d or Tensor s d"
        ("Vec", [n]) -> (\l -> TTensor (position l SNil) dimOne) <$> tyLen env n
        ("Vec", [n, d]) -> (\l -> TTensor (position l SNil)) <$> tyLen env n <*> tyDim env d
        ("Mat", [m, n]) ->
          (\a b -> TTensor (position a (position b SNil)) dimOne)
            <$> tyLen env m
            <*> tyLen env n
        ("Mat", [m, n, d]) ->
          (\a b -> TTensor (position a (position b SNil)))
            <$> tyLen env m
            <*> tyLen env n
            <*> tyDim env d
        ("Tensor", [sh]) -> (`TTensor` dimOne) <$> tyShape env sh
        ("Tensor", [sh, d]) -> TTensor <$> tyShape env sh <*> tyDim env d
        -- A point and a chart take a frame (design §3.10, F4), and so do
        -- the amounts between its points and its coordinates.
        ("Point", [a]) -> TPoint <$> tyFrame env a
        ("Chart", [a]) -> TChart <$> tyFrame env a
        ("Diff", [a]) -> (`overType` Nothing) <$> tyFrame env a
        ("Coords", [a]) -> (`overType` Just dimOne) <$> tyFrame env a
        (n, _)
          | n `elem` builtinTypeNames ->
              bad t ("`" <> n <> "` does not take these arguments")
        (n, _) -> applied env t n args
  S.TyTuple ts -> tupleT <$> mapM (tyType env) ts
  S.TyList a -> listT <$> tyType env a
  S.TyFun a b -> TFun <$> tyType env a <*> tyType env b
  S.TyInt _ -> bad t "a number is a length, not a type"
  S.TyShape _ -> bad t "a bracket is a shape, not a type"
  S.TyShapeCons _ _ -> bad t "a shape is not a type; write Tensor (n : s) d"
  S.TyDim _ -> bad t "a dimension is not a type: a quantity of it is Num (m/s)"
  S.TyForall _ _ -> bad t "forall goes only at the head of a signature or an ascription"

{- | A frame (design §3.10, F4): a frame variable, with its companions, or
a chart's name, which names the frame it minted, read off the chart's
type. A space, a rescaling's name or a type are refused with what to write.
-}
tyFrame :: DataEnv -> S.TyExpr -> Kinds Frame
tyFrame env a = case a.node of
  S.TyName p | Map.member p env.params -> do
    v <- useParam env a p KFrame
    pure
      ( fromMaybe
          (Frame (FrVar v) AAnon (Space (SpVar v) SNil dimOne AAnon))
          (Map.lookup p env.frames)
      )
  S.TyName n -> case namedType env n of
    Found full
      | Just (h, def) <- typeAt env full
      , Just _ <- frameDefMoving def ->
          maybe
            (bad a ("the frame `" <> n <> "` has no chart to read it from"))
            pure
            (chartFrameOf env.codebase h def)
      | Just (_, def) <- typeAt env full
      , isSpaceDef def ->
          bad
            a
            ("`" <> n <> "` is a space; a point is on a frame of it, as in Point degC")
      | otherwise -> bad a ("`" <> n <> "` is a type, not a frame")
    Ambiguous fulls -> ambiguousType a n fulls
    NotFound -> case qualifyName TermLabel env.scope env.codebase n of
      Found c
        | isChartName c env.codebase
        , Just r <- lookupName c env.codebase
        , Just (Forall _ t) <- typeOf r env.codebase
        , Just (FrNamed h) <- (.slot) <$> chartTypeFrame t ->
            bad
              a
              ( "`"
                  <> n
                  <> "` is a rescaling and shares the frame of its parent: write Point "
                  <> maybe
                    (showHash h)
                    (shortestNameOf TypeLabel env.scope env.codebase)
                    (typeNameOf h env.codebase)
              )
      _ -> bad a ("unknown frame `" <> n <> "` in a type")
  _ ->
    bad
      a
      "a point and a chart are typed by a frame, a chart's name or a variable, as in Point degC"

-- | The frame of a chart's type, after any parameters.
chartTypeFrame :: Type -> Maybe Frame
chartTypeFrame = \case
  TFun _ r -> chartTypeFrame r
  TChart f -> Just f
  _ -> Nothing

{- | A minted frame as a type (design §3.10, F3), read off the type of the
chart at its path.
-}
chartFrameOf :: Codebase -> Hash -> TypeDef -> Maybe Frame
chartFrameOf cb h def = do
  path <- mintedPath def
  r <- lookupName path cb
  Forall _ t <- typeOf r cb
  f <- chartTypeFrame t
  if f.slot == FrNamed h then Just f else Nothing

-- | A type name through the scope.
namedType :: DataEnv -> Text -> Qualified
namedType env = qualifyWith env.codebase.uses (isLabel TypeLabel env.codebase) env.scope

typeAt :: DataEnv -> Text -> Maybe (Hash, TypeDef)
typeAt env full = do
  h <- lookupTypeName full env.codebase
  (h,) <$> lookupTypeDef h env.codebase

ambiguousType :: S.TyExpr -> Text -> [Text] -> Kinds a
ambiguousType a n fulls =
  bad
    a
    ( "`"
        <> n
        <> "` is both "
        <> T.intercalate " and " (map (\f -> "`" <> f <> "`") fulls)
        <> "; write one of them"
    )

-- | A declared type, or the one being declared, applied to its arguments.
applied :: DataEnv -> S.TyExpr -> Text -> [S.TyExpr] -> Kinds Type
applied env t n args
  | resolved == Found env.self.text = do
      arity (length env.paramNames)
      kinds <- mapM (gets . Map.findWithDefault KType) env.paramNames
      TData selfType <$> argsAt env kinds args
  | Found full <- resolved
  , Just (_, def) <- typeAt env full
  , isSpaceDef def || isJust (frameDefMoving def) =
      bad
        t
        ( "`"
            <> n
            <> "` is "
            <> (if isSpaceDef def then "a space" else "a frame")
            <> ", not a type: a point on a frame is Point c, an amount along its axes Vec "
            <> n
            <> " m"
        )
  | Found full <- resolved
  , Just (h, def) <- typeAt env full = do
      let written = writtenParams def.params
      arity (length written)
      TData h <$> argsAt env (map snd written) args
  | Ambiguous fulls <- resolved = ambiguousType t n fulls
  | otherwise = bad t ("unknown type `" <> n <> "`")
 where
  -- The type's own name exists before it is entered.
  resolved =
    qualifyWith
      env.codebase.uses
      (\x -> x == env.self.text || isLabel TypeLabel env.codebase x)
      env.scope
      n
  arity k =
    when (length args /= k)
      $ bad
        t
        ( "`"
            <> n
            <> "` takes "
            <> T.pack (show k)
            <> (if k == 1 then " argument" else " arguments")
            <> ", given "
            <> T.pack (show (length args))
        )

{- | The arguments of a declared type at its written parameters' kinds:
the written arguments in order, then the companions (design §3.9,
§3.10): the axes of each length argument, then each frame argument's
axes and space.
-}
argsAt :: DataEnv -> [Kind] -> [S.TyExpr] -> Kinds [Arg]
argsAt env kinds args = do
  converted <- zipWithM (argOf env) kinds args
  pure
    ( map fst converted
        ++ [AAxis ax | (_, LenAxes ax) <- converted]
        ++ concat
          [ [ AAxis f.axes
            , ASpace f.space.slot
            , AShape f.space.shape
            , ADim f.space.dim
            , AAxis f.space.base
            ]
          | (_, FrameOf f) <- converted
          ]
    )

-- | What an argument brings with it: a length its axes, a frame itself.
data Companion = NoCompanion | LenAxes Axis | FrameOf Frame

-- | An argument at a written parameter's kind, with its companions.
argOf :: DataEnv -> Kind -> S.TyExpr -> Kinds (Arg, Companion)
argOf env k a = case k of
  KType -> (,NoCompanion) . AType <$> tyType env a
  KLen -> bimap ALen LenAxes <$> tyLen env a
  KShape -> (,NoCompanion) . AShape <$> tyShape env a
  KDim -> (,NoCompanion) . ADim <$> tyDim env a
  KFrame -> (\f -> (AFrame f.slot, FrameOf f)) <$> tyFrame env a
  KAxis -> bad a "an axis set cannot be written"
  KSpace -> bad a "a space is written as a frame's: (c : ITS90)"

-- | A position of a shape: a length and its axes.
position :: (Len, Axis) -> Shape -> Shape
position = uncurry SCons

{- | A written length and the axes it means (design §3.9): a literal is
that many anonymous axes, a parameter a whole axis set (its length and
its companion axis parameter), and @rank s@ anonymous, as an index's
positions are numbers. A frame variable means its axes, and a space
variable its base axes, as many as its space has (design §3.10, F4).
-}
tyLen :: DataEnv -> S.TyExpr -> Kinds (Len, Axis)
tyLen env a = case a.node of
  S.TyInt k
    | k > lengthLimit ->
        bad
          a
          ( "a length of "
              <> T.pack (show k)
              <> ": a tensor has at most "
              <> "2^40"
              <> " components"
          )
    | k >= 0 -> pure (LLit (fromInteger k), AAnon)
  S.TyName p | Map.member p env.params -> do
    known <- gets (Map.lookup p)
    case known of
      Just KFrame -> do
        modify (Map.insert (vectorKey p) KLen)
        pure $ case Map.lookup p env.frames of
          Just f -> (spaceLength f.space, f.axes)
          Nothing -> (LLit 0, AAnon)
      Just KSpace -> do
        modify (Map.insert (vectorKey p) KLen)
        pure $ case Map.lookup p env.spaces of
          Just sp -> (spaceLength sp, sp.base)
          Nothing -> (LLit 0, AAnon)
      _ -> do
        v <- useParam env a p KLen
        -- A sized binder is its literal length beside its own axes.
        let len = maybe (LVar v 0) LLit (Map.lookup p env.sized)
        pure (len, maybe AAnon AVar (Map.lookup p env.axisOf))
  -- The one type-level function (design §4.1): the rank of a shape.
  S.TyApp hd [sh] | hd.text == "rank" -> (,AAnon) . rankLen <$> tyShape env sh
  S.TyName "rank" -> bad a "rank takes a shape: rank s"
  S.TyApp hd _ | hd.text == "rank" -> bad a "rank takes one shape: rank s"
  S.TyName n -> namedAxes env a n
  _ ->
    bad
      a
      "a length is a number, a parameter, a frame's or a space's axes, or rank s"

-- | The length of a space of one axis set.
spaceLength :: Space -> Len
spaceLength sp = case sp.shape of
  SCons l _ _ -> l
  _ -> LLit 0

{- | A name in a length position (design §3.10, F4): a frame's axes, as
many as its space has, or a space's base axes. @Vec lvlh m@ is a
three-vector along lvlh's axes, @Vec GCRS m@ along GCRS's base.
-}
namedAxes :: DataEnv -> S.TyExpr -> Text -> Kinds (Len, Axis)
namedAxes env a n = case namedType env n of
  Found full
    | Just (h, def) <- typeAt env full
    , Just _ <- frameDefMoving def ->
        case chartFrameOf env.codebase h def of
          Just f
            | SCons l _ SNil <- f.space.shape -> pure (l, f.axes)
          _ ->
            bad
              a
              ("the frame `" <> n <> "` has no axes: its space is not of vectors")
    | Just (h, def) <- typeAt env full
    , Just sp <- spaceOf h def ->
        case sp.shape of
          SCons l _ SNil -> pure (l, sp.base)
          _ -> bad a ("the space `" <> n <> "` has no axes: it is a space of numbers")
    | otherwise -> bad a ("`" <> n <> "` is a type, not a length or a frame's axes")
  Ambiguous fulls -> ambiguousType a n fulls
  NotFound
    | isJust (unitDim env n) ->
        bad
          a
          ( "`"
              <> n
              <> "` is a unit, not a length: a vector's length comes first, Vec 3 "
              <> n
          )
    | otherwise -> bad a ("unknown name `" <> n <> "` in a type")

tyShape :: DataEnv -> S.TyExpr -> Kinds Shape
tyShape env a = case a.node of
  S.TyShape items -> foldr position SNil <$> mapM (tyLen env) items
  S.TyShapeCons hd tl -> position <$> tyLen env hd <*> tyShape env tl
  S.TyName p | Map.member p env.params -> SVar <$> useParam env a p KShape
  _ -> bad a "a shape is a list of lengths like [2, 3], or a parameter"

{- | A dimension (design §4.1): a name, which is a variable when it is a
parameter and otherwise a unit, meaning its dimension (@Num km@ is @Num
m@); @1@; or a product of them with powers in parentheses, @(kg·m²/s²)@.
-}
tyDim :: DataEnv -> S.TyExpr -> Kinds Dim
tyDim env a = case a.node of
  S.TyInt 1 -> pure dimOne
  S.TyName n
    | Map.member n env.params -> dimVar <$> useParam env a n KDim
    | Just d <- unitDim env n -> pure d
    | otherwise -> bad a ("`" <> n <> "` is not a unit or a dimension variable")
  S.TyDim factors ->
    foldr dimMul dimOne
      <$> mapM (\(f, k) -> dimPow k <$> tyDim env f) factors
  -- `Num (m s)` reads as an application: say how to write the product.
  S.TyApp hd args
    | Just names <- mapM nameOf args -> bad a (S.juxtaposedHint (hd.text : names))
  _ ->
    bad
      a
      "a dimension is a unit, a variable, 1, or a product of them in parentheses, like (m/s^2)"
 where
  nameOf f = case f.node of
    S.TyName n -> Just n
    _ -> Nothing

-- | The dimension of a base unit or a unit in scope, by its name.
unitDim :: DataEnv -> Text -> Maybe Dim
unitDim env n
  | Just b <- lookup n [(baseSymbol b', b') | b' <- [minBound .. maxBound]] =
      Just (dimBase b)
  | Found u <- qualifyName TermLabel env.scope env.codebase n
  , isUnitName u env.codebase
  , Just r <- lookupName u env.codebase
  , Just (Forall [] (TUnit d)) <- typeOf r env.codebase =
      Just d
  | otherwise = Nothing

{- | A type written as a search query (design §7.3): every name that is not
a built-in type, a declared type, a base unit or a unit is a variable, of
the kind its position gives it. A query headed by @forall@ is read as a
signature is ('signatureScheme'); one without stays implicit, a search
pattern.
-}
queryScheme :: S.Scope -> Codebase -> S.TyExpr -> Either ResolveError Scheme
queryScheme scope cb t = case t.node of
  S.TyForall _ _ -> fst <$> signatureScheme scope cb t
  _ -> do
    let vars = Set.toList (Set.filter isVar (Set.fromList (map (.text) (tyNames t))))
        env = emptyEnv cb scope (S.Name t.span "") vars
        preset = Map.fromList [(v, KFrame) | v <- framesNamed t, v `elem` vars]
    -- As for a declaration: kinds first, then each variable with its
    -- companions (design §3.9, §3.10).
    (_, kinds1) <- runStateT (tyType env t) preset
    let written = [(v, Map.findWithDefault KType v kinds1) | v <- vars]
        comps =
          companionsOf
            (length vars)
            written
            Map.empty
            (Set.fromList [v | v <- vars, Map.member (vectorKey v) kinds1])
            env.params
    (ty, kinds) <-
      runStateT
        ( tyType
            env
              { axisOf = comps.compAxes
              , frames = comps.compFrames
              , spaces = comps.compSpaces
              }
            t
        )
        kinds1
    pure
      ( Forall
          ( [(i, Map.findWithDefault KType v kinds) | (i, v) <- zip [0 ..] vars]
              ++ comps.compVars
          )
          ty
      )
 where
  -- Names resolve through the scope (design §7.6).
  isVar = typeVariable scope cb

-- | Every name a written type uses, with its span, in order.
tyNames :: S.TyExpr -> [S.Name]
tyNames e = case e.node of
  S.TyName n -> [S.Name e.span n]
  S.TyInt _ -> []
  S.TyApp hd args -> hd : concatMap tyNames args
  S.TyTuple ts -> concatMap tyNames ts
  S.TyList a -> tyNames a
  S.TyFun a b -> tyNames a ++ tyNames b
  S.TyShape items -> concatMap tyNames items
  S.TyShapeCons hd tl -> tyNames hd ++ tyNames tl
  S.TyDim factors -> concatMap (tyNames . fst) factors
  S.TyForall bs a ->
    map (.name) bs
      ++ [s | b <- bs, Just s <- [b.space]]
      ++ concat [tyNames t | b <- bs, Just t <- [b.over]]
      ++ tyNames a

{- | The variables a @forall@ binds, by name (design §4.8): each with its
id and kind in the scheme, and its companions: for a length, its axis
variable (design §3.9) and the literal it is when the binder is sized; for
a frame its frame and for a space its space, companions and all (design
§3.10).
-}
type Bound = Map.Map Text BoundVar

data BoundVar = BoundVar
  { var :: VarId
  , kind :: Kind
  , axis :: Maybe VarId
  , size :: Maybe Int
  , frame :: Maybe Frame
  , space :: Maybe Space
  }

-- | A bound variable with every id it holds renumbered.
renumberBound :: (VarId -> VarId) -> BoundVar -> BoundVar
renumberBound f bv =
  BoundVar
    { var = f bv.var
    , kind = bv.kind
    , axis = f <$> bv.axis
    , size = bv.size
    , frame = movedFrame <$> bv.frame
    , space = movedSpace <$> bv.space
    }
 where
  moved t = substOnce (Map.fromList [(v, varArg k (f v)) | (v, k) <- freeVars t]) t
  movedFrame fr = case moved (TPoint fr) of
    TPoint fr' -> fr'
    _ -> fr
  movedSpace sp = case moved (TPoint (Frame (FrNamed selfType) AAnon sp)) of
    TPoint fr' -> fr'.space
    _ -> sp

{- | A signature's type (design §4.8, §3.9 decision 6), with the variables
its @forall@ binds. The variables are numbered in the order they first
appear, as 'canonicalScheme' numbers them, so that a signature and the
text it prints as convert to the same scheme.
-}
signatureScheme ::
  S.Scope -> Codebase -> S.TyExpr -> Either ResolveError (Scheme, Bound)
signatureScheme scope cb t = do
  (Forall _ ty, bound) <- explicitScheme scope cb Map.empty t
  let vs = freeVars ty
      renumber = Map.fromList (zip (map fst vs) [0 ..])
      moved = Map.fromList [(v, varArg k i) | ((v, k), i) <- zip vs [0 ..]]
      at v = Map.findWithDefault v v renumber
  pure
    ( Forall [(i, k) | ((_, k), i) <- zip vs [0 ..]] (substOnce moved ty)
    , Map.map (renumberBound at) bound
    )

{- | A type whose variables are bound explicitly (design §4.8, §3.9
decision 6): by its own @forall@, or, for an ascription, by the signature
of the definition it is in (the given variables, which stay free in the
scheme). Every other name is a name and resolves like one; an unknown
lowercase one is an error. A binder, or a signature's variable in an
ascription, shadows a unit, a base unit or a declared type of its name
throughout the type, dimensions included. Kinds
are learned from where the variables are used; a length variable stands
for a whole axis set, its length and a companion axis variable, and a
sized binder, @(a : 3)@, for that many axes of its own. A variable where a
frame goes is a frame, of the space its binder names, @(c : ITS90)@
or @(c : s)@, or of a space of its own (design §3.10, F1).
-}
explicitScheme ::
  S.Scope -> Codebase -> Bound -> S.TyExpr -> Either ResolveError (Scheme, Bound)
explicitScheme scope cb outer t0 = do
  let (binders, body) = case t0.node of
        S.TyForall bs b -> (bs, b)
        _ -> ([], t0)
  checkBinders Set.empty (map (.name) binders)
  let own = map (.name.text) binders
      -- Outer variables keep their ids; the type's own are numbered above them.
      base =
        1
          + maximum
            ( -1
                : concat
                  [ bv.var
                      : maybe [] pure bv.axis
                      ++ maybe [] frameIds bv.frame
                      ++ maybe [] spaceIds bv.space
                  | bv <- Map.elems outer
                  ]
            )
      ownIds = Map.fromList (zip own [base ..])
      visible = Map.withoutKeys outer (Set.fromList own)
      params = ownIds <> Map.map (.var) visible
      sizes =
        Map.fromList [(b.name.text, fromInteger k) | b <- binders, Just k <- [b.size]]
          <> Map.mapMaybe (.size) visible
      annotatedWith = [(b.name.text, s) | b <- binders, Just s <- [b.space], s.text /= "Len"]
      bareLengths =
        Set.fromList [b.name.text | b <- binders, Just s <- [b.space], s.text == "Len"]
      amounts = [(b.name.text, t) | b <- binders, Just t <- [b.over]]
  case [(b, k) | b <- binders, Just k <- [b.size], k > lengthLimit] of
    (b, k) : _ ->
      Left
        ( DataError
            b.name.span
            ( "a length of "
                <> T.pack (show k)
                <> ": a tensor has at most "
                <> "2^40"
                <> " components"
            )
        )
    [] -> pure ()
  case [ n
       | n <- concatMap tyNames (body : map snd amounts)
       , Map.notMember n.text params
       , typeVariable scope cb n.text
       ] of
    n : _ ->
      Left
        ( DataError
            n.span
            ( "unknown name `"
                <> n.text
                <> "` in a type; bind it with forall if it is a variable"
            )
        )
    [] -> pure ()
  -- A binder's space: a declared one, or a space variable bound here.
  annotations <-
    Map.fromList
      <$> sequence
        [ (n,) <$> annotation s
        | (n, s) <- annotatedWith
        ]
  let env =
        (emptyEnv cb scope (S.Name t0.span "") (Map.keys params))
          { params = params
          , axisOf = Map.mapMaybe (.axis) visible
          , sized = sizes
          , frames = Map.mapMaybe (.frame) visible
          , spaces = Map.mapMaybe (.space) visible
          }
      known =
        Map.map (.kind) visible
          <> Map.fromList [(n, KLen) | n <- Map.keys sizes]
          <> Map.fromList [(n, KLen) | n <- Set.toList bareLengths]
          <> Map.fromList [(n, KFrame) | (n, _) <- annotatedWith]
          <> Map.fromList [(n, KSpace) | (n, _) <- amounts]
          <> Map.fromList [(s, KSpace) | Right s <- Map.elems annotations]
          <> Map.fromList [(n, KFrame) | n <- framesNamed body, n `elem` own]
  -- Kinds first, then each variable with its companions.
  (_, kinds) <- runStateT (mapM (tyType env) (body : map snd amounts)) known
  let used =
        [ (n, k)
        | n <- own
        , Just k <- [Map.lookup n kinds]
        ]
      vector = Set.fromList [n | n <- own, Map.member (vectorKey n) kinds]
      rawComps = companionsOf (base + length own) used annotations vector ownIds
      comps = rawComps{compAxes = Map.withoutKeys rawComps.compAxes bareLengths}
      env' =
        env
          { axisOf = comps.compAxes <> env.axisOf
          , frames = comps.compFrames <> env.frames
          , spaces = comps.compSpaces <> env.spaces
          }
  constraints <-
    mapM (\(n, t) -> (n,) . fst <$> runStateT (tyType env' t) kinds) amounts
  constrained <- foldlM (constrainSpace amounts) comps.compSpaces constraints
  let refine sp = case sp.slot of
        SpVar v ->
          fromMaybe
            sp
            ( lookup
                v
                [(Map.findWithDefault 0 n ownIds, s) | (n, s) <- Map.toList constrained]
            )
        _ -> sp
      frames = Map.map (\f -> Frame f.slot f.axes (refine f.space)) comps.compFrames
      finalEnv = env'{spaces = constrained <> env.spaces, frames = frames <> env.frames}
  (ty, _) <- runStateT (tyType finalEnv body) kinds
  let idOf n = Map.findWithDefault 0 n ownIds
  pure
    ( Forall
        ([(idOf n, k) | (n, k) <- used, Map.notMember n sizes] ++ comps.compVars)
        ty
    , Map.fromList
        [ ( n
          , BoundVar
              (idOf n)
              k
              (Map.lookup n comps.compAxes)
              (Map.lookup n sizes)
              (Map.lookup n frames)
              (Map.lookup n constrained)
          )
        | (n, k) <- used
        ]
    )
 where
  constrainSpace amounts spaces (n, t) = case (Map.lookup n spaces, t) of
    (Just sp, TTensor sh d)
      | validShape sh -> Right (Map.insert n sp{shape = anonymous sh, dim = d} spaces)
    _ ->
      Left
        ( DataError
            (maybe t0.span (.span) (lookup n amounts))
            "a space constraint takes Num d, Vec n d or Tensor s d"
        )
  validShape = \case
    SNil -> True
    SCons _ _ SNil -> True
    SVar _ -> True
    _ -> False
  anonymous = \case
    SCons l _ rest -> SCons l AAnon (anonymous rest)
    sh -> sh
  annotation s
    | Just bv <- Map.lookup s.text outer
    , Just sp <- bv.space =
        Right (Left sp)
    | maybe False (isLower . fst) (T.uncons s.text) = Right (Right s.text)
    | otherwise = case qualifyWith cb.uses (isLabel TypeLabel cb) scope s.text of
        Found full
          | Just h <- lookupTypeName full cb
          , Just sp <- lookupTypeDef h cb >>= spaceOf h ->
              Right (Left sp)
        _ ->
          Left
            ( DataError
                s.span
                ( "`"
                    <> s.text
                    <> "` is not a space: a frame's binder names one, as in (c : ITS90)"
                )
            )
  frameIds f = map fst (freeVars (TPoint f))
  spaceIds sp = map fst (freeVars (TPoint (Frame (FrNamed selfType) AAnon sp)))
  checkBinders _ [] = Right ()
  checkBinders seen (n : ns)
    | not (maybe False (isLower . fst) (T.uncons n.text)) || n.text == "rank" =
        Left
          ( DataError
              n.span
              ("`" <> n.text <> "` cannot be a type variable; a variable is a lowercase name")
          )
    | Set.member n.text seen =
        Left (DataError n.span ("`" <> n.text <> "` is bound twice"))
    | otherwise = checkBinders (Set.insert n.text seen) ns
