{-# LANGUAGE PatternSynonyms #-}

{- | Hindley-Milner inference over Core (design §4.5) and elaboration to Typed
Core (§5.3) in one pass: every node is typed and rebuilt with explicit
annotations, kinded abstractions at generalisation points and kinded
applications at uses of polymorphic names. Errors carry the path of the
node that failed (§4.7).

Two primitives have relational types (§4.2): the tensor product and the
contracting product need shape concatenation, and equality is an instance
constraint over tensors and booleans. These are carried as pending
constraints, solved as soon as the shapes involved are known, and defaulted
at generalisation when they cannot be.

A length can be the rank of a shape variable plus an offset (§4.1), as in
@timap@'s index @Vec (rank s)@. Unifying such a rank with a literal or a
length variable binds a variable outright; only two ranks of different
shape variables wait, as a pending 'Rank' equation, which is an error if
it is still unsolved at generalisation.
-}
module Metron.Infer (
  TypeError (..),
  TypeLookup,
  elaborateClosed,
  elaborateClosedWith,
  readingsOf,
  rewriteReadings,
  hasReadingMarkers,
  Annotations (..),
  noAnnotations,
  matchesQuery,
) where

import Control.Monad (foldM, forM_, replicateM, unless, zipWithM, zipWithM_)
import Control.Monad.State.Strict (
  StateT,
  get,
  gets,
  modify',
  put,
  runStateT,
 )
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (first, second)
import Data.List (isSuffixOf, minimumBy, nubBy, sortOn)
import Data.Map.Strict qualified as Map (
  Map,
  empty,
  fromList,
  insert,
  lookup,
 )
import Data.Maybe (fromMaybe)
import Data.Monoid (Any (..))
import Data.Ord (Down (..), comparing)
import Data.Ratio (numerator)
import Data.Text (Text)
import Data.Text qualified as T (
  concat,
  intercalate,
  isPrefixOf,
  isSuffixOf,
  pack,
  unwords,
 )
import Metron.Builtin (
  boolT,
  frameDefMoving,
  pattern ConsC,
  pattern FalseC,
  pattern NilC,
  pattern TrueC,
  pattern TupleT,
 )
import Metron.Core (
  Alt (..),
  ConRef (..),
  Fin (..),
  Hash,
  Hint (..),
  Lit (LTensor),
  Nat (Z),
  NudgeKind (Stat),
  Term (..),
  Vec (..),
  foldTerm,
  lengthLimit,
  mapChildren,
  showHash,
  vecAppend,
  vecLength,
  vecMap,
  vecToList,
  vecTraverse,
  vecZip3,
  vecZipWith,
 )
import Metron.Desugar (
  Path,
  ascriptionMarker,
  isFromMarker,
  isQuantityMarker,
  isToMarker,
  unmarked,
 )
import Metron.Dimension (
  Dim,
  DimAtom (Base, DVar),
  dimAtoms,
  dimDiv,
  dimFromAtoms,
  dimInv,
  dimMul,
  dimOne,
  dimPow,
  dimVar,
  dimVars,
  isDimOne,
  renderDim,
 )
import Metron.Primitive.Types (
  StaticArg (..),
  primScheme,
  primSchemeFor,
 )
import Metron.TCore (TAlt (..), TTerm (..))
import Metron.Type (
  Arg (..),
  Axis (..),
  Frame (axes, slot, space),
  FrameSlot (..),
  Kind (..),
  Len (..),
  Scheme (..),
  Shape (..),
  Space (base, dim, shape, slot),
  SpaceSlot (..),
  Subst,
  Type (..),
  TypeDef (params),
  TypeLookup (schemesOf, typeDefOf),
  VarId,
  appendShape,
  applyArg,
  applyAxis,
  applyDim,
  applyFrame,
  applyLen,
  applyScheme,
  applyShape,
  applyType,
  closedLens,
  conText,
  dataConstructors,
  emptySubst,
  equalityArgs,
  freeVars,
  numD,
  numT,
  overType,
  rankLen,
  renderType,
  substOnce,
  vecT,
  withBuiltins,
 )

{- | A type error at a path into the term being checked. Inside a 'Cycle' the
path starts with the member index.
-}
data TypeError = TypeError {path :: Path, message :: Text}
  deriving stock (Eq, Show)

-- | Types of codebase definitions, one scheme per cycle member.

-- | A deferred relation between types (design §4.2).
data Constraint
  = -- | @s3 ~ s1 ++ s2@
    Append Shape Shape Shape
  | -- | @Eq τ@: τ is a tensor, Bool, point, or data whose components are (design §4.2)
    EqInstance Type
  | -- | lt, le, gt, ge: a number or a point (design §3.6)
    OrdInstance Type
  | -- | @rank s ~ l@, pending only while both sides are ranks of different shape variables (design §4.2)
    Rank Shape Len
  | {- | @Diff c ~ τ@, or @Coords c ~ τ@ (design §3.10, F4): pending while
    neither the frame's space's shape nor the tensor's is known
    -}
    OverIs Frame (Maybe Dim) Type
  | {- | a point converted with no @from@ is on a frame whose chart takes no
    parameters (design §3.10, F7): checked once the frame is known, and
    at run time when it never is
    -}
    Fixed Frame
  | {- | a primitive with two readings, chosen by the types it is used at
    once one of them is known (design §3.10, U4, U6)
    -}
    Dispatch Reading

{- | What a 'Dispatch' chooses between. The quantity rule and @to@ are
different operations for a unit and for a chart, so their choice is
written into the term ('rewriteReadings') and an unknown one at
generalisation is refused as ambiguous. Arithmetic has no reading to
choose: it takes amounts, with unit syntax lowered before inference.
-}
data Reading
  = {- | a quantity whose reading the desugarer left to the types, by its
    marker: the literal, what follows it, and the result; @scale@ for a
    unit, @pointOn@ for a chart (U4)
    -}
    Quantity Text (Maybe Text) Type Type Type
  | {- | a @to@ whose reading the desugarer left to the types, by its
    marker: the value, the target, and the result; the display unit's
    @to@ for a unit, @toChart@ for a point and a chart (U6), @toAxes@ for
    an amount and a chart (F10)
    -}
    Convert Text Type Type Type
  | {- | a @from … to@ (design §3.10, F7, F10), by its marker: the value,
    the source chart, the target, and the result; @fromTo@ for a point,
    @axesFromTo@ for an amount
    -}
    ConvertFrom Text Type Type Type Type

data St = St
  { subst :: Subst
  , next :: Int
  , nextAxis :: Int
  {- ^ axis variables are numbered apart, from 'axisBase', so that adding
  them (design §3.9) moves no other variable's id
  -}
  , pending :: [(Path, Constraint)]
  -- ^ reversed paths, as 'failAt' takes them
  , typeDefs :: Hash -> Maybe TypeDef
  -- ^ the declared types, for equality on them
  , annotations :: Annotations
  , chosen :: Map.Map Text Text
  {- ^ the primitive each quantity or @to@ marker was resolved to
  (design §3.10, U4, U6), by the marker's name
  -}
  }

type Infer = StateT St (Either TypeError)

{- | What the annotations of an input add to inference (design §4.8): the
signature a name carries, for a reference written under that name that
still points where the name does (the full path, the hash and the cycle
index), and the ascriptions, by the names of their markers in a term
desugared to check them ('Metron.Desugar.desugarMarked'), each with the path
an error in it is reported at ('Metron.Desugar.ascriptionPath'). Annotations
are label-level or surface syntax, never in a stored term: its types are
inferred without them.
-}
data Annotations = Annotations
  { signatureFor :: Text -> Hash -> Maybe Int -> Maybe Scheme
  , ascriptions :: Map.Map Text (Scheme, Path)
  }

-- | No annotations: what a stored term is inferred with.
noAnnotations :: Annotations
noAnnotations = Annotations (\_ _ _ -> Nothing) Map.empty

{- | Infer and elaborate a closed term: its scheme(s), one per cycle member,
and the Typed Core term with all metavariables resolved.
-}
elaborateClosed :: TypeLookup -> Term Z -> Either TypeError ([Scheme], TTerm Z)
elaborateClosed = elaborateClosedWith noAnnotations

-- | 'elaborateClosed' with the annotations of the input being checked.
elaborateClosedWith ::
  Annotations -> TypeLookup -> Term Z -> Either TypeError ([Scheme], TTerm Z)
elaborateClosedWith annots look term = fst <$> elaborating annots look term

{- | The primitive each quantity and @to@ marker of a closed term resolves
to (design §3.10, U4, U6), by its marker's name, from inference with the
given annotations: a signature read as an ascription of the body it signs
resolves the markers in it. 'rewriteReadings' writes them into the term.
-}
readingsOf ::
  Annotations -> TypeLookup -> Term Z -> Either TypeError (Map.Map Text Text)
readingsOf annots look term = snd <$> elaborating annots look term

elaborating ::
  Annotations ->
  TypeLookup ->
  Term Z ->
  Either TypeError (([Scheme], TTerm Z), Map.Map Text Text)
elaborating annots look term = do
  ((schemes, tt), st) <-
    runStateT go (St emptySubst 0 axisBase [] look.typeDefOf annots Map.empty)
  pure ((map (applyScheme st.subst) schemes, zonk st.subst tt), st.chosen)
 where
  go = case term of
    Cycle hints bodies -> do
      vars <- vecTraverse (const freshType) bodies
      let ctx = vecAppend (vecMap (Forall []) vars) VNil
      bodies' <-
        vecTraverse
          ( \(i, body, v) -> do
              (t, body') <- infer look [i] ctx body
              unify [i] v t
              pure body'
          )
          (vecZip3 (indices bodies) bodies vars)
      settle [] VNil
      schemes <- generaliseAll VNil (vecToList vars)
      s <- gets (.subst)
      let quantified = nubBy (\a b -> fst a == fst b) (concat [vs | Forall vs _ <- schemes])
          members = vecZipWith (\h v -> (h, applyType s v)) hints vars
      pure (schemes, TCycle quantified members bodies')
    _ -> do
      (t, tt) <- infer look [] VNil term
      settle [] VNil
      sc@(Forall vs _) <- generalise VNil t
      pure ([sc], abstractOver vs tt)

-- | Wrap a term in the abstractions of a scheme.
abstractOver :: [(VarId, Kind)] -> TTerm n -> TTerm n
abstractOver vs t = foldr (uncurry TTyLam) t vs

fresh :: Kind -> Infer Arg
fresh = \case
  KType -> AType . TVar <$> freshId
  KLen -> ALen . (`LVar` 0) <$> freshId
  KShape -> AShape . SVar <$> freshId
  KDim -> ADim . dimVar <$> freshId
  KAxis -> do
    st <- get
    put st{nextAxis = st.nextAxis + 1}
    pure (AAxis (AVar st.nextAxis))
  KFrame -> AFrame . FrVar <$> freshId
  KSpace -> ASpace . SpVar <$> freshId
 where
  freshId = do
    st <- get
    put st{next = st.next + 1}
    pure st.next

{- | Where axis variables are numbered from: far above any other variable
an inference run makes, so the two never meet.
-}
axisBase :: Int
axisBase = 1000000000

freshAxis :: Infer Axis
freshAxis =
  fresh KAxis >>= \case
    AAxis a -> pure a
    _ -> error "fresh KAxis"

freshDim :: Infer Dim
freshDim =
  fresh KDim >>= \case
    ADim d -> pure d
    _ -> error "fresh KDim"

freshType :: Infer Type
freshType =
  fresh KType >>= \case
    AType t -> pure t
    _ -> error "fresh KType"

freshLen :: Int -> Infer Len
freshLen offset =
  fresh KLen >>= \case
    ALen (LVar v _) -> pure (LVar v offset)
    _ -> error "fresh KLen"

freshShape :: Infer Shape
freshShape =
  fresh KShape >>= \case
    AShape s -> pure s
    _ -> error "fresh KShape"

resolve :: Type -> Infer Type
resolve t = gets (\st -> applyType st.subst t)

resolveShape :: Shape -> Infer Shape
resolveShape s = gets (\st -> applyShape st.subst s)

failAt :: Path -> Text -> Infer a
failAt p msg = lift (Left (TypeError (reverse p) msg))

tshow :: (Show a) => a -> Text
tshow = T.pack . show

-- Unification --------------------------------------------------------------------

unify :: Path -> Type -> Type -> Infer ()
unify p expected actual = do
  e <- resolve expected
  a <- resolve actual
  case (e, a) of
    _ | e == a -> pure ()
    (TVar v, t) -> bindVar p v (AType t)
    (t, TVar v) -> bindVar p v (AType t)
    (TFun a1 b1, TFun a2 b2) -> unify p a1 a2 >> unify p b1 b2
    (TupleT as, TupleT bs)
      | length as == length bs -> zipWithM_ (unify p) as bs
      | otherwise ->
          failAt
            p
            ( "expected a tuple of "
                <> tshow (length as)
                <> " components, got one of "
                <> tshow (length bs)
            )
    (TData h1 as, TData h2 bs)
      | h1 == h2 && length as == length bs -> zipWithM_ unifyArg as bs
    (TPoint f1, TPoint f2) -> unifyFrame p "points" f1 f2
    (TChart f1, TChart f2) -> unifyFrame p "charts" f1 f2
    -- A synonym still residual (design §3.10, F4): its space's shape is not
    -- known, so it unifies through the space, or waits.
    (TOver f1 m1, TOver f2 m2) -> do
      unifyAxis p f1.axes f2.axes
      unifyShape p f1.space.shape f2.space.shape
      unifyDim p (fromMaybe f1.space.dim m1) (fromMaybe f2.space.dim m2)
    -- The amount between points is an amount (design §3.10, F4).
    (TOver f md, TTensor sh d) -> overTensor p f md sh d
    (TTensor sh d, TOver f md) -> overTensor p f md sh d
    -- A unit is not an amount (design §3.10, U3, U9): `1 km` is the amount.
    (TUnit _, TTensor _ _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": an amount where a unit goes; a unit is written by its name, km or km/h"
        )
    (TTensor _ _, TUnit _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": a unit where an amount goes; one of it is written 1 km"
        )
    -- The shapes, then the dimensions, reported as the types they are in.
    (TTensor s1 d1, TTensor s2 d2) -> inTypes e a (unifyShape p s1 s2 >> unifyDim p d1 d2)
    (TUnit d1, TUnit d2) -> inTypes e a (unifyDim p d1 d2)
    (TPoint _, TTensor _ _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": a point and an amount; a point has no sum, multiple or unit; use .+ and .-, or to with a chart (design §3.6)"
        )
    (TTensor _ _, TPoint _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": an amount and a point; a point has no sum, multiple or unit; use .+ and .-, or to with a chart (design §3.6)"
        )
    _ -> failAt p ("expected " <> renderType e <> ", got " <> renderType a)
 where
  -- A mismatch inside, reported with the two types it is in.
  inTypes e a inner = do
    st <- get
    case runStateT inner st of
      Right ((), st') -> put st'
      Left (TypeError _ detail) ->
        failAt
          p
          ("expected " <> renderType e <> ", got " <> renderType a <> ": " <> detail)
  -- Arguments of a declared type, by kind; a kind mismatch cannot happen for
  -- a well-formed type, so it reports as a plain mismatch.
  unifyArg x y = case (x, y) of
    (AType t1, AType t2) -> unify p t1 t2
    (ALen l1, ALen l2) -> unifyLen p l1 l2
    (AShape s1, AShape s2) -> unifyShape p s1 s2
    (ADim d1, ADim d2) -> unifyDim p d1 d2
    (AAxis a1, AAxis a2) -> unifyAxis p a1 a2
    (AFrame f1, AFrame f2) -> unifyFrameSlot p "frames" f1 f2
    (ASpace s1, ASpace s2) -> unifySpaceSlot p s1 s2
    _ ->
      failAt p ("expected " <> renderType expected <> ", got " <> renderType actual)

{- | Two frames (design §3.10, F4, F5): one space, then one identity and one
axis set. The space comes first, so frames of two spaces are reported as
such, which no @to@ joins; two named frames of one space are two types,
reported as what the caller unifies: "points on degC and degF: convert one
with `to`".
-}
unifyFrame :: Path -> Text -> Frame -> Frame -> Infer ()
unifyFrame p what f1 f2 = do
  unifySpace p f1.space f2.space
  unifyFrameSlot p what f1.slot f2.slot
  unifyAxis p f1.axes f2.axes

unifyFrameSlot :: Path -> Text -> FrameSlot -> FrameSlot -> Infer ()
unifyFrameSlot p what x y = do
  s <- gets (.subst)
  case (slot s x, slot s y) of
    (a, b) | a == b -> pure ()
    (FrVar v, b) -> bindVar p v (AFrame b)
    (a, FrVar v) -> bindVar p v (AFrame a)
    (FrNamed h1, FrNamed h2) ->
      failAt
        p
        ( what
            <> " on "
            <> showHash h1
            <> " and "
            <> showHash h2
            <> (if what == "points" then ": convert one with `to`" else "")
        )
 where
  slot s = \case
    FrVar v | Just (AFrame b) <- Map.lookup v s -> slot s b
    b -> b

{- | Two spaces: one identity, then their companions. Two named spaces that
differ are frames of two spaces, which no conversion joins (design §3.10,
F2: a kind error).
-}
unifySpace :: Path -> Space -> Space -> Infer ()
unifySpace p s1 s2 = do
  unifySpaceSlot p s1.slot s2.slot
  unifyShape p s1.shape s2.shape
  unifyDim p s1.dim s2.dim
  unifyAxis p s1.base s2.base

unifySpaceSlot :: Path -> SpaceSlot -> SpaceSlot -> Infer ()
unifySpaceSlot p x y = do
  s <- gets (.subst)
  case (slot s x, slot s y) of
    (a, b) | a == b -> pure ()
    (SpVar v, b) -> bindVar p v (ASpace b)
    (a, SpVar v) -> bindVar p v (ASpace a)
    (SpNamed h1, SpNamed h2) ->
      failAt
        p
        ( "frames of two spaces, "
            <> showHash h1
            <> " and "
            <> showHash h2
            <> ": a point converts only to a frame of its own space"
        )
 where
  slot s = \case
    SpVar v | Just (ASpace b) <- Map.lookup v s -> slot s b
    b -> b

{- | @Diff c@ (or @Coords c@) residual against a tensor (design §3.10, F4):
the tensor's dimension is the space's, and its shape, once known, is the
space's shape along the frame's axes, which fixes the space's shape. A
tensor whose shape is not known yet waits, as a pending constraint.
-}
overTensor :: Path -> Frame -> Maybe Dim -> Shape -> Dim -> Infer ()
overTensor p f md sh d = do
  unifyDim p (fromMaybe f.space.dim md) d
  sh' <- resolveShape sh
  case closedLens sh' of
    Just ls -> do
      unifyShape p f.space.shape (foldr (\(l, _) -> SCons l AAnon) SNil ls)
      mapM_ (\(_, a) -> unifyAxis p a f.axes) ls
    Nothing -> defer p (OverIs f md (TTensor sh' d))

bindVar :: Path -> VarId -> Arg -> Infer ()
bindVar p v arg = do
  let occurs = case arg of
        AType t -> v `elem` map fst (freeVars t)
        AShape s -> v `elem` map fst (freeVars (TTensor s dimOne))
        ALen _ -> False
        ADim d -> v `elem` dimVars d
        -- A slot holds no variable but itself.
        AAxis _ -> False
        AFrame _ -> False
        ASpace _ -> False
      trivial = case arg of
        AType (TVar w) -> w == v
        AShape (SVar w) -> w == v
        ALen (LVar w 0) -> w == v
        ADim d -> d == dimVar v
        AAxis (AVar w) -> w == v
        AFrame (FrVar w) -> w == v
        ASpace (SpVar w) -> w == v
        _ -> False
  unless trivial
    $ if occurs
      then failAt p "cannot construct an infinite type"
      else modify' (\st -> st{subst = Map.insert v arg st.subst})

-- | Element-wise, with a shape variable allowed at the tail.
unifyShape :: Path -> Shape -> Shape -> Infer ()
unifyShape p x y = go x y
 where
  -- The substitution is applied at every step: unifying two lengths can
  -- bind a shape variable through its rank (design §4.1).
  go a0 b0 = do
    s0 <- gets (.subst)
    case (applyShape s0 a0, applyShape s0 b0) of
      (SNil, SNil) -> pure ()
      (SVar v, sh) -> bindVar p v (AShape sh)
      (sh, SVar v) -> bindVar p v (AShape sh)
      (SCons l1 a1 r1, SCons l2 a2 r2) ->
        unifyLen p l1 l2 >> unifyAxis p a1 a2 >> go r1 r2
      _ -> mismatch
  -- The ranks differ: say so of the whole shapes, not of the tails.
  mismatch = do
    s <- gets (.subst)
    failAt p (describe (applyShape s x) <> " against " <> describe (applyShape s y))
  describe sh = case rankOf sh of
    (0, False) -> "a number"
    (1, False) -> "a vector"
    (2, False) -> "a matrix"
    (r, False) -> "a rank-" <> tshow r <> " tensor"
    (r, True) -> "a tensor of rank at least " <> tshow r
  -- Leading lengths, and whether a shape variable follows them.
  rankOf :: Shape -> (Int, Bool)
  rankOf = \case
    SNil -> (0, False)
    SVar _ -> (0, True)
    SCons _ _ rest -> let (r, open) = rankOf rest in (r + 1, open)

{- | The name slot of a position (design §3.9) unifies syntactically:
anonymous with anonymous, a name with itself, a variable with any slot.
-}
unifyAxis :: Path -> Axis -> Axis -> Infer ()
unifyAxis p x y = do
  s <- gets (.subst)
  case (applyAxis s x, applyAxis s y) of
    (a, b) | a == b -> pure ()
    (AVar v, b) -> bindVar p v (AAxis b)
    (a, AVar v) -> bindVar p v (AAxis a)
    (a, b) -> failAt p (describe a <> " against " <> describe b <> hint a b)
 where
  -- An anonymous value meets a frame (design §3.9, decision 5).
  hint a b
    | AAnon `elem` [a, b] =
        "; give it a frame with `withAxes c v`, or `v to c` if it is along its space's base axes"
    | otherwise = ""
  describe = \case
    AAnon -> "anonymous axes"
    ANamed h -> "the axes of " <> showHash h
    AVar _ -> "an axis variable"

{- | Design §4.1: literals must agree; a variable plus offset against a
literal solves the variable when the literal is large enough; two offset
forms solve for the smaller offset.

A rank @rank s + k@ (design §4.1, §4.2) is solved through the shape: against
a literal @j@, @s@ is @j - k@ fresh lengths; against @n + m@, @n@ is @rank s
+ (k - m)@ when @k ≥ m@, and otherwise @s@ gains @m - k@ fresh leading
lengths, which is what "at least" means for a rank. Ranks of two
different shape variables are equal only by a pending 'Rank' equation.
-}
unifyLen :: Path -> Len -> Len -> Infer ()
unifyLen p x y = do
  s <- gets (.subst)
  case (applyLen s x, applyLen s y) of
    (LLit a, LLit b)
      | a == b -> pure ()
      | otherwise -> failAt p ("lengths differ: " <> tshow a <> " and " <> tshow b)
    (LVar v k, LLit j) -> bindLen v k j
    (LLit j, LVar v k) -> bindLen v k j
    (LVar v k, LVar w j)
      | v == w ->
          unless (k == j) (failAt p ("lengths differ by " <> tshow (abs (k - j))))
      | j >= k -> bindVar p v (ALen (LVar w (j - k)))
      | otherwise -> bindVar p w (ALen (LVar v (k - j)))
    (LRank v k, LLit j) -> rankIs v k j
    (LLit j, LRank v k) -> rankIs v k j
    (LRank v k, LVar w m) -> rankVar v k w m
    (LVar w m, LRank v k) -> rankVar v k w m
    (LRank v k, LRank w j)
      | v == w ->
          unless (k == j) (failAt p ("ranks differ by " <> tshow (abs (k - j))))
      | k >= j -> do
          w' <- grow w (k - j)
          defer p (Rank (SVar v) (LRank w' 0))
      | otherwise -> do
          v' <- grow v (j - k)
          defer p (Rank (SVar w) (LRank v' 0))
 where
  bindLen v k j
    | j >= k = bindVar p v (ALen (LLit (j - k)))
    | otherwise =
        failAt
          p
          ( "a vector of length "
              <> tshow j
              <> " is too short: at least "
              <> tshow k
              <> " needed"
          )
  -- rank v + k = j: v is a shape of j - k lengths, each still unknown.
  rankIs v k j
    | j >= k = do
        ls <- mapM (const freshPosition) [1 .. j - k]
        bindVar p v (AShape (foldr (uncurry SCons) SNil ls))
    | otherwise =
        failAt
          p
          ("a rank of at least " <> tshow k <> " cannot be " <> tshow j)
  -- rank v + k = w + m.
  rankVar v k w m
    | k >= m = bindVar p w (ALen (LRank v (k - m)))
    | otherwise = do
        v' <- grow v (m - k)
        bindVar p w (ALen (LRank v' 0))
  -- Give a shape variable n fresh leading lengths and a fresh tail, which
  -- is returned: rank v = rank v' + n.
  grow v n
    | n == 0 = pure v
    | otherwise = do
        ls <- mapM (const freshPosition) [1 .. n]
        tl <- freshShape
        bindVar p v (AShape (foldr (uncurry SCons) tl ls))
        case tl of
          SVar v' -> pure v'
          _ -> error "freshShape"
  -- A position of a shape, length and axes still unknown.
  freshPosition = (,) <$> freshLen 0 <*> freshAxis

{- | Kennedy's algorithm (design §4.4): to unify two dimensions, solve
@d1 · d2⁻¹ = 1@. Pick the variable with the smallest exponent; if it
divides every other exponent, solve for it; otherwise substitute a fresh
variable times the quotients and repeat, Euclid-style.
-}
unifyDim :: Path -> Dim -> Dim -> Infer ()
unifyDim p d1 d2 = solve (dimDiv d1 d2)
 where
  solve delta = do
    s <- gets (.subst)
    let d = applyDim s delta
        vars = [(v, k) | (DVar v, k) <- dimAtoms d]
    case vars of
      [] -> unless (isDimOne d) (failAt p ("dimensions differ by " <> renderDim d))
      _ -> do
        let (v, x0) = minimumBy (comparing (abs . snd)) vars
        -- Work with a positive exponent: δ = 1 and δ⁻¹ = 1 are the same equation.
        let d' = if x0 < 0 then dimInv d else d
            x = abs x0
            others = [(a, k) | (a, k) <- dimAtoms d', a /= DVar v]
            divides (_, k) = k `mod` x == 0
            isVar (a, _) = case a of
              DVar _ -> True
              Base _ -> False
        if all divides others
          then
            bindVar p v (ADim (dimFromAtoms [(a, negate (k `div` x)) | (a, k) <- others]))
          -- Only base exponents fail to divide: no integer solution (design
          -- §4.4, case 2), and the Euclid step would substitute `v := v'`
          -- forever.
          else
            if all divides (filter isVar others)
              then failAt p ("dimensions differ by " <> renderDim d)
              else do
                v' <- freshDim
                bindVar
                  p
                  v
                  (ADim (dimMul v' (dimFromAtoms [(a, negate (k `div` x)) | (a, k) <- others])))
                solve d'

-- Constraints ----------------------------------------------------------------------

defer :: Path -> Constraint -> Infer ()
defer p c = do
  modify' (\st -> st{pending = (p, c) : st.pending})
  solvePending

{- | Solve every pending constraint that has become determined, repeating
until nothing more moves.
-}
solvePending :: Infer ()
solvePending = do
  st <- get
  put st{pending = []}
  remaining <- foldM step [] (reverse st.pending)
  modify' (\st' -> st'{pending = remaining ++ st'.pending})
  unless (length remaining == length st.pending) solvePending
 where
  step acc (p, c) = do
    progressed <- solveOne p c
    pure (if progressed then acc else (p, c) : acc)

-- | Try one constraint. Returns whether it was discharged.
solveOne :: Path -> Constraint -> Infer Bool
solveOne p = \case
  Append s1 s2 s3 -> do
    s <- gets (.subst)
    let s1' = applyShape s s1
        s2' = applyShape s s2
        s3' = applyShape s s3
    if s2' == SNil
      then unifyShape p s3' s1' >> pure True
      else case closedLens s1' of
        Just ls -> do
          unifyShape p s3' (appendShape ls s2')
          pure True
        Nothing -> case (closedLens s2', closedLens s3') of
          (Just l2, Just l3)
            | length l3 >= length l2 -> do
                let k = length l3 - length l2
                unifyShape p s1' (appendShape (take k l3) SNil)
                unifyShape p (appendShape (drop k l3) SNil) s2'
                pure True
            | otherwise ->
                failAt p "the result of a product has lower rank than one of its operands"
          _ -> pure False
  EqInstance t -> do
    t' <- resolve t
    case t' of
      -- Equality takes amounts (design §3.10, U9).
      TUnit _ -> failAt p ("no equality on " <> renderType t')
      TTensor _ _ -> pure True
      TPoint _ -> pure True
      TOver _ _ -> pure True
      -- A declared type compares when its fields do (design §4.2): Bool,
      -- tuples and lists among them.
      TData h as -> do
        defs <- gets (.typeDefs)
        case equalityArgs defs h as of
          Just ts -> mapM_ (defer p . EqInstance) ts >> pure True
          Nothing -> failAt p ("no equality on " <> renderType t')
      TVar _ -> pure False
      _ -> failAt p ("no equality on " <> renderType t')
  OrdInstance t -> do
    t' <- resolve t
    case t' of
      TTensor SNil _ -> pure True
      TTensor (SVar _) _ -> pure False
      TPoint f | f.space.shape == SNil -> pure True
      TPoint f | SVar _ <- f.space.shape -> pure False
      TVar _ -> pure False
      _ ->
        failAt
          p
          ("no ordering on " <> renderType t' <> "; only numbers and points compare")
  Rank sh l -> do
    s <- gets (.subst)
    case (rankLen (applyShape s sh), applyLen s l) of
      (LRank v _, LRank w _) | v /= w -> pure False
      (a, b) -> unifyLen p a b >> pure True
  OverIs f md t -> do
    s <- gets (.subst)
    case (overType (applyFrame s f) (applyDim s <$> md), applyType s t) of
      (TOver _ _, TTensor sh _) | Nothing <- closedLens sh -> pure False
      (TOver _ _, TVar _) -> pure False
      (o, t') -> unify p o t' >> pure True
  Fixed f -> do
    s <- gets (.subst)
    case (applyFrame s f).slot of
      FrNamed h -> do
        defs <- gets (.typeDefs)
        case defs h >>= frameDefMoving of
          Just True ->
            failAt
              p
              ( showHash h
                  <> " takes arguments: write «0» from ("
                  <> showHash h
                  <> " …) to «1»"
              )
          _ -> pure True
      FrVar _ -> pure False
  Dispatch r -> decide p r

{- | Choose a reading once the types say which (design §3.10). A quantity is
read by what follows its literal, or by its result where that already
says; a @to@ by its target, or by its value or result. Unit syntax after
a literal or a @to@ is a unit (U9), the one place a unit type arises.
Returns whether the reading was chosen.
-}
decide :: Path -> Reading -> Infer Bool
decide p = \case
  Quantity marker written lit atom res -> do
    atom' <- resolve atom
    res' <- resolve res
    case (atom', res') of
      (TUnit _, _) -> scaleReading
      (TChart _, _) -> chartReading
      (TVar _, TTensor{}) -> pure False
      (TVar _, TPoint _) -> chartReading
      (TVar _, _) -> pure False
      (other, _) ->
        failAt
          (1 : p)
          ( maybe "this" (\w -> "`" <> w <> "`") written
              <> " is "
              <> (case other of TFun _ _ -> "a function, "; _ -> "a ")
              <> renderType other
              <> ", not a unit or a chart: write the `*`"
          )
   where
    scaleReading = do
      asPrim p "scale" [(0, lit), (1, atom)] res
      choose marker "scale"
    -- A point (design §3.10, F8): its chart first, then its coordinates.
    chartReading = do
      asPrim p "pointOn" [(1, atom), (0, lit)] res
      choose marker "pointOn"
  Convert marker val tgt res -> do
    tgt' <- resolve tgt
    val' <- resolve val
    res' <- resolve res
    case (tgt', val', res') of
      (TUnit _, _, _) -> unitTo
      (TChart _, v, w)
        | any isPoint [v, w] -> chartTo
        | any isAmount [v, w] -> axesTo
        | otherwise -> pure False
      (TVar _, v, w)
        | any isAmount [v, w] -> axesTo
        | any isPoint [v, w] -> chartTo
        | otherwise -> pure False
      (TTensor{}, _, _) ->
        failAt
          (1 : p)
          "an amount after `to`, which takes a unit or a chart: write the unit, as in to km or to km/h"
      (other, _, _) ->
        failAt (1 : p) ("`to` takes a unit or a chart, not " <> renderType other)
   where
    unitTo = asPrim p "to" [(0, val), (1, tgt)] res >> choose marker "to"
    chartTo = do
      asPrim p "toChart" [(0, val), (1, tgt)] res
      fixed p val
      choose marker "toChart"
    axesTo = asPrim p "toAxes" [(0, val), (1, tgt)] res >> choose marker "toAxes"
  ConvertFrom marker val src tgt res -> do
    val' <- resolve val
    res' <- resolve res
    let reading prim = do
          asPrim p prim [(0, val), (1, src), (2, tgt)] res
          choose marker prim
    case (val', res') of
      (v, w)
        | any isPoint [v, w] -> reading "fromTo"
        | any isAmount [v, w] -> reading "axesFromTo"
        | all isTypeVar [v, w] -> pure False
        | otherwise ->
            failAt
              (0 : p)
              ("`from … to` converts a point or an amount, not " <> renderType v)
 where
  -- An amount, or the amount between points of a frame not yet known.
  isAmount = \case
    TTensor{} -> True
    TOver _ _ -> True
    _ -> False
  isPoint = \case
    TPoint _ -> True
    _ -> False
  choose marker prim = do
    modify' (\st -> st{chosen = Map.insert marker prim st.chosen})
    pure True

{- | A reading taken (design §3.10): the primitive's scheme, instantiated,
at the marker's operands, each by its path, and its result.
-}
asPrim :: Path -> Text -> [(Int, Type)] -> Type -> Infer ()
asPrim p name args res = case primScheme name of
  Nothing -> failAt p ("unknown primitive " <> name)
  Just sc -> do
    (t, _) <- instantiate sc
    let go ty = \case
          [] -> unify p ty res
          (i, a) : rest -> case ty of
            TFun param r -> unify (i : p) param a >> go r rest
            _ -> failAt p ("primitive " <> name <> " applied to too many arguments")
    go t args

{- | A point converted with no @from@ (design §3.10, F7): its frame's chart
takes no parameters, checked once the frame is known.
-}
fixed :: Path -> Type -> Infer ()
fixed p t =
  resolve t >>= \case
    TPoint f -> defer p (Fixed f)
    _ -> pure ()

isTypeVar :: Type -> Bool
isTypeVar = \case
  TVar _ -> True
  _ -> False

{- | At a generalisation point, constraints that only mention variables about
to be quantified cannot wait: default them (design §4.2). The unknown part
of a product's operand takes the least rank it can ('defaultProducts'); an
unknown equality type is taken to be `Num`. Constraints that mention variables of the enclosing
context stay pending, and so do constraints created outside the term being
generalised (the path given is that term's): the product around
@[1, 2] * (let y = 1 in [3])@ is not the inner let's to default.
-}
settle :: Path -> Vec n Scheme -> Infer ()
settle here ctx = do
  solvePending
  settleReadings here ctx
  s <- gets (.subst)
  let envVars = concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
      touchesEnv c = any (`elem` envVars) (constraintVars (applyC s c))
  st <- get
  let (stay, dflt) = partitionWith (\(p, c) -> outside p || touchesEnv c) st.pending
      (products, others) = partitionWith (isAppend . snd) dflt
  put st{pending = products ++ stay}
  defaultProducts products
  forM_ (reverse others) $ \(p, c) -> case applyC s c of
    -- Defaulted above.
    Append{} -> pure ()
    EqInstance t -> unify p numT t >> defer p c
    -- Ordering defaults to a number of any dimension, so that \a b -> a < b
    -- stays dimension-polymorphic.
    OrdInstance t -> do
      d <- freshDim
      unify p (numD d) t
      defer p c
    -- A rank equation has no default; it waits for the others, which may
    -- fix one of its shapes.
    Rank _ _ -> modify' (\st' -> st'{pending = (p, c) : st'.pending})
    -- An amount on a frame of a space nothing fixes (design §3.10, F4): no
    -- type says what @Diff c@ is of a space variable's shape, and no
    -- default would be right.
    OverIs{} ->
      failAt
        p
        "the amount between points on a frame of a space not known here: give a signature naming the space, as in forall (c : GCRS)"
    -- A frame still unknown: the run-time conversion checks it.
    Fixed _ -> pure ()
    -- Settled already ('settleReadings').
    Dispatch _ -> modify' (\st' -> st'{pending = (p, c) : st'.pending})
  solvePending
  -- Two shapes of equal but unknown rank: no type says that, and picking a
  -- rank would be a guess (design §4.2).
  s' <- gets (.subst)
  left <- gets (.pending)
  let envVars' = concat [map fst (freeVars (applyType s' b)) | Forall _ b <- vecToList ctx]
  forM_
    [ p
    | (p, c@(Rank _ _)) <- left
    , not (outside p)
    , not (any (`elem` envVars') (constraintVars (applyC s' c)))
    ]
    $ \p ->
      failAt
        p
        "two tensors here must have the same rank, which a generalised type cannot say; give one of them a known rank"
 where
  partitionWith f xs = (filter f xs, filter (not . f) xs)
  outside p = not (here `isSuffixOf` p)
  isAppend = \case
    Append{} -> True
    _ -> False

{- | Default the products still pending at a generalisation point (design
§4.2). A product's constraint @s3 ~ s1 ++ s2@ waits while @s1@ ends in a
variable; that variable takes the least rank the constraint allows. That is
none, unless @s3@ already has more leading lengths than @s1@ and a closed
@s2@ have together. So a bare unknown-rank operand of @outer@ is a scalar
and one of @dot@ a vector, while @[[x]]@ keeps the two lengths it has:
@x@ becomes a scalar and @[[x]]@ a matrix. Dot's two constraints share
their @s1@, so the variable that must take the most lengths is defaulted
first, one at a time, and the rest are re-read once it is solved.
-}
defaultProducts :: [(Path, Constraint)] -> Infer ()
defaultProducts cs = do
  s <- gets (.subst)
  let open =
        [ (p, v, need)
        | (p, c) <- cs
        , Append s1 s2 s3 <- [applyC s c]
        , (lead1, Just v) <- [spine s1]
        , let need = case closedLens s2 of
                Just l2 -> max 0 (fst (spine s3) - lead1 - length l2)
                Nothing -> 0
        ]
  case sortOn (\(_, _, need) -> Down need) open of
    [] -> pure ()
    (p, v, need) : _ -> do
      ls <- replicateM need ((,) <$> freshLen 0 <*> freshAxis)
      unifyShape p (SVar v) (appendShape ls SNil)
      solvePending
      defaultProducts cs
 where
  -- A shape's leading lengths, and the variable it ends in if it is open.
  spine = \case
    SNil -> (0 :: Int, Nothing)
    SVar v -> (0, Just v)
    SCons _ _ rest -> first (+ 1) (spine rest)

{- | The readings still open at a generalisation point that only mention
variables about to be quantified (design §3.10). A quantity or a @to@ is
settled here. An unresolved quantity suffix denotes a chart; a conversion
still ambiguous between point and axes conversion requires a signature.
-}
settleReadings :: Path -> Vec n Scheme -> Infer ()
settleReadings here ctx = do
  s <- gets (.subst)
  st <- get
  let envVars = concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
      open (p, c) = case c of
        Dispatch _ ->
          here `isSuffixOf` p
            && not (any (`elem` envVars) (constraintVars (applyC s c)))
        _ -> False
      (readings, rest) = (filter open st.pending, filter (not . open) st.pending)
      -- A chart suffix determines a point type that may settle a surrounding
      -- conversion. Resolve these before inspecting the other readings.
      isQuantity = \case (_, Dispatch Quantity{}) -> True; _ -> False
      inOrder =
        reverse (filter isQuantity readings)
          ++ reverse (filter (not . isQuantity) readings)
  put st{pending = rest}
  forM_ inOrder $ \(p, c) -> case c of
    Dispatch reading -> do
      resolved <- decide p reading
      unless resolved $ case reading of
        Quantity marker _ lit atom res -> do
          asPrim p "pointOn" [(1, atom), (0, lit)] res
          modify'
            (\current -> current{chosen = Map.insert marker "pointOn" current.chosen})
        Convert{} ->
          failAt
            p
            "ambiguous: `to` here could convert a point or an amount along chart axes; give the definition a signature that says which"
        ConvertFrom{} ->
          failAt
            p
            "ambiguous: `from … to` here could convert a point or an amount; give the definition a signature that says which"
    _ -> pure ()
  solvePending

applyC :: Subst -> Constraint -> Constraint
applyC s = \case
  Append a b c -> Append (applyShape s a) (applyShape s b) (applyShape s c)
  EqInstance t -> EqInstance (applyType s t)
  OrdInstance t -> OrdInstance (applyType s t)
  Rank sh l -> Rank (applyShape s sh) (applyLen s l)
  OverIs f md t -> OverIs (applyFrame s f) (applyDim s <$> md) (applyType s t)
  Fixed f -> Fixed (applyFrame s f)
  Dispatch r -> Dispatch $ case r of
    Quantity m w a b c -> Quantity m w (ty a) (ty b) (ty c)
    Convert m a b c -> Convert m (ty a) (ty b) (ty c)
    ConvertFrom m a b c res -> ConvertFrom m (ty a) (ty b) (ty c) (ty res)
 where
  ty = applyType s

-- | The types a reading is between.
readingTypes :: Reading -> [Type]
readingTypes = \case
  Quantity _ _ a b c -> [a, b, c]
  Convert _ a b c -> [a, b, c]
  ConvertFrom _ a b c r -> [a, b, c, r]

constraintVars :: Constraint -> [VarId]
constraintVars = \case
  Append a b c -> map fst (concatMap (freeVars . (`TTensor` dimOne)) [a, b, c])
  EqInstance t -> map fst (freeVars t)
  OrdInstance t -> map fst (freeVars t)
  Rank sh l -> map fst (freeVars (TTensor (SCons l AAnon sh) dimOne))
  OverIs f md t -> map fst (freeVars (TFun (TOver f md) t))
  Fixed f -> map fst (freeVars (TPoint f))
  Dispatch r -> concatMap (map fst . freeVars) (readingTypes r)

-- Generalisation and instantiation ---------------------------------------------------

{- | Quantify the variables of a type that are free in neither the context
nor a constraint still pending: such a constraint ties its variables to
the context (or to a term outside this one), and quantifying them would
cut that tie, as in @\k -> let g = \v -> k * v in g [1, 2]@, which once
typed its result as any shape at all.

Kennedy's algorithm may solve for the inverse of a variable, giving
@Num (1/d^2) -> Num (1/d^3)@ where @Num (d^2) -> Num (d^3)@ means the same
scheme. A quantified dimension variable that only appears with negative
exponents is replaced by the inverse of a fresh one, through the
substitution, so that the elaborated term (zonked with it) and the scheme
agree.
-}
generalise :: Vec n Scheme -> Type -> Infer Scheme
generalise ctx t = do
  orient ctx [t]
  quantify ctx t

{- | Types generalised together, as a cycle's members are: they share their
quantified variables, so a dimension variable is flipped only when it is
inverted in all of them.
-}
generaliseAll :: Vec n Scheme -> [Type] -> Infer [Scheme]
generaliseAll ctx ts = do
  orient ctx ts
  mapM (quantify ctx) ts

orient :: Vec n Scheme -> [Type] -> Infer ()
orient ctx ts = do
  candidates <- mapM (quantifiable ctx) ts
  let quantified = nubBy (\a b -> fst a == fst b) (concatMap snd candidates)
  forM_ (negativeOnly quantified (map fst candidates)) $ \v -> do
    w <- freshDim
    bindVar [] v (ADim (dimInv w))

{- | A named value keeps no free axis variable (design §3.9, decision 5):
at a local binding whose type is not a function, the axis variables it
would quantify are anonymous. Those the context or a pending constraint
holds are not its to fix. (A definition's own scheme stays general; the
default for a definition is where its name is used, 'defaultAxes'.)
-}
defaultValueAxes :: Vec n Scheme -> Type -> Infer ()
defaultValueAxes ctx t = do
  (t', vs) <- quantifiable ctx t
  case t' of
    TFun _ _ -> pure ()
    _ -> forM_ [v | (v, KAxis) <- vs] $ \v -> bindVar [] v (AAxis AAnon)

quantify :: Vec n Scheme -> Type -> Infer Scheme
quantify ctx t = (\(t', quantified) -> Forall quantified t') <$> quantifiable ctx t

-- | A type under the substitution, and its variables that may be quantified.
quantifiable :: Vec n Scheme -> Type -> Infer (Type, [(VarId, Kind)])
quantifiable ctx t = do
  s <- gets (.subst)
  pending <- gets (.pending)
  let t' = applyType s t
      envVars =
        concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
          ++ concatMap (constraintVars . applyC s . snd) pending
  pure (t', filter ((`notElem` envVars) . fst) (freeVars t'))

{- | The quantified dimension variables that occur, in all the types
together, only with negative exponents.
-}
negativeOnly :: [(VarId, Kind)] -> [Type] -> [VarId]
negativeOnly quantified ts =
  [ v
  | (v, KDim) <- quantified
  , let ks = concatMap (exponents v) ts
  , not (null ks)
  , all (< 0) ks
  ]
 where
  exponents v = \case
    TTensor _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TUnit d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TPoint f -> frameExps f
    TOver f md -> frameExps f ++ maybe [] dimExps md
    TChart f -> frameExps f
    TData _ args -> concatMap argExponents args
    TFun a b -> exponents v a ++ exponents v b
    TVar _ -> []
   where
    argExponents = \case
      AType t -> exponents v t
      ADim d -> dimExps d
      _ -> []
    dimExps d = [k | (DVar w, k) <- dimAtoms d, w == v]
    frameExps f = dimExps f.space.dim

{- | Replace the quantified variables by fresh ones and return the arguments
used, for the explicit type applications. This is a one-shot renaming, not
'applyType': a stored scheme's variable ids can coincide with this run's
fresh ids, and chasing such a binding through the substitution would never
terminate.
-}
instantiate :: Scheme -> Infer (Type, [Arg])
instantiate (Forall vs t) = do
  args <- mapM (fresh . snd) vs
  let m = Map.fromList (zip (map fst vs) args)
  -- Simultaneous, not sequential: a fresh id can equal the next quantified
  -- id, and replacing one variable at a time would then rename twice (lint
  -- caught `cross` elaborating to `Vec 3 m -> Vec 3 (m/s) -> Vec 3 (m^2)`).
  pure (substOnce m t, args)

applyArgs :: TTerm n -> [Arg] -> TTerm n
applyArgs = foldl TTyApp

-- Inference ----------------------------------------------------------------------------

infer :: TypeLookup -> Path -> Vec n Scheme -> Term n -> Infer (Type, TTerm n)
infer look p ctx = \case
  -- An ascription's marker, in a term desugared to check them (design
  -- §4.8): the ascribed type, instantiated fresh, is unified with the
  -- expression's, so it narrows and never widens. The marker elaborates to
  -- the expression's own typed term.
  -- A signature's marker around a body whose ascriptions name its
  -- variables reads the same way, its body at its own path.
  PrimApp marker [a]
    | ascriptionMarker `T.isPrefixOf` marker -> do
        let signature = ":signature" `T.isSuffixOf` marker
        r@(t, _) <- infer look (if signature then p else 0 : p) ctx a
        ascribed <- gets (Map.lookup marker . (.annotations.ascriptions))
        case ascribed of
          Nothing -> failAt p "internal error: an ascription without its type"
          Just (sc, at) -> do
            (want, _) <- instantiate sc
            st <- get
            case runStateT (unify p want t) st of
              Right ((), st') -> put st'
              Left err ->
                failAt
                  (reverse at)
                  ((if signature then "the signature: " else "the ascription: ") <> err.message)
        pure r
  Var i -> do
    (t, args) <- instantiate (lookupCtx i ctx)
    pure (t, applyArgs (TVr i) args)
  Ref h idx hint -> case look.schemesOf h of
    Nothing -> failAt p "reference to a definition with no stored type"
    Just schemes -> case nth (fromMaybe 0 idx) schemes of
      Just sc -> do
        (t, args) <- instantiate sc
        let Hint written = hint
        signature <- gets (\st -> st.annotations.signatureFor written h idx)
        case signature of
          Nothing -> pure (t, applyArgs (TRef h idx hint) args)
          -- A use sees the name's signature (design §4.8). The type
          -- applications stay those of the hash's own scheme, which lint
          -- checks; the signature, an instance of it, narrows them.
          Just narrower -> do
            (t', _) <- instantiate narrower
            unify p t t'
            pure (t', applyArgs (TRef h idx hint) args)
      Nothing -> failAt p "reference to a cycle member that does not exist"
  PrimApp name args -> do
    let literals = [case unmarked a of Lit l -> Just l; _ -> Nothing | a <- args]
        static :: Term m -> Maybe StaticArg
        static a = case unmarked a of
          Lit l -> Just (LitArg l)
          Con NilC [] -> Just (ListArg [])
          Con ConsC [x, rest] -> case static rest of
            Just (ListArg xs) -> Just (ListArg (static x : xs))
            _ -> Nothing
          Con c [] -> Just (ConArg c)
          _ -> Nothing
        statics = map static args
        positional = name `elem` ["contract", "permute", "slice"]
    defs <- gets (.typeDefs)
    -- contract, permute and slice (design §4.2): the scheme is computed
    -- from the literal positions, then used like any other; a chart's
    -- declaration reads its frame, axes and space off its tags (design
    -- §3.10, F3).
    t <- case primSchemeFor defs name statics of
      Just (Right sc) -> fst <$> instantiate sc
      Just (Left msg) -> failAt p msg
      -- A `from … to` (design §3.10, F7): a point or an amount, by type.
      Nothing
        | [_, _, _] <- args
        , isFromMarker name -> do
            a <- freshType
            b <- freshType
            c <- freshType
            r <- freshType
            defer p (Dispatch (ConvertFrom name a b c r))
            pure (TFun a (TFun b (TFun c r)))
      -- A quantity or a `to` whose reading the types choose (design §3.10,
      -- U4, U6): its marker is resolved by the types it meets.
      Nothing
        | [_, atom] <- args
        , isQuantityMarker name || isToMarker name -> do
            a <- freshType
            b <- freshType
            r <- freshType
            defer
              p
              ( Dispatch
                  ( if isQuantityMarker name
                      then Quantity name (writtenName atom) a b r
                      else Convert name a b r
                  )
              )
            pure (TFun a (TFun b r))
      Nothing -> primType p name (length args)
    -- A point converted with no `from` (design §3.10, F7).
    case t of
      TFun (TPoint f) _ | name == "toChart" -> defer p (Fixed f)
      _ -> pure ()
    typed <- zipWithM (\i a -> infer look (i : p) ctx a) [0 ..] args
    -- A tensor of known rank too small for the positions is reported as
    -- such, not as the shape mismatch the unifier would find.
    case (positional, reverse (zip [0 :: Int ..] typed), lastParam t) of
      (True, (i, (ta, _)) : _, Just (TTensor want _)) -> do
        ta' <- resolve ta
        case ta' of
          TTensor sh _
            | Just ls <- closedLens sh
            , length ls < leading want ->
                failAt
                  (i : p)
                  ( T.unwords (name : [literalText l | Just l <- init literals])
                      <> " needs a tensor of rank at least "
                      <> tshow (leading want)
                      <> ", got "
                      <> renderType ta'
                  )
            -- A slice past the end of a known axis, worded as for a
            -- projection (design §2.10).
            | name == "slice"
            , [Just (LTensor ([], [rk])), Just (LTensor ([], [ri])), _] <- literals
            , Just (LLit n) <- axisLen (numerator rk) sh
            , numerator ri >= fromIntegral n ->
                failAt
                  p
                  ( "position "
                      <> tshow (numerator ri)
                      <> " is out of range for axis "
                      <> tshow (numerator rk)
                      <> " of length "
                      <> tshow n
                  )
          _ -> pure ()
      _ -> pure ()
    -- Primitive types are fully known in shape, so peel one arrow per
    -- argument and report a mismatch at the argument that caused it.
    let go i ty = \case
          [] -> pure ty
          a : rest -> case ty of
            TFun param r -> do
              -- The circular functions are the common place to forget that
              -- angles carry a unit (design §3.2.11).
              a' <- resolve a
              case a' of
                -- A unit's size is one number (design §3.10, U7).
                TTensor SCons{} _
                  | name == "unit" ->
                      failAt
                        (i : p)
                        ( "a unit is one number, not "
                            <> renderType a'
                            <> ": declare it as an amount, 60 s, or a unit, kg*m/s^2"
                        )
                _
                  | name `elem` ["sin", "cos", "tan"] ->
                      unifyMsg (i : p) param a (name <> " takes an angle: write 1 rad or 45 deg")
                -- A chart turned or spinning is on a space of vectors
                -- (design §3.10, F10).
                _
                  | name == "mkChart"
                  , i == 2
                  , TChart f <- param
                  , SCons{} <- f.space.shape ->
                      unifyMsg
                        (i : p)
                        param
                        a
                        "a chart on a space of numbers has no axes to turn: `by` and `spinning` are for a space of vectors"
                -- Units do not add (design §3.10, U2).
                TUnit _
                  | name `elem` ["add", "sub"] ->
                      failAt
                        (i : p)
                        ( "units do not add: this is "
                            <> renderType a'
                            <> ", and + and - take amounts"
                        )
                _ -> unify (i : p) param a
              go (i + 1) r rest
            _ -> failAt p ("primitive " <> name <> " applied to too many arguments")
    result <- go (0 :: Int) t (map fst typed)
    -- The arguments may have fixed the shapes a pending product constraint
    -- was waiting for; solve now so later errors print resolved types.
    solvePending
    pure (result, TPrimApp name t (map snd typed))
  -- A literal is polymorphic in its axes (design §3.9, decision 5): its
  -- frame comes from where it is used.
  Lit l@(LTensor (dims, _)) -> do
    axes <- mapM (const freshAxis) dims
    pure
      ( TTensor (foldr (\(k, a) -> SCons (LLit k) a) SNil (zip dims axes)) dimOne
      , TLit l axes
      )
  -- Data (design §5.1): constructors are typed by the table below, a case by
  -- its scrutinee's constructors, with each alternative binding the fields.
  Con c args -> do
    (fieldTys, resultTy) <- constructorType look p c (length args)
    typed <-
      zipWithM
        ( \i (a, want) -> do (ta, a') <- infer look (i : p) ctx a; unify (i : p) want ta; pure a'
        )
        [0 ..]
        (zip args fieldTys)
    resolved <- resolve resultTy
    pure (resolved, TCon c resolved typed)
  Case s alts -> do
    (ts, s') <- infer look (0 : p) ctx s
    result <- freshType
    typedAlts <-
      zipWithM (\i alt -> inferAlt look (i : p) ctx ts result alt) [1 ..] alts
    ts' <- resolve ts
    checkExhaustive look p ts' [c | Alt c _ _ <- alts]
    result' <- resolve result
    pure (result', TCase s' result' typedAlts)
  Lam h body -> do
    a <- freshType
    (b, body') <- infer look (0 : p) (VCons (Forall [] a) ctx) body
    pure (TFun a b, TLam h a body')
  App f a -> do
    (tf, f') <- infer look (0 : p) ctx f
    (ta, a') <- infer look (1 : p) ctx a
    r <- freshType
    tf' <- resolve tf
    case tf' of
      TFun _ _ -> unify (0 : p) tf (TFun ta r)
      TVar _ -> unify (0 : p) tf (TFun ta r)
      _ ->
        failAt (0 : p) (renderType tf' <> " is not a function and cannot be applied")
    pure (r, TApp f' a')
  Let h e body -> do
    (te, e') <- infer look (0 : p) ctx e
    settle (0 : p) ctx
    defaultValueAxes ctx te
    sc@(Forall vs _) <- generalise ctx te
    (tb, body') <- infer look (1 : p) (VCons sc ctx) body
    pure (tb, TLet h sc (abstractOver vs e') body')
  -- A power of a scalar amount. Unit powers are elaborated in unit contexts.
  Pow b n -> do
    (tb, b') <- infer look (0 : p) ctx b
    d <- freshDim
    unify (0 : p) (numD d) tb
    pure (numD (dimPow n d), TPow b' n)
  Noise k l n
    | n > lengthLimit ->
        failAt p ("a tensor has at most " <> "2^40" <> " components")
    | otherwise -> pure (vecT (LLit (fromInteger n)), TNoise k l n)
  -- x ± e over any shape (design §3.4): the uncertainty is a scalar applied
  -- to every component, or a tensor of the value's shape; in both cases one
  -- independent nudge per component.
  Uncertain k l x e -> do
    d <- freshDim
    s <- freshShape
    (tx, x') <- infer look (0 : p) ctx x
    unify (0 : p) (TTensor s d) tx
    (te, e') <- infer look (1 : p) ctx e
    te' <- resolve te
    s' <- resolveShape s
    case (te', s') of
      (TTensor SNil _, _) ->
        unifyMsg
          (1 : p)
          (numD d)
          te
          "the uncertainty must have the dimension of the value"
      -- v ±σ P: a vector with covariance P (design §3.5).
      -- The covariance pairs the value's axes with themselves.
      (TTensor (SCons _ _ (SCons _ _ SNil)) _, SCons n a SNil)
        | k == Stat ->
            unifyMsg
              (1 : p)
              (TTensor (SCons n a (SCons n a SNil)) (dimPow 2 d))
              te
              "a covariance must be an n×n matrix of the value's dimension squared"
        | otherwise ->
            failAt
              (1 : p)
              "a covariance matrix goes with ±σ, not ±: a bound has no covariance"
      _ ->
        unifyMsg
          (1 : p)
          (TTensor s d)
          te
          "the uncertainty must be a scalar, have the shape and dimension of the value, or be its covariance matrix"
    pure (TTensor s d, TUncertain k l x' e')
  Pack ts -> do
    elemShape <- freshShape
    elemDim <- freshDim
    let elemT = TTensor elemShape elemDim
    ts' <-
      zipWithM
        ( \i t -> do
            (tt, t') <- infer look (i : p) ctx t
            unifyMsg
              (i : p)
              elemT
              tt
              "every element of a tensor literal must have the same shape and dimension"
            pure t'
        )
        [0 ..]
        ts
    -- The new leading position's axes come from use, as a literal's do.
    ax <- freshAxis
    pure
      (TTensor (SCons (LLit (length ts)) ax elemShape) elemDim, TPack ax elemT ts')
  Proj t i -> do
    (tt0, t') <- infer look (0 : p) ctx t
    tt <- resolve tt0
    ty <- case tt of
      TTensor (SCons (LLit n) _ rest) d
        | i < n -> pure (TTensor rest d)
        | otherwise ->
            failAt
              p
              ("position " <> tshow i <> " is out of range for a vector of length " <> tshow n)
      TTensor (SCons l _ rest) d -> do
        atLeast <- freshLen (i + 1)
        unifyLen p l atLeast
        pure (TTensor rest d)
      TTensor SNil _ -> failAt p ("cannot project ." <> tshow i <> " from a number")
      -- A coordinate of a point (design §3.10, F5): an amount along one of
      -- its frame's axes, the step applied, in its space's dimension.
      TPoint f -> case f.space.shape of
        SNil ->
          failAt
            p
            ("cannot project ." <> tshow i <> " from a point on a space of numbers")
        SCons (LLit n) _ SNil
          | i >= n ->
              failAt
                p
                ( "position "
                    <> tshow i
                    <> " is out of range for a point on a space of "
                    <> tshow n
                    <> " axes"
                )
        _ -> do
          atLeast <- freshLen (i + 1)
          unifyShape (0 : p) f.space.shape (SCons atLeast AAnon SNil)
          pure (numD f.space.dim)
      -- Rank unknown so far: it must be at least one.
      _ -> do
        atLeast <- freshLen (i + 1)
        rest <- freshShape
        d <- freshDim
        axes <- freshAxis
        unify (0 : p) tt (TTensor (SCons atLeast axes rest) d)
        pure (TTensor rest d)
    pure (ty, TProj t' i)
  Cycle{} -> failAt p "a cycle cannot appear inside an expression"
 where
  -- Unify, but on failure report a message about the construct rather than
  -- the bare mismatch.
  unifyMsg p' expected actual msg = do
    st <- get
    case runStateT (unify p' expected actual) st of
      Right ((), st') -> put st'
      -- The unifier's own message names what differs (a length, a dimension).
      Left (TypeError _ inner) -> failAt p' (msg <> ": " <> inner)
  -- The type of a primitive's last parameter, and the number of lengths a
  -- shape lists before its tail.
  lastParam = \case
    TFun _ r@(TFun _ _) -> lastParam r
    TFun a _ -> Just a
    _ -> Nothing
  leading = \case
    SCons _ _ rest -> 1 + leading rest
    _ -> 0 :: Int
  -- The length at a position of a shape, if the shape lists that many.
  axisLen :: Integer -> Shape -> Maybe Len
  axisLen k = \case
    SCons l _ rest -> if k == 0 then Just l else axisLen (k - 1) rest
    _ -> Nothing
  -- An index literal as it was written: a natural or a vector of them.
  literalText (LTensor (dims, rs)) =
    let natural r = tshow (numerator r)
     in case dims of
          [] -> T.concat (map natural rs)
          _ -> "[" <> T.intercalate ", " (map natural rs) <> "]"

{- | The type a primitive is used at: a fresh instance of its scheme, or for
the relational primitives (design §4.2) fresh shapes with a pending
constraint between them.
-}
primType :: Path -> Text -> Int -> Infer Type
primType p name argc = do
  t <- case name of
    -- Ordinary products are amounts, relational in their shapes (§4.2).
    "outer" -> do
      s1 <- freshShape
      s2 <- freshShape
      s3 <- freshShape
      d1 <- freshDim
      d2 <- freshDim
      defer p (Append s1 s2 s3)
      pure (TFun (TTensor s1 d1) (TFun (TTensor s2 d2) (TTensor s3 (dimMul d1 d2))))
    "div" -> do
      s <- freshShape
      d1 <- freshDim
      d2 <- freshDim
      pure (TFun (TTensor s d1) (TFun (numD d2) (TTensor s (dimDiv d1 d2))))
    "dot" -> do
      s1 <- freshShape
      n <- freshLen 0
      s2 <- freshShape
      left <- freshShape
      s3 <- freshShape
      d1 <- freshDim
      d2 <- freshDim
      -- The contracted positions share one length and one axis set (design
      -- §3.9): the left's last and the right's first.
      a <- freshAxis
      defer p (Append s1 (SCons n a SNil) left)
      defer p (Append s1 s2 s3)
      pure
        ( TFun
            (TTensor left d1)
            (TFun (TTensor (SCons n a s2) d2) (TTensor s3 (dimMul d1 d2)))
        )
    _ | name == "eq" || name == "ne" -> do
      a <- freshType
      defer p (EqInstance a)
      pure (TFun a (TFun a boolT))
    _ | name `elem` ["lt", "le", "gt", "ge"] -> do
      a <- freshType
      defer p (OrdInstance a)
      pure (TFun a (TFun a boolT))
    _ -> case primScheme name of
      Just sc -> fst <$> instantiate sc
      Nothing -> failAt p ("unknown primitive " <> name)
  let arity = countArrows t
  unless (argc == arity)
    $ failAt
      p
      ( "primitive "
          <> name
          <> " expects "
          <> tshow arity
          <> " arguments, got "
          <> tshow argc
      )
  pure t
 where
  countArrows = \case
    TFun _ r -> 1 + countArrows r
    _ -> 0 :: Int

-- Zonking ------------------------------------------------------------------------------

-- | Resolve every metavariable in an elaborated term.
zonk :: Subst -> TTerm n -> TTerm n
zonk s = go
 where
  go :: TTerm m -> TTerm m
  go = \case
    TVr i -> TVr i
    TRef h i hint -> TRef h i hint
    TPrimApp p ty args -> TPrimApp p (applyType s ty) (map go args)
    TLit l axes -> TLit l (map (applyAxis s) axes)
    TLam h ty b -> TLam h (applyType s ty) (go b)
    TApp f a -> TApp (go f) (go a)
    TLet h sc e b -> TLet h (applyScheme s sc) (go e) (go b)
    TCon c ty args -> TCon c (applyType s ty) (map go args)
    TCase sc ty alts ->
      TCase
        (go sc)
        (applyType s ty)
        ( map
            (\(TAlt c bs b) -> TAlt c (vecMap (second (applyType s)) bs) (go b))
            alts
        )
    TPow b n -> TPow (go b) n
    TNoise k l n -> TNoise k l n
    TUncertain k l x e -> TUncertain k l (go x) (go e)
    TPack ax ty ts -> TPack (applyAxis s ax) (applyType s ty) (map go ts)
    TProj t i -> TProj (go t) i
    TTyLam v k b -> TTyLam v k (go b)
    TTyApp b arg -> TTyApp (go b) (applyArg s arg)
    TCycle vs members bodies ->
      TCycle vs (vecMap (second (applyType s)) members) (vecMap go bodies)

-- Readings ----------------------------------------------------------------------------

{- | Write the readings inference chose ('readingsOf') into a term (design
§3.10, U4, U6): a quantity's marker becomes @scale lit u@ or @pointOn c
lit@, a @to@'s marker the display unit's @to@ or @toChart@. A marker with
no reading stays, which hashing refuses as an unknown primitive.
-}
rewriteReadings :: Map.Map Text Text -> Term n -> Term n
rewriteReadings chosen = go
 where
  go :: Term m -> Term m
  go = \case
    PrimApp p [a, b]
      | Just prim <- Map.lookup p chosen ->
          if prim == "pointOn"
            then PrimApp prim [go b, go a]
            else PrimApp prim [go a, go b]
    PrimApp p as
      | Just prim <- Map.lookup p chosen -> PrimApp prim (map go as)
    t -> mapChildren go t

-- | Whether a term has a quantity or @to@ whose reading is still to choose.
hasReadingMarkers :: Term n -> Bool
hasReadingMarkers =
  getAny
    . foldTerm
      ( \case
          PrimApp p _ -> Any (isQuantityMarker p || isToMarker p || isFromMarker p)
          _ -> mempty
      )

-- | The name a quantity's atom was written as, for a message.
writtenName :: Term n -> Maybe Text
writtenName t = case unmarked t of
  Ref _ _ (Hint w) -> Just w
  PrimApp n [] -> Just n
  _ -> Nothing

-- Helpers ------------------------------------------------------------------------------

lookupCtx :: Fin n -> Vec n Scheme -> Scheme
lookupCtx i ctx = case (i, ctx) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupCtx j xs

nth :: Int -> [a] -> Maybe a
nth i xs
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      x : _ -> Just x
      [] -> Nothing

indices :: Vec k a -> Vec k Int
indices = go 0
 where
  go :: Int -> Vec m a -> Vec m Int
  go _ VNil = VNil
  go i (VCons _ xs) = VCons i (go (i + 1) xs)

-- Data ---------------------------------------------------------------------------------

{- | Field types and result type of a constructor applied to @k@ arguments,
with fresh variables where the constructor is polymorphic.
-}
constructorType :: TypeLookup -> Path -> ConRef -> Int -> Infer ([Type], Type)
constructorType look p c k = case c of
  -- A declared type, the built-in ones among them: fresh arguments for its
  -- parameters, by kind.
  UserCon h i | Just def <- withBuiltins look.typeDefOf h -> do
    args <- mapM (freshArg . snd) def.params
    let ty = TData h args
    case dataConstructors look.typeDefOf ty of
      Just table
        | Just fields <- lookup (UserCon h i) table
        , length fields == k ->
            pure (fields, ty)
      _ ->
        failAt
          p
          ("constructor " <> conText c <> " does not take " <> tshow k <> " fields")
  _ ->
    failAt
      p
      ("unknown constructor " <> conText c <> " with " <> tshow k <> " fields")
 where
  freshArg = \case
    KType -> AType <$> freshType
    KLen -> ALen <$> freshLen 0
    KShape -> AShape <$> freshShape
    KDim -> ADim <$> freshDim
    KAxis -> fresh KAxis
    KFrame -> fresh KFrame
    KSpace -> fresh KSpace

{- | One alternative: the constructor's fields enter scope at their types and
the body must have the case's result type.
-}
inferAlt ::
  TypeLookup -> Path -> Vec n Scheme -> Type -> Type -> Alt n -> Infer (TAlt n)
inferAlt look p ctx scrutTy result (Alt c hs body) = do
  st <- resolve scrutTy
  fields <- case dataConstructors look.typeDefOf st of
    Just cs -> case lookup c cs of
      Just fts
        | length fts == vecLength hs -> pure fts
        | otherwise ->
            failAt
              p
              ( "constructor "
                  <> conText c
                  <> " has "
                  <> tshow (length fts)
                  <> " fields, the pattern binds "
                  <> tshow (vecLength hs)
              )
      Nothing ->
        failAt
          p
          ("constructor " <> conText c <> " does not belong to " <> renderType st)
    Nothing -> case st of
      TVar _ -> do
        (fts, rt) <- constructorType look p c (vecLength hs)
        unify p scrutTy rt
        pure fts
      _ ->
        failAt
          p
          ( "cannot match "
              <> renderType st
              <> " against the constructor "
              <> conText c
              <> ( if c `elem` [TrueC, FalseC]
                     then ": the condition of `if` must be a Bool"
                     else ""
                 )
          )
  let typed = attach hs fields
  (tb, body') <-
    infer look (0 : p) (vecAppend (vecMap (Forall [] . snd) typed) ctx) body
  unify p result tb
  pure (TAlt c typed body')
 where
  attach :: Vec k Hint -> [Type] -> Vec k (Hint, Type)
  attach VNil _ = VNil
  attach (VCons h rest) (t : ts) = VCons (h, t) (attach rest ts)
  attach (VCons h rest) [] = VCons (h, boolT) (attach rest []) -- unreachable: lengths were checked

{- | A case covers exactly the constructors of its scrutinee's type, in
canonical order (design §5.1).
-}
checkExhaustive :: TypeLookup -> Path -> Type -> [ConRef] -> Infer ()
checkExhaustive look p ty cs = case dataConstructors look.typeDefOf ty of
  Nothing ->
    failAt
      p
      ( "cannot case on "
          <> renderType ty
          <> "; the scrutinee's type is not a data type, or not yet known"
      )
  Just table -> do
    let want = map fst table
    unless (cs == want)
      $ failAt
        p
        ( "the alternatives must be exactly "
            <> T.intercalate ", " (map conText want)
            <> " in that order; got "
            <> T.intercalate ", " (map conText cs)
        )

{- | Whether a definition's type can be an instance of a query type, both
quantified: the type search of @:ls@ (design §7.3). Each side is instantiated
with fresh variables and the two are unified, so @a -> a@ matches a query
@Num -> Num@ and @Num m -> Num m@ matches a query @a -> a@.
-}
matchesQuery :: Scheme -> Scheme -> Bool
matchesQuery query sc = case runStateT
  go
  (St emptySubst 0 axisBase [] (const Nothing) noAnnotations Map.empty) of
  Right _ -> True
  Left _ -> False
 where
  go = do
    (q, _) <- instantiate query
    (t, _) <- instantiate sc
    unify [] q t
