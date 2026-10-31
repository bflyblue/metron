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
module Eval.Infer (
  TypeError (..),
  TypeLookup,
  elaborateClosed,
  elaborateClosedWith,
  readingsOf,
  rewriteReadings,
  hasReadingMarkers,
  Annotations (..),
  noAnnotations,
  inferClosed,
  matchesQuery,
) where

import Control.Monad (foldM, forM_, unless, zipWithM, zipWithM_)
import Control.Monad.State.Strict (StateT, get, gets, modify', put, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (second)
import Data.List (isSuffixOf, minimumBy, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Ratio (numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Builtin
import Eval.Core
import Eval.Desugar (
  Path,
  ascriptionMarker,
  isQuantityMarker,
  isToMarker,
  unmarked,
 )
import Eval.Dimension
import Eval.TCore
import Eval.Type

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
  | {- | a root chart of a shape, its root, the axes it minted (design §3.9):
    every position along those axes and the root too, or a scalar chart
    with an anonymous root; pending while the shape is unknown
    -}
    Charted Shape Axis Hash
  | {- | a chart's shape, its root, and the shape of a point on it: the
    chart's lengths along the root's axes (design §3.9, stage 2b)
    -}
    Rootward Shape Axis Shape
  | {- | a primitive with two readings, chosen by the types it is used at
    once one of them is known (design §3.10, U2, U4, U6, U7)
    -}
    Dispatch Reading

{- | What a 'Dispatch' chooses between. Arithmetic and a unit declaration
have two readings that are one operation at run time, so the choice is
static only and an unknown one takes the amount reading at
generalisation. The quantity rule and @to@ are different operations, so
their choice is written into the term ('rewriteReadings') and an unknown
one at generalisation is refused as ambiguous.
-}
data Reading
  = {- | @*@ or @/@ (@outer@, @div@): its operands and its result, and the
    shapes and dimensions either reading is made of, made with the
    primitive's type, before its operands', so that a dimension is solved
    as it was before units were a type
    -}
    Arith Text Type Type Type Parts
  | -- | @^k@: the base and the result, and the base's dimension
    Power Integer Dim Type Type
  | {- | a quantity whose reading the desugarer left to the types, by its
    marker: the literal, what follows it, and the result; @scale@ for a
    unit, @pointOn@ for a chart (U4)
    -}
    Quantity Text (Maybe Text) Type Type Type
  | {- | a @to@ whose reading the desugarer left to the types, by its
    marker: the value, the target, and the result; the display unit's
    @to@ for a unit, @toScale@ for a chart (U6)
    -}
    Convert Text Type Type Type
  | -- | a unit declaration's body, an amount or a unit, and the unit (U7)
    UnitOf Type Type

-- | The operands' and the result's shapes and the operands' dimensions.
data Parts = Parts Shape Shape Shape Dim Dim

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
desugared to check them ('Eval.Desugar.desugarMarked'), each with the path
an error in it is reported at ('Eval.Desugar.ascriptionPath'). Annotations
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

inferClosed :: TypeLookup -> Term Z -> Either TypeError [Scheme]
inferClosed look term = fst <$> elaborateClosed look term

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
    (TPoint s1 d1, TPoint s2 d2) -> shapeAndDims s1 d1 s2 d2
    (TScale s1 r1 d1, TScale s2 r2 d2) -> do
      shapeAndDims s1 d1 s2 d2
      unifyAxis p r1 r2
    (TTensor s1 d1, TTensor s2 d2) -> do
      st <- get
      case runStateT (unifyShape p s1 s2 >> unifyDim p d1 d2) st of
        Right ((), st') -> put st'
        Left (TypeError _ detail) ->
          failAt
            p
            ("expected " <> renderType e <> ", got " <> renderType a <> ": " <> detail)
    (TPoint _ _, TTensor _ _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": a point and an amount; a point has no sum, multiple or unit; use .+ and .-, or to with a chart (design §3.6)"
        )
    (TTensor _ _, TPoint _ _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": an amount and a point; a point has no sum, multiple or unit; use .+ and .-, or to with a chart (design §3.6)"
        )
    (TUnit d1, TUnit d2) -> do
      st <- get
      case runStateT (unifyDim p d1 d2) st of
        Right ((), st') -> put st'
        Left (TypeError _ detail) ->
          failAt
            p
            ("expected " <> renderType e <> ", got " <> renderType a <> ": " <> detail)
    -- A unit is not an amount (design §3.10, U3): `1 km` is the amount.
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
    _ -> failAt p ("expected " <> renderType e <> ", got " <> renderType a)
 where
  -- Arguments of a declared type, by kind; a kind mismatch cannot happen for
  -- a well-formed type, so it reports as a plain mismatch.
  unifyArg x y = case (x, y) of
    (AType t1, AType t2) -> unify p t1 t2
    (ALen l1, ALen l2) -> unifyLen p l1 l2
    (AShape s1, AShape s2) -> unifyShape p s1 s2
    (ADim d1, ADim d2) -> unifyDim p d1 d2
    (AAxis a1, AAxis a2) -> unifyAxis p a1 a2
    _ ->
      failAt p ("expected " <> renderType expected <> ", got " <> renderType actual)
  shapeAndDims s1 d1 s2 d2 = do
    st <- get
    case runStateT (unifyShape p s1 s2 >> unifyDim p d1 d2) st of
      Right ((), st') -> put st'
      Left (TypeError _ detail) -> do
        e <- resolve expected
        a <- resolve actual
        failAt
          p
          ("expected " <> renderType e <> ", got " <> renderType a <> ": " <> detail)

bindVar :: Path -> VarId -> Arg -> Infer ()
bindVar p v arg = do
  let occurs = case arg of
        AType t -> v `elem` map fst (freeVars t)
        AShape s -> v `elem` map fst (freeVars (TTensor s dimOne))
        ALen _ -> False
        ADim d -> v `elem` dimVars d
        -- A slot holds no variable but itself.
        AAxis _ -> False
      trivial = case arg of
        AType (TVar w) -> w == v
        AShape (SVar w) -> w == v
        ALen (LVar w 0) -> w == v
        ADim d -> d == dimVar v
        AAxis (AVar w) -> w == v
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
        "; give it a frame with `withAxes c v`, or `along c v` if it is along the root"
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
    case closedLens s1' of
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
      TTensor _ _ -> pure True
      TPoint _ _ -> pure True
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
      TPoint SNil _ -> pure True
      TPoint (SVar _) _ -> pure False
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
  Charted sh r h -> do
    s <- gets (.subst)
    case closedLens (applyShape s sh) of
      Just [] -> unifyAxis p r AAnon >> pure True
      Just ls -> do
        mapM_ (\(_, a) -> unifyAxis p a (ANamed h)) ls
        unifyAxis p r (ANamed h)
        pure True
      Nothing -> pure False
  Rootward sh r pt -> do
    s <- gets (.subst)
    let sh' = applyShape s sh
        pt' = applyShape s pt
    case (closedLens sh', closedLens pt') of
      (Just _, _) -> rooted (unifyShape p pt' (rootward sh' (applyAxis s r)))
      (_, Just ls) -> do
        positions <- mapM (\(l, _) -> (l,) <$> freshAxis) ls
        unifyShape p sh' (appendShape positions SNil)
        rooted (unifyShape p pt' (rootward (appendShape positions SNil) r))
      _ -> pure False
   where
    -- The unifier's own message names the axes that differ.
    rooted act = do
      st <- get
      case runStateT act st of
        Right ((), st') -> put st' >> pure True
        Left (TypeError _ detail) ->
          failAt p ("a point is along its chart's root: " <> detail)
  Dispatch r -> decide p r

{- | Choose a reading once the types say which (design §3.10). A unit on any
side of @*@, @/@ or @^@ makes it unit arithmetic and any other known type
the arithmetic of amounts; an amount and a unit together are refused,
never converted (U2). A quantity is read by what follows its literal, or
by its result where that already says; a @to@ by its target, or by its
value or result. Returns whether the reading was chosen.
-}
decide :: Path -> Reading -> Infer Bool
decide p = \case
  reading@(Arith name a b r (Parts _ _ _ d1 d2)) -> do
    ts <- mapM resolve [a, b, r]
    let units = [() | TUnit _ <- ts]
        amounts = [() | TTensor _ _ <- ts]
        known = [() | t <- ts, not (isTypeVar t)]
    case (units, amounts, known) of
      (_ : _, _ : _, _) -> failAt p (mixed name)
      (_ : _, _, _) -> do
        unify (0 : p) (TUnit d1) a
        unify (1 : p) (TUnit d2) b
        unify p (TUnit (if name == "div" then dimDiv d1 d2 else dimMul d1 d2)) r
        pure True
      (_, _, _ : _) -> amountReading p reading >> pure True
      _ -> pure False
  reading@(Power n d b r) -> do
    ts <- mapM resolve [b, r]
    if any isUnit ts
      then do
        unify (0 : p) (TUnit d) b
        unify p (TUnit (dimPow (fromIntegral n) d)) r
        pure True
      else
        if all isTypeVar ts
          then pure False
          else amountReading p reading >> pure True
  Quantity marker written lit atom res -> do
    atom' <- resolve atom
    res' <- resolve res
    case (atom', res') of
      (TUnit d, _) -> scaleReading d
      (TScale sh r d, _) -> chartReading sh r d
      (TVar _, TTensor _ _) -> do
        d <- freshDim
        unify (1 : p) (TUnit d) atom
        scaleReading d
      (TVar _, TPoint _ _) -> do
        (sh, r, d) <- freshChart
        unify (1 : p) (TScale sh r d) atom
        chartReading sh r d
      (TVar _, _) -> pure False
      (other, _) ->
        failAt
          (1 : p)
          ( maybe "this" (\w -> "`" <> w <> "`") written
              <> " is "
              <> renderType other
              <> ", not a unit or a chart: write the `*`"
          )
   where
    scaleReading d = do
      s <- freshShape
      unify (0 : p) (TTensor s dimOne) lit
      unify p (TTensor s d) res
      choose marker "scale"
    chartReading sh r d = do
      t <- freshShape
      unify (0 : p) (TTensor sh dimOne) lit
      unify p (TPoint t d) res
      defer p (Rootward sh r t)
      choose marker "pointOn"
  Convert marker val tgt res -> do
    tgt' <- resolve tgt
    val' <- resolve val
    res' <- resolve res
    case (tgt', val', res') of
      (TUnit d, _, _) -> unitTo d
      (TScale sh r d, _, _) -> chartTo sh r d
      (TVar _, v, w)
        | any isAmount [v, w] -> do
            d <- freshDim
            unify (1 : p) (TUnit d) tgt
            unitTo d
        | any isPoint [v, w] -> do
            (sh, r, d) <- freshChart
            unify (1 : p) (TScale sh r d) tgt
            chartTo sh r d
        | otherwise -> pure False
      (TTensor _ _, _, _) ->
        failAt
          (1 : p)
          "an amount after `to`, which takes a unit or a chart: write the unit, as in to km or to km/h"
      (other, _, _) ->
        failAt (1 : p) ("`to` takes a unit or a chart, not " <> renderType other)
   where
    unitTo d = do
      s <- freshShape
      unify (0 : p) (TTensor s d) val
      unify p (TTensor s d) res
      choose marker "to"
    chartTo sh r d = do
      t <- freshShape
      unify (0 : p) (TPoint t d) val
      unify p (TPoint t d) res
      defer p (Rootward sh r t)
      choose marker "toScale"
  UnitOf a r -> do
    a' <- resolve a
    case a' of
      TUnit d -> unify p (TUnit d) r >> pure True
      TVar _ -> pure False
      _ -> amountReading p (UnitOf a r) >> pure True
 where
  isAmount = \case
    TTensor _ _ -> True
    _ -> False
  isPoint = \case
    TPoint _ _ -> True
    _ -> False
  freshChart = (,,) <$> freshShape <*> freshAxis <*> freshDim
  choose marker prim = do
    modify' (\st -> st{chosen = Map.insert marker prim st.chosen})
    pure True
  mixed name =
    "an amount and a unit together: "
      <> (if name == "div" then "/" else "*")
      <> " takes two amounts or two units"

{- | The reading of amounts, which arithmetic and a unit's declaration take
when the types have not chosen by generalisation (design §3.10, U2): the
types they had before units were a type, the product's shape constraint
with them.
-}
amountReading :: Path -> Reading -> Infer ()
amountReading p = \case
  Arith "div" a b r (Parts s _ _ d1 d2) -> do
    unify (0 : p) (TTensor s d1) a
    unify (1 : p) (numD d2) b
    unify p (TTensor s (dimDiv d1 d2)) r
  Arith _ a b r (Parts s1 s2 s3 d1 d2) -> do
    defer p (Append s1 s2 s3)
    unify (0 : p) (TTensor s1 d1) a
    unify (1 : p) (TTensor s2 d2) b
    unify p (TTensor s3 (dimMul d1 d2)) r
  Power n d b r -> do
    unify (0 : p) (numD d) b
    unify p (numD (dimPow (fromIntegral n) d)) r
  UnitOf a r -> do
    d <- freshDim
    a' <- resolve a
    case a' of
      TTensor (SCons{}) _ ->
        failAt
          (0 : p)
          ( "a unit is one number, not "
              <> renderType a'
              <> ": declare it as an amount, 60 s, or a unit, kg*m/s^2"
          )
      _ -> pure ()
    unify (0 : p) (numD d) a
    unify p (TUnit d) r
  -- Not reached: these are refused as ambiguous instead.
  Quantity{} -> pure ()
  Convert{} -> pure ()

isTypeVar :: Type -> Bool
isTypeVar = \case
  TVar _ -> True
  _ -> False

isUnit :: Type -> Bool
isUnit = \case
  TUnit _ -> True
  _ -> False

{- | At a generalisation point, constraints that only mention variables about
to be quantified cannot wait: default them (design §4.2). The unknown-rank
operand of a product is taken to be a scalar; an unknown equality type is
taken to be `Num`. Constraints that mention variables of the enclosing
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
  put st{pending = stay}
  forM_ (reverse dflt) $ \(p, c) -> case applyC s c of
    Append s1 _ _ -> unifyShape p s1 SNil >> defer p c
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
    -- A chart's shape still unknown is taken to be scalar, as a product's
    -- operand of unknown rank is: no type says "the root's axes at every
    -- position" of a shape variable, and taking the chart's own would
    -- label a point's base-form numbers with the chart's axes.
    Charted sh _ _ -> unifyShape p sh SNil >> defer p c
    Rootward sh _ _ -> unifyShape p sh SNil >> defer p c
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

{- | The readings still open at a generalisation point that only mention
variables about to be quantified (design §3.10). A quantity or a @to@ is
refused as ambiguous: its readings are different operations, and a scheme
cannot carry the choice. Arithmetic and a unit's declaration take the
amount reading (U2), which may install a product's shape constraint for
'settle' to default after.
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
      inOrder = reverse readings
  forM_ inOrder $ \(p, c) -> case c of
    Dispatch Quantity{} ->
      failAt
        p
        "ambiguous: what follows this literal could be a unit or a chart; give the definition a signature, as in per :: forall d. Unit d -> Num d"
    Dispatch Convert{} ->
      failAt
        p
        "ambiguous: `to` here could take a unit or a chart; give the definition a signature that says which"
    _ -> pure ()
  put st{pending = rest}
  forM_ inOrder $ \(p, c) -> case c of
    Dispatch r -> amountReading p r
    _ -> pure ()
  solvePending

applyC :: Subst -> Constraint -> Constraint
applyC s = \case
  Append a b c -> Append (applyShape s a) (applyShape s b) (applyShape s c)
  EqInstance t -> EqInstance (applyType s t)
  OrdInstance t -> OrdInstance (applyType s t)
  Rank sh l -> Rank (applyShape s sh) (applyLen s l)
  Charted sh r h -> Charted (applyShape s sh) (applyAxis s r) h
  Rootward sh r pt -> Rootward (applyShape s sh) (applyAxis s r) (applyShape s pt)
  Dispatch r -> Dispatch $ case r of
    Arith n a b c parts -> Arith n (ty a) (ty b) (ty c) parts
    Power k d b c -> Power k d (ty b) (ty c)
    Quantity m w a b c -> Quantity m w (ty a) (ty b) (ty c)
    Convert m a b c -> Convert m (ty a) (ty b) (ty c)
    UnitOf a b -> UnitOf (ty a) (ty b)
 where
  ty = applyType s

-- | The types a reading is between.
readingTypes :: Reading -> [Type]
readingTypes = \case
  Arith _ a b c _ -> [a, b, c]
  Power _ _ b c -> [b, c]
  Quantity _ _ a b c -> [a, b, c]
  Convert _ a b c -> [a, b, c]
  UnitOf a b -> [a, b]

constraintVars :: Constraint -> [VarId]
constraintVars = \case
  Append a b c -> map fst (concatMap (freeVars . (`TTensor` dimOne)) [a, b, c])
  EqInstance t -> map fst (freeVars t)
  OrdInstance t -> map fst (freeVars t)
  Rank sh l -> map fst (freeVars (TTensor (SCons l AAnon sh) dimOne))
  Charted sh r _ -> map fst (freeVars (TScale sh r dimOne))
  Rootward sh r pt -> map fst (freeVars (TFun (TScale sh r dimOne) (TPoint pt dimOne)))
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
    TPoint _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TUnit d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TScale _ _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TData _ args -> concatMap argExponents args
    TFun a b -> exponents v a ++ exponents v b
    TVar _ -> []
   where
    argExponents = \case
      AType t -> exponents v t
      ADim d -> [k | (DVar w, k) <- dimAtoms d, w == v]
      _ -> []

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
        statics =
          [ case unmarked a of
              Lit l -> Just (LitArg l)
              Con c [] -> Just (ConArg c)
              _ -> Nothing
          | a <- args
          ]
        positional = name `elem` ["contract", "permute", "slice"]
    -- contract, permute and slice (design §4.2): the scheme is computed
    -- from the literal positions, then used like any other; a chart that
    -- introduces axes reads them off its first argument (design §3.9).
    t <- case primSchemeFor name statics of
      Just (Right sc) -> fst <$> instantiate sc
      Just (Left msg) -> failAt p msg
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
    chartConstraints p name t statics
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
              if name `elem` ["sin", "cos", "tan"]
                then unifyMsg (i : p) param a (name <> " takes an angle: write 1 rad or 45 deg")
                else unify (i : p) param a
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
  -- A power of an amount or of a unit (design §3.10, U2).
  Pow b n -> do
    (tb, b') <- infer look (0 : p) ctx b
    d <- freshDim
    r <- freshType
    defer p (Dispatch (Power n d tb r))
    r' <- resolve r
    pure (r', TPow b' n)
  Noise k l n -> pure (vecT (LLit (fromIntegral n)), TNoise k l n)
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
    pure (TTensor (SCons (LLit (length ts)) ax elemShape) elemDim, TPack ax ts')
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
      -- A component of a point is a point (design §3.6).
      TPoint (SCons (LLit n) _ rest) d
        | i < n -> pure (TPoint rest d)
        | otherwise ->
            failAt
              p
              ( "position "
                  <> tshow i
                  <> " is out of range for a point over a vector of length "
                  <> tshow n
              )
      TPoint (SCons l _ rest) d -> do
        atLeast <- freshLen (i + 1)
        unifyLen p l atLeast
        pure (TPoint rest d)
      TPoint SNil _ -> failAt p ("cannot project ." <> tshow i <> " from a scalar point")
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

{- | What the chart primitives' schemes cannot say over a shape variable
(design §3.9), deferred as constraints at the type a primitive is used
at ('chartRelation' is lint's side): a root chart's axes and root, and
that a point lies along its chart's root. A chart that mints axes takes
the constructor of a minted axis type.
-}
chartConstraints :: Path -> Text -> Type -> [Maybe StaticArg] -> Infer ()
chartConstraints p name t statics = case (name, t, statics) of
  ( "mkScale"
    , TFun _ (TFun _ (TFun (TTensor sh _) (TScale _ r _)))
    , Just (ConArg (UserCon h _)) : _
    ) -> do
      minted h
      defer p (Charted sh r h)
  (_, _, Just (ConArg (UserCon h _)) : _)
    | name `elem` ["mkChart4", "mkChart5"] -> minted h
  ("pointOn", TFun (TScale sh r _) (TFun _ (TPoint pt _)), _) -> defer p (Rootward sh r pt)
  ("toScale", TFun (TPoint pt _) (TFun (TScale sh r _) _), _) -> defer p (Rootward sh r pt)
  _ -> pure ()
 where
  minted h = do
    defs <- gets (.typeDefs)
    case defs h of
      Just def | isAxesDef def -> pure ()
      _ ->
        failAt
          p
          ( name
              <> " takes the axes a chart declaration mints first: declare the chart with chart"
          )

{- | The type a primitive is used at: a fresh instance of its scheme, or for
the relational primitives (design §4.2) fresh shapes with a pending
constraint between them.
-}
primType :: Path -> Text -> Int -> Infer Type
primType p name argc = do
  t <- case name of
    -- Two amounts or two units (design §3.10, U2), chosen by the operands'
    -- types: the amounts' product is relational in its shapes (§4.2).
    _ | name `elem` ["outer", "div"] -> do
      -- In the order the amounts' types made them, so that dimensions
      -- solve as they did: div's shape and dimensions; outer's shapes,
      -- then dimensions.
      parts <-
        if name == "div"
          then do
            s <- freshShape
            Parts s s s <$> freshDim <*> freshDim
          else
            Parts
              <$> freshShape
              <*> freshShape
              <*> freshShape
              <*> freshDim
              <*> freshDim
      a <- freshType
      b <- freshType
      r <- freshType
      defer p (Dispatch (Arith name a b r parts))
      pure (TFun a (TFun b r))
    -- A unit's declaration (U7): an amount, the unit's size, or a unit.
    "unit" -> do
      a <- freshType
      r <- freshType
      defer p (Dispatch (UnitOf a r))
      pure (TFun a r)
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
    TPack ax ts -> TPack (applyAxis s ax) (map go ts)
    TProj t i -> TProj (go t) i
    TTyLam v k b -> TTyLam v k (go b)
    TTyApp b arg -> TTyApp (go b) (applyArg s arg)
    TCycle vs members bodies ->
      TCycle vs (vecMap (second (applyType s)) members) (vecMap go bodies)

-- Readings ----------------------------------------------------------------------------

{- | Write the readings inference chose ('readingsOf') into a term (design
§3.10, U4, U6): a quantity's marker becomes @scale lit u@ or @pointOn c
lit@, a @to@'s marker the display unit's @to@ or @toScale@. A marker with
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
    PrimApp p as -> PrimApp p (map go as)
    Var i -> Var i
    Ref h i hint -> Ref h i hint
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

-- | Whether a term has a quantity or @to@ whose reading is still to choose.
hasReadingMarkers :: Term n -> Bool
hasReadingMarkers = \case
  PrimApp p as -> isQuantityMarker p || isToMarker p || any hasReadingMarkers as
  Var _ -> False
  Ref{} -> False
  Lit _ -> False
  Lam _ b -> hasReadingMarkers b
  App a b -> hasReadingMarkers a || hasReadingMarkers b
  Let _ e b -> hasReadingMarkers e || hasReadingMarkers b
  Con _ as -> any hasReadingMarkers as
  Case s alts -> hasReadingMarkers s || any (\(Alt _ _ b) -> hasReadingMarkers b) alts
  Pow t _ -> hasReadingMarkers t
  Noise{} -> False
  Uncertain _ _ x e -> hasReadingMarkers x || hasReadingMarkers e
  Pack ts -> any hasReadingMarkers ts
  Proj t _ -> hasReadingMarkers t
  Cycle _ bs -> any hasReadingMarkers (vecToList bs)

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

vecZip3 :: Vec k a -> Vec k b -> Vec k c -> Vec k (a, b, c)
vecZip3 as bs cs = case (as, bs, cs) of
  (VNil, VNil, VNil) -> VNil
  (VCons a as', VCons b bs', VCons c cs') -> VCons (a, b, c) (vecZip3 as' bs' cs')

vecZipWith :: (a -> b -> c) -> Vec k a -> Vec k b -> Vec k c
vecZipWith f as bs = case (as, bs) of
  (VNil, VNil) -> VNil
  (VCons a as', VCons b bs') -> VCons (f a b) (vecZipWith f as' bs')

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
