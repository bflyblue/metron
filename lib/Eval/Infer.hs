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
-}
module Eval.Infer (
  TypeError (..),
  TypeLookup,
  elaborateClosed,
  inferClosed,
  matchesQuery,
) where

import Control.Monad (foldM, forM_, unless, zipWithM, zipWithM_)
import Control.Monad.State.Strict (StateT, get, gets, modify', put, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.List (isSuffixOf, minimumBy, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Desugar (Path)
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

data St = St
  { subst :: Subst
  , next :: Int
  , pending :: [(Path, Constraint)]
  -- ^ reversed paths, as 'failAt' takes them
  , typeDefs :: Hash -> Maybe TypeDef
  -- ^ the declared types, for equality on them
  }

type Infer = StateT St (Either TypeError)

{- | Infer and elaborate a closed term: its scheme(s), one per cycle member,
and the Typed Core term with all metavariables resolved.
-}
elaborateClosed :: TypeLookup -> Term Z -> Either TypeError ([Scheme], TTerm Z)
elaborateClosed look term = do
  ((schemes, tt), st) <- runStateT go (St emptySubst 0 [] look.typeDefOf)
  pure (map (applyScheme st.subst) schemes, zonk st.subst tt)
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
abstractOver vs t = foldr (\(v, k) -> TTyLam v k) t vs

fresh :: Kind -> Infer Arg
fresh k = do
  st <- get
  put st{next = st.next + 1}
  pure $ case k of
    KType -> AType (TVar st.next)
    KLen -> ALen (LVar st.next 0)
    KShape -> AShape (SVar st.next)
    KDim -> ADim (dimVar st.next)

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
    (TTuple as, TTuple bs)
      | length as == length bs -> zipWithM_ (unify p) as bs
      | otherwise ->
          failAt
            p
            ( "expected a tuple of "
                <> tshow (length as)
                <> " components, got one of "
                <> tshow (length bs)
            )
    (TList a1, TList a2) -> unify p a1 a2
    (TData h1 as, TData h2 bs)
      | h1 == h2 && length as == length bs -> zipWithM_ unifyArg as bs
    (TPoint s1 d1, TPoint s2 d2) -> shapeAndDims s1 d1 s2 d2
    (TScale s1 d1, TScale s2 d2) -> shapeAndDims s1 d1 s2 d2
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
            <> ": a point and an amount; a point has no sum, multiple or unit; use .+ and .-, or to with a scale (design §3.6)"
        )
    (TTensor _ _, TPoint _ _) ->
      failAt
        p
        ( "expected "
            <> renderType e
            <> ", got "
            <> renderType a
            <> ": an amount and a point; a point has no sum, multiple or unit; use .+ and .-, or to with a scale (design §3.6)"
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
      trivial = case arg of
        AType (TVar w) -> w == v
        AShape (SVar w) -> w == v
        ALen (LVar w 0) -> w == v
        ADim d -> d == dimVar v
        _ -> False
  unless trivial
    $ if occurs
      then failAt p "cannot construct an infinite type"
      else modify' (\st -> st{subst = Map.insert v arg st.subst})

-- | Element-wise, with a shape variable allowed at the tail.
unifyShape :: Path -> Shape -> Shape -> Infer ()
unifyShape p x y = do
  s <- gets (.subst)
  case (applyShape s x, applyShape s y) of
    (SNil, SNil) -> pure ()
    (SVar v, sh) -> bindVar p v (AShape sh)
    (sh, SVar v) -> bindVar p v (AShape sh)
    (SCons l1 r1, SCons l2 r2) -> unifyLen p l1 l2 >> unifyShape p r1 r2
    (SNil, SCons _ _) -> failAt p "a number is not a vector"
    (SCons _ _, SNil) -> failAt p "a vector is not a number"

{- | Design §4.1: literals must agree; a variable plus offset against a
literal solves the variable when the literal is large enough; two offset
forms solve for the smaller offset.
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
      TBool -> pure True
      TPoint _ _ -> pure True
      -- Structured data compares when its components do.
      TTuple ts -> mapM_ (defer p . EqInstance) ts >> pure True
      TList elt -> defer p (EqInstance elt) >> pure True
      -- A declared type compares when its fields do (design §4.2).
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
  s <- gets (.subst)
  let envVars = concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
      touchesEnv c = any (`elem` envVars) (constraintVars (applyC s c))
      outside p = not (here `isSuffixOf` p)
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
  solvePending
 where
  partitionWith f xs = (filter f xs, filter (not . f) xs)

applyC :: Subst -> Constraint -> Constraint
applyC s = \case
  Append a b c -> Append (applyShape s a) (applyShape s b) (applyShape s c)
  EqInstance t -> EqInstance (applyType s t)
  OrdInstance t -> OrdInstance (applyType s t)

constraintVars :: Constraint -> [VarId]
constraintVars = \case
  Append a b c -> map fst (concatMap (freeVars . (`TTensor` dimOne)) [a, b, c])
  EqInstance t -> map fst (freeVars t)
  OrdInstance t -> map fst (freeVars t)

-- Generalisation and instantiation ---------------------------------------------------

{- | Quantify the variables of a type that are free in neither the context
nor a constraint still pending: such a constraint ties its variables to
the context (or to a term outside this one), and quantifying them would
cut that tie, as in @\k -> let g = \v -> k * v in g [1, 2]@, which once
typed its result as any shape at all.

Kennedy's algorithm may solve for the inverse of a variable, giving
@Num [d^-2] -> Num [d^-3]@ where @Num [d^2] -> Num [d^3]@ means the same
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
    TBool -> []
    TTensor _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TPoint _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TScale _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
    TTuple parts -> concatMap (exponents v) parts
    TList t -> exponents v t
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
  -- caught `cross` elaborating to `Vec 3 [m] -> Vec 3 [m/s] -> Vec 3 [m^2]`).
  pure (substOnce m t, args)

applyArgs :: TTerm n -> [Arg] -> TTerm n
applyArgs = foldl TTyApp

-- Inference ----------------------------------------------------------------------------

infer :: TypeLookup -> Path -> Vec n Scheme -> Term n -> Infer (Type, TTerm n)
infer look p ctx = \case
  Var i -> do
    (t, args) <- instantiate (lookupCtx i ctx)
    pure (t, applyArgs (TVr i) args)
  Ref h idx hint -> case look.schemesOf h of
    Nothing -> failAt p "reference to a definition with no stored type"
    Just schemes -> case nth (fromMaybe 0 idx) schemes of
      Just sc -> do
        (t, args) <- instantiate sc
        pure (t, applyArgs (TRef h idx hint) args)
      Nothing -> failAt p "reference to a cycle member that does not exist"
  PrimApp name args -> do
    t <- primType p name (length args)
    typed <- zipWithM (\i a -> infer look (i : p) ctx a) [0 ..] args
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
  Lit l@(LTensor (dims, _)) -> pure (TTensor (shapeOfDims dims) dimOne, TLit l)
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
    sc@(Forall vs _) <- generalise ctx te
    (tb, body') <- infer look (1 : p) (VCons sc ctx) body
    pure (tb, TLet h sc (abstractOver vs e') body')
  Pow b n -> do
    (tb, b') <- infer look (0 : p) ctx b
    d <- freshDim
    unify (0 : p) (numD d) tb
    pure (numD (dimPow (fromIntegral n) d), TPow b' n)
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
      (TTensor (SCons _ (SCons _ SNil)) _, SCons n SNil)
        | k == Stat ->
            unifyMsg
              (1 : p)
              (TTensor (SCons n (SCons n SNil)) (dimPow 2 d))
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
              "every element of a tensor literal must have the same shape"
            pure t'
        )
        [0 ..]
        ts
    pure (TTensor (SCons (LLit (length ts)) elemShape) elemDim, TPack ts')
  Proj t i -> do
    (tt0, t') <- infer look (0 : p) ctx t
    tt <- resolve tt0
    ty <- case tt of
      TTensor (SCons (LLit n) rest) d
        | i < n -> pure (TTensor rest d)
        | otherwise ->
            failAt
              p
              ("position " <> tshow i <> " is out of range for a vector of length " <> tshow n)
      TTensor (SCons l rest) d -> do
        atLeast <- freshLen (i + 1)
        unifyLen p l atLeast
        pure (TTensor rest d)
      TTensor SNil _ -> failAt p ("cannot project ." <> tshow i <> " from a number")
      -- A component of a point is a point (design §3.6).
      TPoint (SCons (LLit n) rest) d
        | i < n -> pure (TPoint rest d)
        | otherwise ->
            failAt
              p
              ( "position "
                  <> tshow i
                  <> " is out of range for a point over a vector of length "
                  <> tshow n
              )
      TPoint (SCons l rest) d -> do
        atLeast <- freshLen (i + 1)
        unifyLen p l atLeast
        pure (TPoint rest d)
      TPoint SNil _ -> failAt p ("cannot project ." <> tshow i <> " from a scalar point")
      -- Rank unknown so far: it must be at least one.
      _ -> do
        atLeast <- freshLen (i + 1)
        rest <- freshShape
        d <- freshDim
        unify (0 : p) tt (TTensor (SCons atLeast rest) d)
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
      Left _ -> do
        e <- resolve expected
        a <- resolve actual
        failAt p' (msg <> ": expected " <> renderType e <> ", got " <> renderType a)

{- | The type a primitive is used at: a fresh instance of its scheme, or for
the relational primitives (design §4.2) fresh shapes with a pending
constraint between them.
-}
primType :: Path -> Text -> Int -> Infer Type
primType p name argc = do
  t <- case name of
    "outer" -> do
      s1 <- freshShape
      s2 <- freshShape
      s3 <- freshShape
      d1 <- freshDim
      d2 <- freshDim
      defer p (Append s1 s2 s3)
      pure (TFun (TTensor s1 d1) (TFun (TTensor s2 d2) (TTensor s3 (dimMul d1 d2))))
    "dot" -> do
      s1 <- freshShape
      n <- freshLen 0
      s2 <- freshShape
      left <- freshShape
      s3 <- freshShape
      d1 <- freshDim
      d2 <- freshDim
      defer p (Append s1 (SCons n SNil) left)
      defer p (Append s1 s2 s3)
      pure
        ( TFun
            (TTensor left d1)
            (TFun (TTensor (SCons n s2) d2) (TTensor s3 (dimMul d1 d2)))
        )
    _ | name == "eq" || name == "ne" -> do
      a <- freshType
      defer p (EqInstance a)
      pure (TFun a (TFun a TBool))
    _ | name `elem` ["lt", "le", "gt", "ge"] -> do
      a <- freshType
      defer p (OrdInstance a)
      pure (TFun a (TFun a TBool))
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
    TLit l -> TLit l
    TLam h ty b -> TLam h (applyType s ty) (go b)
    TApp f a -> TApp (go f) (go a)
    TLet h sc e b -> TLet h (applyScheme s sc) (go e) (go b)
    TCon c ty args -> TCon c (applyType s ty) (map go args)
    TCase sc ty alts ->
      TCase
        (go sc)
        (applyType s ty)
        ( map
            (\(TAlt c bs b) -> TAlt c (vecMap (\(h, t) -> (h, applyType s t)) bs) (go b))
            alts
        )
    TPow b n -> TPow (go b) n
    TNoise k l n -> TNoise k l n
    TUncertain k l x e -> TUncertain k l (go x) (go e)
    TPack ts -> TPack (map go ts)
    TProj t i -> TProj (go t) i
    TTyLam v k b -> TTyLam v k (go b)
    TTyApp b arg -> TTyApp (go b) (applyArg s arg)
    TCycle vs members bodies ->
      TCycle vs (vecMap (\(h, ty) -> (h, applyType s ty)) members) (vecMap go bodies)

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
  Builtin "True" | k == 0 -> pure ([], TBool)
  Builtin "False" | k == 0 -> pure ([], TBool)
  Builtin "Tuple" | k >= 2 -> do
    ts <- mapM (const freshType) [1 .. k]
    pure (ts, TTuple ts)
  Builtin "Nil" | k == 0 -> (\t -> ([], TList t)) <$> freshType
  Builtin "Cons" | k == 2 -> (\t -> ([t, TList t], TList t)) <$> freshType
  -- A declared type: fresh arguments for its parameters, by kind.
  UserCon h i | Just def <- look.typeDefOf h -> do
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
              <> ( if c `elem` [Builtin "True", Builtin "False"]
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
  attach (VCons h rest) [] = VCons (h, TBool) (attach rest []) -- unreachable: lengths were checked

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
@Num -> Num@ and @Num [m] -> Num [m]@ matches a query @a -> a@.
-}
matchesQuery :: Scheme -> Scheme -> Bool
matchesQuery query sc = case runStateT go (St emptySubst 0 [] (const Nothing)) of
  Right _ -> True
  Left _ -> False
 where
  go = do
    (q, _) <- instantiate query
    (t, _) <- instantiate sc
    unify [] q t
