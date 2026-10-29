-- | Hindley-Milner inference over Core (design §4.5) and elaboration to Typed
-- Core (§5.3) in one pass: every node is typed and rebuilt with explicit
-- annotations, kinded abstractions at generalisation points and kinded
-- applications at uses of polymorphic names. Errors carry the path of the
-- node that failed (§4.7).
--
-- Two primitives have relational types (§4.2): the tensor product and the
-- contracting product need shape concatenation, and equality is an instance
-- constraint over tensors and booleans. These are carried as pending
-- constraints, solved as soon as the shapes involved are known, and defaulted
-- at generalisation when they cannot be.
module Eval.Infer
  ( TypeError (..)
  , TypeLookup
  , elaborateClosed
  , inferClosed
  ) where

import Control.Monad (foldM, forM_, unless, zipWithM)
import Control.Monad.State.Strict (StateT, get, gets, modify', put, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.List (nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.List (minimumBy)
import Data.Ord (comparing)
import Eval.Core
import Eval.Desugar (Path)
import Eval.Dimension
import Eval.TCore
import Eval.Type

-- | A type error at a path into the term being checked. Inside a 'Cycle' the
-- path starts with the member index.
data TypeError = TypeError {path :: Path, message :: Text}
  deriving stock (Eq, Show)

-- | Types of codebase definitions, one scheme per cycle member.
type TypeLookup = Hash -> Maybe [Scheme]

-- | A deferred relation between types (design §4.2).
data Constraint
  = -- | @s3 ~ s1 ++ s2@
    Append Shape Shape Shape
  | -- | @Eq τ@: τ is a tensor or Bool
    EqInstance Type

data St = St
  { subst :: Subst
  , next :: Int
  , pending :: [(Path, Constraint)] -- ^ reversed paths, as 'failAt' takes them
  }

type Infer = StateT St (Either TypeError)

-- | Infer and elaborate a closed term: its scheme(s), one per cycle member,
-- and the Typed Core term with all metavariables resolved.
elaborateClosed :: TypeLookup -> Term Z -> Either TypeError ([Scheme], TTerm Z)
elaborateClosed look term = do
  ((schemes, tt), st) <- runStateT go (St emptySubst 0 [])
  pure (map (applyScheme st.subst) schemes, zonk st.subst tt)
  where
    go = case term of
      Cycle hints bodies -> do
        vars <- vecTraverse (const freshType) bodies
        let ctx = vecAppend (vecMap (Forall []) vars) VNil
        bodies' <-
          vecTraverse
            (\(i, body, v) -> do
               (t, body') <- infer look [i] ctx body
               unify [i] v t
               pure body')
            (vecZip3 (indices bodies) bodies vars)
        settle VNil
        schemes <- mapM (generalise VNil) (vecToList vars)
        s <- gets (.subst)
        let quantified = nubBy (\a b -> fst a == fst b) (concat [vs | Forall vs _ <- schemes])
            members = vecZipWith (\h v -> (h, applyType s v)) hints vars
        pure (schemes, TCycle quantified members bodies')
      _ -> do
        (t, tt) <- infer look [] VNil term
        settle VNil
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
  put st {next = st.next + 1}
  pure $ case k of
    KType -> AType (TVar st.next)
    KLen -> ALen (LVar st.next 0)
    KShape -> AShape (SVar st.next)
    KDim -> ADim (dimVar st.next)

freshDim :: Infer Dim
freshDim = fresh KDim >>= \case
  ADim d -> pure d
  _ -> error "fresh KDim"

freshType :: Infer Type
freshType = fresh KType >>= \case
  AType t -> pure t
  _ -> error "fresh KType"

freshLen :: Int -> Infer Len
freshLen offset = fresh KLen >>= \case
  ALen (LVar v _) -> pure (LVar v offset)
  _ -> error "fresh KLen"

freshShape :: Infer Shape
freshShape = fresh KShape >>= \case
  AShape s -> pure s
  _ -> error "fresh KShape"

resolve :: Type -> Infer Type
resolve t = gets (\st -> applyType st.subst t)

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
    (TTensor s1 d1, TTensor s2 d2) -> do
      st <- get
      case runStateT (unifyShape p s1 s2 >> unifyDim p d1 d2) st of
        Right ((), st') -> put st'
        Left (TypeError _ detail) ->
          failAt p ("expected " <> renderType e <> ", got " <> renderType a <> ": " <> detail)
    _ -> failAt p ("expected " <> renderType e <> ", got " <> renderType a)

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
  unless trivial $
    if occurs
      then failAt p "cannot construct an infinite type"
      else modify' (\st -> st {subst = Map.insert v arg st.subst})

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

-- | Design §4.1: literals must agree; a variable plus offset against a
-- literal solves the variable when the literal is large enough; two offset
-- forms solve for the smaller offset.
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
      | v == w -> unless (k == j) (failAt p ("lengths differ by " <> tshow (abs (k - j))))
      | j >= k -> bindVar p v (ALen (LVar w (j - k)))
      | otherwise -> bindVar p w (ALen (LVar v (k - j)))
  where
    bindLen v k j
      | j >= k = bindVar p v (ALen (LLit (j - k)))
      | otherwise = failAt p ("a vector of length " <> tshow j <> " is too short: at least " <> tshow k <> " needed")

-- | Kennedy's algorithm (design §4.4): to unify two dimensions, solve
-- @d1 · d2⁻¹ = 1@. Pick the variable with the smallest exponent; if it
-- divides every other exponent, solve for it; otherwise substitute a fresh
-- variable times the quotients and repeat, Euclid-style.
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
          if all (\(_, k) -> k `mod` x == 0) others
            then bindVar p v (ADim (dimFromAtoms [(a, negate (k `div` x)) | (a, k) <- others]))
            else do
              v' <- freshDim
              bindVar p v (ADim (dimMul v' (dimFromAtoms [(a, negate (k `div` x)) | (a, k) <- others])))
              solve d'

-- Constraints ----------------------------------------------------------------------

defer :: Path -> Constraint -> Infer ()
defer p c = do
  modify' (\st -> st {pending = (p, c) : st.pending})
  solvePending

-- | Solve every pending constraint that has become determined, repeating
-- until nothing more moves.
solvePending :: Infer ()
solvePending = do
  st <- get
  put st {pending = []}
  remaining <- foldM step [] (reverse st.pending)
  modify' (\st' -> st' {pending = remaining ++ st'.pending})
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
          | otherwise -> failAt p "the result of a product has lower rank than one of its operands"
        _ -> pure False
  EqInstance t -> do
    t' <- resolve t
    case t' of
      TTensor _ _ -> pure True
      TBool -> pure True
      TVar _ -> pure False
      _ -> failAt p ("no equality on " <> renderType t')

-- | At a generalisation point, constraints that only mention variables about
-- to be quantified cannot wait: default them (design §4.2). The unknown-rank
-- operand of a product is taken to be a scalar; an unknown equality type is
-- taken to be `Num`. Constraints that mention variables of the enclosing
-- context stay pending.
settle :: Vec n Scheme -> Infer ()
settle ctx = do
  solvePending
  s <- gets (.subst)
  let envVars = concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
      touchesEnv c = any (`elem` envVars) (constraintVars (applyC s c))
  st <- get
  let (stay, dflt) = partitionWith (touchesEnv . snd) st.pending
  put st {pending = stay}
  forM_ (reverse dflt) $ \(p, c) -> case applyC s c of
    Append s1 _ _ -> unifyShape p s1 SNil >> defer p c
    EqInstance t -> unify p numT t >> defer p c
  solvePending
  where
    partitionWith f xs = (filter f xs, filter (not . f) xs)
    applyC s = \case
      Append a b c -> Append (applyShape s a) (applyShape s b) (applyShape s c)
      EqInstance t -> EqInstance (applyType s t)
    constraintVars = \case
      Append a b c -> map fst (concatMap (freeVars . (`TTensor` dimOne)) [a, b, c])
      EqInstance t -> map fst (freeVars t)

-- Generalisation and instantiation ---------------------------------------------------

generalise :: Vec n Scheme -> Type -> Infer Scheme
generalise ctx t = do
  s <- gets (.subst)
  let t' = applyType s t
      envVars = concat [map fst (freeVars (applyType s b)) | Forall _ b <- vecToList ctx]
      quantified = filter ((`notElem` envVars) . fst) (freeVars t')
  pure (Forall quantified (positiveDims quantified t'))

-- | Kennedy's algorithm may solve for the inverse of a variable, giving
-- @Num [d^-2] -> Num [d^-3]@ where @Num [d^2] -> Num [d^3]@ means the same
-- scheme. A quantified dimension variable that only appears with negative
-- exponents is replaced by its inverse.
positiveDims :: [(VarId, Kind)] -> Type -> Type
positiveDims quantified t = foldr flipIfNegative t [v | (v, KDim) <- quantified]
  where
    flipIfNegative v ty
      | not (null (exponents v ty)) && all (< 0) (exponents v ty) = rewrite v ty
      | otherwise = ty
    exponents v = \case
      TBool -> []
      TTensor _ d -> [k | (DVar w, k) <- dimAtoms d, w == v]
      TFun a b -> exponents v a ++ exponents v b
      TVar _ -> []
    rewrite v = \case
      TBool -> TBool
      TTensor sh d -> TTensor sh (substDimVar v (dimInv (dimVar v)) d)
      TFun a b -> TFun (rewrite v a) (rewrite v b)
      TVar w -> TVar w

-- | Replace the quantified variables by fresh ones and return the arguments
-- used, for the explicit type applications. This is a one-shot renaming, not
-- 'applyType': a stored scheme's variable ids can coincide with this run's
-- fresh ids, and chasing such a binding through the substitution would never
-- terminate.
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
  Ref h idx -> case look h of
    Nothing -> failAt p "reference to a definition with no stored type"
    Just schemes -> case nth (fromMaybe 0 idx) schemes of
      Just sc -> do
        (t, args) <- instantiate sc
        pure (t, applyArgs (TRef h idx) args)
      Nothing -> failAt p "reference to a cycle member that does not exist"
  PrimApp name args -> do
    t <- primType p name (length args)
    typed <- zipWithM (\i a -> infer look (i : p) ctx a) [0 ..] args
    -- Primitive types are fully known in shape, so peel one arrow per
    -- argument and report a mismatch at the argument that caused it.
    let go i ty = \case
          [] -> pure ty
          a : rest -> case ty of
            TFun param r -> unify (i : p) param a >> go (i + 1) r rest
            _ -> failAt p ("primitive " <> name <> " applied to too many arguments")
    result <- go (0 :: Int) t (map fst typed)
    -- The arguments may have fixed the shapes a pending product constraint
    -- was waiting for; solve now so later errors print resolved types.
    solvePending
    pure (result, TPrimApp name t (map snd typed))
  Lit l@(LTensor dims _) -> pure (TTensor (shapeOfDims dims) dimOne, TLit l)
  Lit l@(LBool _) -> pure (TBool, TLit l)
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
      _ -> failAt (0 : p) (renderType tf' <> " is not a function and cannot be applied")
    pure (r, TApp f' a')
  Let h e body -> do
    (te, e') <- infer look (0 : p) ctx e
    settle ctx
    sc@(Forall vs _) <- generalise ctx te
    (tb, body') <- infer look (1 : p) (VCons sc ctx) body
    pure (tb, TLet h sc (abstractOver vs e') body')
  If c t e -> do
    (tc, c') <- infer look (0 : p) ctx c
    unifyMsg (0 : p) TBool tc "the condition of `if` must be a Bool"
    (tt, t') <- infer look (1 : p) ctx t
    (te, e') <- infer look (2 : p) ctx e
    unifyMsg (2 : p) tt te "both branches of `if` must have the same type"
    pure (tt, TIf c' t' e')
  Pow b n -> do
    (tb, b') <- infer look (0 : p) ctx b
    d <- freshDim
    unify (0 : p) (numD d) tb
    pure (numD (dimPow (fromIntegral n) d), TPow b' n)
  Noise k n -> pure (vecT (LLit (fromIntegral n)), TNoise k n)
  Uncertain k x e -> do
    d <- freshDim
    (tx, x') <- infer look (0 : p) ctx x
    unify (0 : p) (numD d) tx
    (te, e') <- infer look (1 : p) ctx e
    unifyMsg (1 : p) (numD d) te "the uncertainty must have the dimension of the value"
    pure (numD d, TUncertain k x' e')
  Pack ts -> do
    elemShape <- freshShape
    elemDim <- freshDim
    let elemT = TTensor elemShape elemDim
    ts' <-
      zipWithM
        (\i t -> do
           (tt, t') <- infer look (i : p) ctx t
           unifyMsg (i : p) elemT tt "every element of a tensor literal must have the same shape"
           pure t')
        [0 ..]
        ts
    pure (TTensor (SCons (LLit (length ts)) elemShape) elemDim, TPack ts')
  Proj t i -> do
    (tt0, t') <- infer look (0 : p) ctx t
    tt <- resolve tt0
    ty <- case tt of
      TTensor (SCons (LLit n) rest) d
        | i < n -> pure (TTensor rest d)
        | otherwise -> failAt p ("position " <> tshow i <> " is out of range for a vector of length " <> tshow n)
      TTensor (SCons l rest) d -> do
        atLeast <- freshLen (i + 1)
        unifyLen p l atLeast
        pure (TTensor rest d)
      TTensor SNil _ -> failAt p ("cannot project ." <> tshow i <> " from a number")
      -- Rank unknown so far: it must be at least one.
      _ -> do
        atLeast <- freshLen (i + 1)
        rest <- freshShape
        d <- freshDim
        unify (0 : p) tt (TTensor (SCons atLeast rest) d)
        pure (TTensor rest d)
    pure (ty, TProj t' i)
  Cycle {} -> failAt p "a cycle cannot appear inside an expression"
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

-- | The type a primitive is used at: a fresh instance of its scheme, or for
-- the relational primitives (design §4.2) fresh shapes with a pending
-- constraint between them.
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
      pure (TFun (TTensor left d1) (TFun (TTensor (SCons n s2) d2) (TTensor s3 (dimMul d1 d2))))
    _ | name == "eq" || name == "ne" -> do
      a <- freshType
      defer p (EqInstance a)
      pure (TFun a (TFun a TBool))
    _ -> case primScheme name of
      Just sc -> fst <$> instantiate sc
      Nothing -> failAt p ("unknown primitive " <> name)
  let arity = countArrows t
  unless (argc == arity) $
    failAt p ("primitive " <> name <> " expects " <> tshow arity <> " arguments, got " <> tshow argc)
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
      TRef h i -> TRef h i
      TPrimApp p ty args -> TPrimApp p (applyType s ty) (map go args)
      TLit l -> TLit l
      TLam h ty b -> TLam h (applyType s ty) (go b)
      TApp f a -> TApp (go f) (go a)
      TLet h sc e b -> TLet h (applyScheme s sc) (go e) (go b)
      TIf c t e -> TIf (go c) (go t) (go e)
      TPow b n -> TPow (go b) n
      TNoise k n -> TNoise k n
      TUncertain k x e -> TUncertain k (go x) (go e)
      TPack ts -> TPack (map go ts)
      TProj t i -> TProj (go t) i
      TTyLam v k b -> TTyLam v k (go b)
      TTyApp b arg -> TTyApp (go b) (applyArg s arg)
      TCycle vs members bodies -> TCycle vs (vecMap (\(h, ty) -> (h, applyType s ty)) members) (vecMap go bodies)

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
