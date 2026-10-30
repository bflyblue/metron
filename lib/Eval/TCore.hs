{- | Typed Core (design §5.3, core.md): Core after inference and elaboration,
explicitly typed in the manner of System F and GHC's Core. Every binder
carries its type, polymorphism is explicit through one kinded abstraction
form and one kinded application form, and a primitive carries the type it
is used at. The interpreter runs this; a compiler would start from it.

'lint' is the counterpart of GHC's Core Lint: a plain type checker (no
inference) that validates an elaborated term. Elaboration bugs surface
there, not in the evaluator.
-}
module Eval.TCore (
  TTerm (..),
  primScheme,
  baseUnit,
  closedLens,
  appendShape,
  lintClosed,
  renderTTerm,
  patternText,
  TAlt (..),
) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Dimension
import Eval.Type

{- | Typed Core terms in a scope of @n@ term variables. Type-level variables
are identified by number and bound by 'TTyLam' with their kind.
-}
data TTerm (n :: Nat) where
  TVr :: Fin n -> TTerm n
  TRef :: Hash -> Maybe Int -> Hint -> TTerm n
  -- | A saturated primitive at a specific type (an instance of 'primScheme').
  TPrimApp :: Text -> Type -> [TTerm n] -> TTerm n
  TLit :: Lit -> TTerm n
  TLam :: Hint -> Type -> TTerm (S n) -> TTerm n
  TApp :: TTerm n -> TTerm n -> TTerm n
  -- | The bound term has the scheme; its abstractions are explicit in it.
  TLet :: Hint -> Scheme -> TTerm n -> TTerm (S n) -> TTerm n
  -- | A constructor at its result type (@Nil@ alone fixes no element type).
  TCon :: ConRef -> Type -> [TTerm n] -> TTerm n
  -- | A case at its result type.
  TCase :: TTerm n -> Type -> [TAlt n] -> TTerm n
  TPow :: TTerm n -> Integer -> TTerm n
  TNoise :: NudgeKind -> Label -> Integer -> TTerm n
  TUncertain :: NudgeKind -> Label -> TTerm n -> TTerm n -> TTerm n
  TPack :: [TTerm n] -> TTerm n
  TProj :: TTerm n -> Int -> TTerm n
  -- | Abstraction over a type-level variable of the given kind.
  TTyLam :: VarId -> Kind -> TTerm n -> TTerm n
  -- | Application to a type-level argument.
  TTyApp :: TTerm n -> Arg -> TTerm n
  {- | Mutually recursive members, monomorphic inside the cycle at the given
  types, generalised together over the listed variables outside it.
  -}
  TCycle ::
    [(VarId, Kind)] -> Vec k (Hint, Type) -> Vec k (TTerm (Plus k n)) -> TTerm n

-- | A typed alternative: the fields enter scope at their types.
data TAlt n = forall k. TAlt ConRef (Vec k (Hint, Type)) (TTerm (Plus k n))

instance Show (TAlt n) where
  show (TAlt c bs b) = "TAlt " ++ show c ++ " " ++ show (vecToList bs) ++ " (" ++ show b ++ ")"

deriving stock instance Show (TTerm n)

-- Primitive signatures ------------------------------------------------------------

-- | The base unit a primitive stands for, if it is one (design §3.2.11).
baseUnit :: Text -> Maybe BaseDim
baseUnit = \case
  "m" -> Just L
  "kg" -> Just M
  "s" -> Just T
  "A" -> Just I
  "K" -> Just Θ
  "mol" -> Just N
  "cd" -> Just J
  "rad" -> Just Ang
  _ -> Nothing

{- | The scheme of each primitive. Quantified variables use small fixed ids;
inference instantiates them, 'lint' matches against them. See core.md
"Operators across ranks" for which are shape-polymorphic, and design §4.3
for the dimension rules.
-}
primScheme :: Text -> Maybe Scheme
primScheme name = case name of
  "add" -> Just (Forall [sv, dv] (TFun sd (TFun sd sd)))
  "sub" -> Just (Forall [sv, dv] (TFun sd (TFun sd sd)))
  "emul" -> Just (Forall [sv, dv, d2v] (TFun sd (TFun sd2 (TTensor s (dimMul d d2)))))
  "ediv" -> Just (Forall [sv, dv, d2v] (TFun sd (TFun sd2 (TTensor s (dimDiv d d2)))))
  "div" ->
    Just (Forall [sv, dv, d2v] (TFun sd (TFun (numD d2) (TTensor s (dimDiv d d2)))))
  -- outer, dot, eq and ne have constraint types; see 'lintConstrained'.
  "neg" -> Just (Forall [sv, dv] (TFun sd sd))
  "abs" -> Just (Forall [sv, dv] (TFun sd sd))
  "floor" -> num1
  "ceil" -> num1
  "round" -> num1
  "sqrt" -> Just (Forall [dv] (TFun (numD (dimPow 2 d)) (numD d)))
  -- Plane angle is a dimension (design §3.2.11): the circular functions take
  -- radians and their inverses return them.
  "sin" -> mono (TFun angleT numT)
  "cos" -> mono (TFun angleT numT)
  "tan" -> mono (TFun angleT numT)
  "asin" -> mono (TFun numT angleT)
  "acos" -> mono (TFun numT angleT)
  "atan" -> mono (TFun numT angleT)
  "sinh" -> num1
  "cosh" -> num1
  "tanh" -> num1
  "exp" -> num1
  "log" -> num1
  "atan2" -> Just (Forall [dv] (TFun (numD d) (TFun (numD d) angleT)))
  -- Points and scales (design §3.6).
  "mkScale" -> Just (Forall [sv, dv] (TFun (numD d) (TFun sd (TScale s d))))
  "pointOn" ->
    Just
      (Forall [sv, dv] (TFun (TScale s d) (TFun (TTensor s dimOne) (TPoint s d))))
  "pointAdd" -> Just (Forall [sv, dv] (TFun (TPoint s d) (TFun sd (TPoint s d))))
  "pointSub" -> Just (Forall [sv, dv] (TFun (TPoint s d) (TFun (TPoint s d) sd)))
  "toScale" -> Just (Forall [sv, dv] (TFun (TPoint s d) (TFun (TScale s d) (TPoint s d))))
  -- lt, le, gt, ge have instance types; see lintConstrained.
  "and" -> mono (TFun TBool (TFun TBool TBool))
  "or" -> mono (TFun TBool (TFun TBool TBool))
  "not" -> mono (TFun TBool TBool)
  "pi" -> mono numT
  "to" -> Just (Forall [sv, dv] (TFun sd (TFun (numD d) sd)))
  -- The wedge product is the general binary product of vectors; the 3D
  -- cross product is `star (wedge a b)` and lives in the prelude.
  "wedge" ->
    Just
      ( Forall
          [nv, dv, d2v]
          (TFun (vecD n d) (TFun (vecD n d2) (matD n n (dimMul d d2))))
      )
  "star" -> Just (Forall [dv] (TFun (matD three three d) (vecD three d)))
  "norm" -> Just (Forall [nv, dv] (TFun (vecD n d) (numD d)))
  "transpose" -> Just (Forall [nv, mv, dv] (TFun (matD n m d) (matD m n d)))
  "inverse" -> Just (Forall [nv, dv] (TFun (matD n n d) (matD n n (dimInv d))))
  -- det : Mat n n d -> Num [d^n] needs the length as an exponent; until that
  -- relation exists, det is on dimensionless matrices.
  "det" -> Just (Forall [nv] (TFun (matD n n dimOne) numT))
  -- Covariance (design §3.5): a square-root factor, the covariance of a
  -- vector's statistical nudges, and a vector with a given covariance.
  "cholesky" -> Just (Forall [nv, dv] (TFun (matD n n (dimPow 2 d)) (matD n n d)))
  "covariance" -> Just (Forall [nv, dv] (TFun (vecD n d) (matD n n (dimPow 2 d))))
  -- The parts of an enclosure (design §3.2.9), elementwise, in the
  -- operand's dimension.
  "mid" -> Just (Forall [sv, dv] (TFun sd sd))
  "bound" -> Just (Forall [sv, dv] (TFun sd sd))
  "sigma" -> Just (Forall [sv, dv] (TFun sd sd))
  "vmap" ->
    Just
      (Forall [sv, dv, d2v] (TFun (TFun (numD d) (numD d2)) (TFun sd (TTensor s d2))))
  _ -> case baseUnit name of
    Just b -> mono (numD (dimBase b))
    Nothing -> Nothing
 where
  sv = (0, KShape)
  dv = (1, KDim)
  d2v = (2, KDim)
  nv = (3, KLen)
  mv = (4, KLen)
  s = SVar 0
  d = dimVar 1
  d2 = dimVar 2
  n = LVar 3 0
  m = LVar 4 0
  three = LLit 3
  sd = TTensor s d
  sd2 = TTensor s d2
  matD r c = TTensor (SCons r (SCons c SNil))
  mono = Just . Forall []
  num1 = mono (TFun numT numT)
  angleT = numD (dimBase Ang)

-- Lint -------------------------------------------------------------------------

{- | Check a closed term and return its scheme(s): one, or one per cycle
member. The result is 'Left' only when elaboration produced an ill-typed
term, which is an internal error.
-}
lintClosed :: TypeLookup -> TTerm Z -> Either Text [Scheme]
lintClosed look = \case
  TCycle vars members bodies -> do
    let ctx = vecAppend (vecMap (Forall [] . snd) members) VNil
    sequence_
      [ do
          t <- lint look ctx body >>= asMono ("cycle member `" <> h <> "`")
          require
            (t == expected)
            ( "cycle member `"
                <> h
                <> "` has type "
                <> renderType t
                <> " but is annotated "
                <> renderType expected
            )
      | ((Hint h, expected), body) <- zip (vecToList members) (vecToList bodies)
      ]
    pure [Forall vars t | (_, t) <- vecToList members]
  t -> (: []) <$> lint look VNil t

lint ::
  TypeLookup -> Vec n Scheme -> TTerm n -> Either Text Scheme
lint look ctx = \case
  TVr i -> Right (lookupCtx i ctx)
  TRef h idx _ -> case look.schemesOf h of
    Nothing -> Left "reference to a definition with no stored type"
    Just schemes ->
      maybe
        (Left "reference to a missing cycle member")
        Right
        (nth (fromMaybe 0 idx) schemes)
  TPrimApp name ty args -> do
    case primScheme name of
      Just general ->
        require
          (ty `isInstanceOf` general)
          ( "primitive "
              <> name
              <> " used at "
              <> renderType ty
              <> ", not an instance of "
              <> renderScheme general
          )
      Nothing -> lintConstrained look name ty
    let go t = \case
          [] -> Right t
          arg : rest -> case t of
            TFun p r -> do
              ta <- monoOf arg
              require
                (ta == p)
                ( "argument of "
                    <> name
                    <> " has type "
                    <> renderType ta
                    <> ", expected "
                    <> renderType p
                )
              go r rest
            _ -> Left ("primitive " <> name <> " applied to too many arguments")
    result <- go ty args
    require (not (isFun result)) ("primitive " <> name <> " is not saturated")
    mono result
  TLit (LTensor (dims, rs)) -> do
    require
      (length rs == product dims)
      "tensor literal has the wrong number of values for its shape"
    mono (TTensor (shapeOfDims dims) dimOne)
  TLam _ ty body -> do
    tb <- lint look (VCons (Forall [] ty) ctx) body >>= asMono "lambda body"
    mono (TFun ty tb)
  TApp f a -> do
    tf <- monoOf f
    ta <- monoOf a
    case tf of
      TFun p r -> do
        require (ta == p) ("applied " <> renderType tf <> " to " <> renderType ta)
        mono r
      _ -> Left ("applied a non-function of type " <> renderType tf)
  TLet _ sc rhs body -> do
    actual <- lint look ctx rhs
    require
      (actual == sc)
      ( "let binder annotated "
          <> renderScheme sc
          <> " but bound to "
          <> renderScheme actual
      )
    lint look (VCons sc ctx) body
  -- Data (design §5.1): a constructor's fields match the table at its
  -- result type; a case covers its scrutinee's constructors exactly, binds
  -- the fields at their types, and every body has the result type.
  TCon c ty args -> do
    fts <-
      maybe
        (Left ("constructor " <> conText c <> " does not build " <> renderType ty))
        Right
        (lookup c =<< dataConstructors look.typeDefOf ty)
    require
      (length fts == length args)
      ( "constructor "
          <> conText c
          <> " applied to "
          <> T.pack (show (length args))
          <> " fields"
      )
    forM_ (zip args fts) $ \(a, want) -> do
      ta <- monoOf a
      require
        (ta == want)
        ( "field of "
            <> conText c
            <> " has type "
            <> renderType ta
            <> ", not "
            <> renderType want
        )
    mono ty
  TCase sc ty alts -> do
    tsc <- monoOf sc
    table <-
      maybe
        (Left ("case on " <> renderType tsc <> ", which is not a data type"))
        Right
        (dataConstructors look.typeDefOf tsc)
    require
      ([c | TAlt c _ _ <- alts] == map fst table)
      ( "case alternatives are not exactly "
          <> T.intercalate ", " (map (conText . fst) table)
      )
    forM_ alts $ \(TAlt c bs body) -> do
      let fts = maybe [] id (lookup c table)
      require
        (map snd (vecToList bs) == fts)
        ("fields of " <> conText c <> " bound at the wrong types")
      tb <- monoOfIn (vecAppend (vecMap (\(_, t) -> Forall [] t) bs) ctx) body
      require
        (tb == ty)
        ( "alternative "
            <> conText c
            <> " has type "
            <> renderType tb
            <> ", not "
            <> renderType ty
        )
    mono ty
  TPow b n -> do
    tb <- monoOf b
    case tb of
      TTensor SNil d -> mono (TTensor SNil (dimPow (fromIntegral n) d))
      _ -> Left "power of a non-number"
  TNoise _ _ k -> mono (vecT (LLit (fromIntegral k)))
  TUncertain _ _ x e -> do
    tx <- monoOf x
    te <- monoOf e
    case (tx, te) of
      (TTensor _ d, TTensor SNil d') | d == d' -> mono tx
      (TTensor _ _, _) | tx == te -> mono tx
      (TTensor (SCons n SNil) d, TTensor (SCons n' (SCons n'' SNil)) d2)
        | n == n', n == n'', d2 == dimPow 2 d -> mono tx
      _ ->
        Left
          "± needs a tensor and an uncertainty of its dimension: scalar, of its shape, or its covariance matrix"
  TPack ts -> do
    tys <- mapM monoOf ts
    case tys of
      [] -> Left "an empty pack has no element type to lint against"
      TTensor sh d : rest -> do
        require
          (all (== TTensor sh d) rest)
          "pack of tensors with different shapes or dimensions"
        mono (TTensor (SCons (LLit (length ts)) sh) d)
      t : _ -> Left ("pack of non-tensors of type " <> renderType t)
  TProj t i -> do
    tt <- monoOf t
    case tt of
      TTensor (SCons (LLit k) rest) d | i < k -> mono (TTensor rest d)
      TTensor (SCons (LVar _ k) rest) d | i < k -> mono (TTensor rest d)
      TPoint (SCons (LLit k) rest) d | i < k -> mono (TPoint rest d)
      TPoint (SCons (LVar _ k) rest) d | i < k -> mono (TPoint rest d)
      _ -> Left ("projection ." <> T.pack (show i) <> " from " <> renderType tt)
  TTyLam v k body -> do
    Forall vs t <- lint look ctx body
    pure (Forall ((v, k) : vs) t)
  TTyApp body arg -> do
    Forall vs t <- lint look ctx body
    case vs of
      (v, k) : rest -> do
        require (kindOf arg == k) "type application at the wrong kind"
        pure (Forall rest (substOnce (Map.singleton v arg) t))
      [] -> Left "type application to a term with no type abstraction"
  TCycle{} -> Left "a cycle inside an expression"
 where
  monoOf t = lint look ctx t >>= asMono "subterm"
  monoOfIn :: forall j. Vec j Scheme -> TTerm j -> Either Text Type
  monoOfIn ctx' t = lint look ctx' t >>= asMono "subterm"
  mono = Right . Forall []
  isFun = \case
    TFun _ _ -> True
    _ -> False
  kindOf = \case
    AType _ -> KType
    ALen _ -> KLen
    AShape _ -> KShape
    ADim _ -> KDim

{- | The primitives whose types are relations rather than schemes (design
§4.2). Inference solved or defaulted their constraints; lint re-checks the
relation on the elaborated type.
-}
lintConstrained :: TypeLookup -> Text -> Type -> Either Text ()
lintConstrained look name ty = case (name, ty) of
  ("outer", TFun (TTensor s1 d1) (TFun (TTensor s2 d2) (TTensor s3 d3))) -> do
    ls <-
      maybe (Left "outer: the left operand's rank is not known") Right (closedLens s1)
    require
      (s3 == appendShape ls s2)
      ( "outer: result shape "
          <> renderType (TTensor s3 d3)
          <> " is not the concatenation of its operands"
      )
    require
      (d3 == dimMul d1 d2)
      "outer: result dimension is not the product of its operands'"
  ("dot", TFun (TTensor sl d1) (TFun (TTensor sr d2) (TTensor s3 d3))) -> do
    ls <-
      maybe (Left "dot: the left operand's rank is not known") Right (closedLens sl)
    (s1, n) <- maybe (Left "dot: the left operand is a number") Right (unsnoc ls)
    s2 <- case sr of
      SCons n' rest | n' == n -> Right rest
      _ -> Left "dot: the right operand's first length is not the left operand's last"
    require
      (s3 == appendShape s1 s2)
      "dot: result shape is not the contraction of its operands"
    require
      (d3 == dimMul d1 d2)
      "dot: result dimension is not the product of its operands'"
  (eqName, TFun t (TFun t' TBool))
    | eqName `elem` ["eq", "ne"] -> do
        require (t == t') (eqName <> ": operands differ in type")
        equatable look.typeDefOf t
    | eqName `elem` ["lt", "le", "gt", "ge"] -> do
        require (t == t') (eqName <> ": operands differ in type")
        case t of
          TTensor SNil _ -> Right ()
          TPoint SNil _ -> Right ()
          _ -> Left ("no ordering on " <> renderType t)
  _ ->
    Left
      ( "primitive "
          <> name
          <> " used at "
          <> renderType ty
          <> ", which is not a type it has"
      )
 where
  unsnoc = \case
    [] -> Nothing
    xs -> Just (init xs, last xs)

-- | The lengths of a shape that ends in @[]@.
closedLens :: Shape -> Maybe [Len]
closedLens = \case
  SNil -> Just []
  SCons l rest -> (l :) <$> closedLens rest
  SVar _ -> Nothing

appendShape :: [Len] -> Shape -> Shape
appendShape ls tl = foldr SCons tl ls

asMono :: Text -> Scheme -> Either Text Type
asMono what (Forall vs t) = require (null vs) (what <> " is unexpectedly polymorphic") >> Right t

require :: Bool -> Text -> Either Text ()
require b msg = if b then Right () else Left msg

nth :: Int -> [a] -> Maybe a
nth i xs
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      x : _ -> Just x
      [] -> Nothing

lookupCtx :: Fin n -> Vec n a -> a
lookupCtx i ctx = case (i, ctx) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupCtx j xs

{- | Whether a type is an instance of a scheme: one-way matching of the
scheme's quantified variables, each at its kind. Arguments come before
results in a scheme, so by the time a composite dimension such as
@d1 d2@ is met, its variables are bound and it is checked by equality;
the one composite that binds is a single variable to a power (@sqrt@),
solved by taking the root.
-}
isInstanceOf :: Type -> Scheme -> Bool
isInstanceOf ty (Forall vs0 pat0) = case matchType pat ty Map.empty of
  Just _ -> True
  Nothing -> False
 where
  -- The scheme's variable ids are small fixed numbers that can coincide
  -- with the inferred type's ids; rename them to negative ids, which no
  -- inferred type contains, so pattern and actual variables never mix.
  renamed = Map.fromList [(v, fresh v k) | (v, k) <- vs0]
  fresh v = \case
    KType -> AType (TVar (negate (v + 1)))
    KLen -> ALen (LVar (negate (v + 1)) 0)
    KShape -> AShape (SVar (negate (v + 1)))
    KDim -> ADim (dimVar (negate (v + 1)))
  vs = [(negate (v + 1), k) | (v, k) <- vs0]
  pat = applyType renamed pat0
  quantified v = v `elem` map fst vs
  matchType p t m = case (p, t) of
    (TVar v, _) | quantified v -> bindArg v (AType t) m
    (TFun a b, TFun c d) -> matchType a c m >>= matchType b d
    (TTensor a da, TTensor b db) -> matchShape a b m >>= matchDim da db
    (TPoint a da, TPoint b db) -> matchShape a b m >>= matchDim da db
    (TScale a da, TScale b db) -> matchShape a b m >>= matchDim da db
    _ -> if p == t then Just m else Nothing
  matchShape p sh m = case (p, sh) of
    (SVar v, _) | quantified v -> bindArg v (AShape sh) m
    (SCons l rest, SCons l' rest') -> matchLen l l' m >>= matchShape rest rest'
    _ -> if p == sh then Just m else Nothing
  matchLen p l m = case p of
    LVar v off | quantified v -> case l of
      LLit j | j >= off -> bindArg v (ALen (LLit (j - off))) m
      LVar u j | j >= off -> bindArg v (ALen (LVar u (j - off))) m
      _ -> Nothing
    _ -> if p == l then Just m else Nothing
  -- Bound pattern variables are replaced once (their replacements come
  -- from another namespace and must not be chased); the remaining
  -- pattern variables are the scheme's unbound ones.
  matchDim p actual m =
    let unbound = [(v, k) | (DVar v, k) <- dimAtoms p, quantified v, not (Map.member v m)]
        boundPart =
          dimFromAtoms
            [ (a, k)
            | (a, k) <- dimAtoms p
            , case a of DVar v -> not (quantified v) || Map.member v m; _ -> True
            ]
        known = case substOnce m (TTensor SNil boundPart) of
          TTensor _ d -> d
          _ -> boundPart
     in case unbound of
          [] -> if known == actual then Just m else Nothing
          [(v, k)] ->
            -- p = known · v^k, so v^k = actual / known.
            dimRoot k (dimDiv actual known) >>= \root -> bindArg v (ADim root) m
          _ -> Nothing
  bindArg v arg m = case Map.lookup v m of
    Nothing -> Just (Map.insert v arg m)
    Just existing -> if existing == arg then Just m else Nothing

-- Rendering --------------------------------------------------------------------------

{- | Print Typed Core with every annotation visible: @Λt0. \(x : t0) -> x@,
@f @Num 1@, @let g : Vec (n1 + 1) -> Num = … in …@.
-}
renderTTerm ::
  (Hash -> Maybe Int -> Text -> Text) -> Vec n Text -> TTerm n -> Text
renderTTerm namer = go 0
 where
  go :: Int -> Vec m Text -> TTerm m -> Text
  go prec ctx = \case
    TVr i -> lookupCtx i ctx
    TRef h idx (Hint written) -> namer h idx written
    TPrimApp p _ [] -> p
    TPrimApp p _ args -> paren (prec > 10) (T.unwords (p : map (go 11 ctx) args))
    TLit (LTensor ([], [r])) -> showD r
    TLit (LTensor (dims, rs)) -> nested dims rs
    TLam (Hint h) ty b ->
      paren
        (prec > 0)
        ("\\(" <> h <> " : " <> renderTypeIds ty <> ") -> " <> go 0 (VCons h ctx) b)
    TApp f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
    TLet (Hint h) sc e b ->
      paren
        (prec > 0)
        ( "let "
            <> h
            <> " : "
            <> renderSchemeIds sc
            <> " = "
            <> go 0 ctx e
            <> " in "
            <> go 0 (VCons h ctx) b
        )
    TCon c _ args -> case (c, args) of
      (Builtin "True", []) -> "true"
      (Builtin "False", []) -> "false"
      (Builtin "Tuple", _) -> "(" <> T.intercalate ", " (map (go 0 ctx) args) <> ")"
      (Builtin "Nil", []) -> "{}"
      (Builtin "Cons", [x, xs]) -> paren (prec > 4) (go 5 ctx x <> " : " <> go 4 ctx xs)
      _ ->
        paren
          (prec > 10 && not (null args))
          (T.unwords (conText c : map (go 11 ctx) args))
    TCase sc _ [TAlt (Builtin "False") VNil e, TAlt (Builtin "True") VNil t] ->
      paren
        (prec > 0)
        ("if " <> go 0 ctx sc <> " then " <> go 0 ctx t <> " else " <> go 0 ctx e)
    TCase sc _ alts ->
      paren
        (prec > 0)
        ("case " <> go 0 ctx sc <> " of " <> T.intercalate "; " [alt a | a <- alts])
     where
      alt (TAlt c bs b) =
        let names = vecMap (\(Hint h, _) -> h) bs
            ctx' = vecAppend names ctx
         in patternText c (vecToList names) <> " -> " <> go 0 ctx' b
    TPow b n -> paren (prec > 9) (go 10 ctx b <> "^" <> T.pack (show n))
    TNoise Bound l k -> "noise " <> T.pack (show k) <> renderLabel l
    TNoise Stat l k -> "gauss " <> T.pack (show k) <> renderLabel l
    TUncertain k l x e ->
      paren
        (prec > 5)
        ( go 6 ctx x
            <> (if k == Bound then " ± " else " ±σ ")
            <> go 6 ctx e
            <> renderLabel l
        )
    TPack ts -> "[" <> T.intercalate ", " (map (go 0 ctx) ts) <> "]"
    TProj b i -> go 11 ctx b <> "." <> T.pack (show i)
    TTyLam v k b -> paren (prec > 0) ("Λ" <> varName v k <> ". " <> go 0 ctx b)
    TTyApp b arg -> paren (prec > 10) (go 10 ctx b <> " @" <> renderArg arg)
    TCycle vars members bodies ->
      let ctx' = vecAppend (vecMap (\(Hint h, _) -> h) members) ctx
          binders = T.concat ["Λ" <> varName v k <> ". " | (v, k) <- vars]
       in binders
            <> T.intercalate
              "; "
              [ h <> " : " <> renderTypeIds ty <> " = " <> go 0 ctx' b
              | ((Hint h, ty), b) <- zip (vecToList members) (vecToList bodies)
              ]
  paren b s = if b then "(" <> s <> ")" else s
  varName v = \case
    KType -> "t" <> T.pack (show v)
    KLen -> "n" <> T.pack (show v)
    KShape -> "s" <> T.pack (show v)
    KDim -> "d" <> T.pack (show v)
  showD r = T.pack (show (fromRational r :: Double))
  nested dims rs = case dims of
    [] -> maybe "[]" showD (nth 0 rs)
    [_] -> "[" <> T.intercalate ", " (map showD rs) <> "]"
    d : rest ->
      let stride = product rest
       in "["
            <> T.intercalate
              ", "
              [nested rest (take stride (drop (i * stride) rs)) | i <- [0 .. d - 1]]
            <> "]"

-- | How a constructor pattern is written (design §2.3).
patternText :: ConRef -> [Text] -> Text
patternText c names = case (c, names) of
  (Builtin "True", []) -> "true"
  (Builtin "False", []) -> "false"
  (Builtin "Tuple", _) -> "(" <> T.intercalate ", " names <> ")"
  (Builtin "Nil", []) -> "{}"
  (Builtin "Cons", [x, xs]) -> x <> " : " <> xs
  _ -> T.unwords (conText c : names)

{- | The types `==` is defined at (design §4.2): tensors, booleans, points,
and structured data whose components are: tuples, lists and declared types.
-}
equatable :: (Hash -> Maybe TypeDef) -> Type -> Either Text ()
equatable defs t = case t of
  TTensor _ _ -> Right ()
  TBool -> Right ()
  TPoint _ _ -> Right ()
  TTuple ts -> mapM_ (equatable defs) ts
  TList e -> equatable defs e
  TData h as | Just ts <- equalityArgs defs h as -> mapM_ (equatable defs) ts
  _ -> Left ("no equality on " <> renderType t)
