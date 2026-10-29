-- | Typed Core (design §5.3, core.md): Core after inference and elaboration,
-- explicitly typed in the manner of System F and GHC's Core. Every binder
-- carries its type, polymorphism is explicit through one kinded abstraction
-- form and one kinded application form, and a primitive carries the type it
-- is used at. The interpreter runs this; a compiler would start from it.
--
-- 'lint' is the counterpart of GHC's Core Lint: a plain type checker (no
-- inference) that validates an elaborated term. Elaboration bugs surface
-- there, not in the evaluator.
module Eval.TCore
  ( TTerm (..)
  , primScheme
  , closedLens
  , appendShape
  , lintClosed
  , renderTTerm
  ) where

import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Type

-- | Typed Core terms in a scope of @n@ term variables. Type-level variables
-- are identified by number and bound by 'TTyLam' with their kind.
data TTerm (n :: Nat) where
  TVr :: Fin n -> TTerm n
  TRef :: Hash -> Maybe Int -> TTerm n
  -- | A saturated primitive at a specific type (an instance of 'primScheme').
  TPrimApp :: Text -> Type -> [TTerm n] -> TTerm n
  TLit :: Lit -> TTerm n
  TLam :: Hint -> Type -> TTerm (S n) -> TTerm n
  TApp :: TTerm n -> TTerm n -> TTerm n
  -- | The bound term has the scheme; its abstractions are explicit in it.
  TLet :: Hint -> Scheme -> TTerm n -> TTerm (S n) -> TTerm n
  TIf :: TTerm n -> TTerm n -> TTerm n -> TTerm n
  TPow :: TTerm n -> Integer -> TTerm n
  TNoise :: NudgeKind -> Integer -> TTerm n
  TUncertain :: NudgeKind -> TTerm n -> TTerm n -> TTerm n
  TPack :: [TTerm n] -> TTerm n
  TProj :: TTerm n -> Int -> TTerm n
  -- | Abstraction over a type-level variable of the given kind.
  TTyLam :: VarId -> Kind -> TTerm n -> TTerm n
  -- | Application to a type-level argument.
  TTyApp :: TTerm n -> Arg -> TTerm n
  -- | Mutually recursive members, monomorphic inside the cycle at the given
  -- types, generalised together over the listed variables outside it.
  TCycle :: [(VarId, Kind)] -> Vec k (Hint, Type) -> Vec k (TTerm (Plus k n)) -> TTerm n

deriving stock instance Show (TTerm n)

-- Primitive signatures ------------------------------------------------------------

-- | The scheme of each primitive. Quantified variables use small fixed ids;
-- inference instantiates them, 'lint' matches against them. See core.md
-- "Operators across ranks" for which are shape-polymorphic.
primScheme :: Text -> Maybe Scheme
primScheme = \case
  "add" -> elementwise2
  "sub" -> elementwise2
  "emul" -> elementwise2
  "ediv" -> elementwise2
  "div" -> Just (Forall [(0, KShape)] (TFun s (TFun numT s)))
  -- outer, dot, eq and ne have constraint types; see 'lintConstrained'.
  "atan2" -> num2
  "to" -> num2
  "neg" -> elementwise1
  "abs" -> elementwise1
  "floor" -> num1
  "ceil" -> num1
  "round" -> num1
  "sqrt" -> num1
  "sin" -> num1
  "cos" -> num1
  "tan" -> num1
  "asin" -> num1
  "acos" -> num1
  "atan" -> num1
  "sinh" -> num1
  "cosh" -> num1
  "tanh" -> num1
  "exp" -> num1
  "log" -> num1
  "lt" -> cmp
  "le" -> cmp
  "gt" -> cmp
  "ge" -> cmp
  "and" -> mono (TFun TBool (TFun TBool TBool))
  "or" -> mono (TFun TBool (TFun TBool TBool))
  "not" -> mono (TFun TBool TBool)
  "pi" -> mono numT
  "cross" -> mono (TFun (vecT (LLit 3)) (TFun (vecT (LLit 3)) (vecT (LLit 3))))
  "norm" -> Just (Forall [(0, KLen)] (TFun (vecT n) numT))
  "transpose" -> Just (Forall [(0, KLen), (1, KLen)] (TFun (matT n m) (matT m n)))
  "inverse" -> Just (Forall [(0, KLen)] (TFun (matT n n) (matT n n)))
  "det" -> Just (Forall [(0, KLen)] (TFun (matT n n) numT))
  "vmap" -> Just (Forall [(0, KShape)] (TFun (TFun numT numT) (TFun s s)))
  _ -> Nothing
  where
    n = LVar 0 0
    m = LVar 1 0
    s = TTensor (SVar 0)
    matT r c = TTensor (SCons r (SCons c SNil))
    mono = Just . Forall []
    num1 = mono (TFun numT numT)
    num2 = mono (TFun numT (TFun numT numT))
    cmp = mono (TFun numT (TFun numT TBool))
    elementwise1 = Just (Forall [(0, KShape)] (TFun s s))
    elementwise2 = Just (Forall [(0, KShape)] (TFun s (TFun s s)))

-- Lint -------------------------------------------------------------------------

-- | Check a closed term and return its scheme(s): one, or one per cycle
-- member. The result is 'Left' only when elaboration produced an ill-typed
-- term, which is an internal error.
lintClosed :: (Hash -> Maybe [Scheme]) -> TTerm Z -> Either Text [Scheme]
lintClosed look = \case
  TCycle vars members bodies -> do
    let ctx = vecAppend (vecMap (Forall [] . snd) members) VNil
    sequence_
      [ do
          t <- lint look ctx body >>= asMono ("cycle member `" <> h <> "`")
          require (t == expected) ("cycle member `" <> h <> "` has type " <> renderType t <> " but is annotated " <> renderType expected)
      | ((Hint h, expected), body) <- zip (vecToList members) (vecToList bodies)
      ]
    pure [Forall vars t | (_, t) <- vecToList members]
  t -> (: []) <$> lint look VNil t

lint :: (Hash -> Maybe [Scheme]) -> Vec n Scheme -> TTerm n -> Either Text Scheme
lint look ctx = \case
  TVr i -> Right (lookupCtx i ctx)
  TRef h idx -> case look h of
    Nothing -> Left "reference to a definition with no stored type"
    Just schemes -> maybe (Left "reference to a missing cycle member") Right (nth (fromMaybe 0 idx) schemes)
  TPrimApp name ty args -> do
    case primScheme name of
      Just general ->
        require (ty `isInstanceOf` general) ("primitive " <> name <> " used at " <> renderType ty <> ", not an instance of " <> renderScheme general)
      Nothing -> lintConstrained name ty
    let go t = \case
          [] -> Right t
          arg : rest -> case t of
            TFun p r -> do
              ta <- monoOf arg
              require (ta == p) ("argument of " <> name <> " has type " <> renderType ta <> ", expected " <> renderType p)
              go r rest
            _ -> Left ("primitive " <> name <> " applied to too many arguments")
    result <- go ty args
    require (not (isFun result)) ("primitive " <> name <> " is not saturated")
    mono result
  TLit (LTensor dims rs) -> do
    require (length rs == product dims) "tensor literal has the wrong number of values for its shape"
    mono (TTensor (shapeOfDims dims))
  TLit (LBool _) -> mono TBool
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
    require (actual == sc) ("let binder annotated " <> renderScheme sc <> " but bound to " <> renderScheme actual)
    lint look (VCons sc ctx) body
  TIf c t e -> do
    tc <- monoOf c
    require (tc == TBool) "if condition is not Bool"
    tt <- monoOf t
    te <- monoOf e
    require (tt == te) ("if branches differ: " <> renderType tt <> " and " <> renderType te)
    mono tt
  TPow b _ -> do
    tb <- monoOf b
    require (tb == numT) "power of a non-number"
    mono numT
  TNoise _ k -> mono (vecT (LLit (fromIntegral k)))
  TUncertain _ x e -> do
    tx <- monoOf x
    te <- monoOf e
    require (tx == numT && te == numT) "± on non-numbers"
    mono numT
  TPack ts -> do
    tys <- mapM monoOf ts
    case tys of
      [] -> Left "an empty pack has no element type to lint against"
      TTensor sh : rest -> do
        require (all (== TTensor sh) rest) "pack of tensors with different shapes"
        mono (TTensor (SCons (LLit (length ts)) sh))
      t : _ -> Left ("pack of non-tensors of type " <> renderType t)
  TProj t i -> do
    tt <- monoOf t
    case tt of
      TTensor (SCons (LLit k) rest) | i < k -> mono (TTensor rest)
      TTensor (SCons (LVar _ k) rest) | i < k -> mono (TTensor rest)
      _ -> Left ("projection ." <> T.pack (show i) <> " from " <> renderType tt)
  TTyLam v k body -> do
    Forall vs t <- lint look ctx body
    pure (Forall ((v, k) : vs) t)
  TTyApp body arg -> do
    Forall vs t <- lint look ctx body
    case vs of
      (v, k) : rest -> do
        require (kindOf arg == k) "type application at the wrong kind"
        pure (Forall rest (applyType (Map.singleton v arg) t))
      [] -> Left "type application to a term with no type abstraction"
  TCycle {} -> Left "a cycle inside an expression"
  where
    monoOf t = lint look ctx t >>= asMono "subterm"
    mono = Right . Forall []
    isFun = \case
      TFun _ _ -> True
      _ -> False
    kindOf = \case
      AType _ -> KType
      ALen _ -> KLen
      AShape _ -> KShape

-- | The primitives whose types are relations rather than schemes (design
-- §4.2). Inference solved or defaulted their constraints; lint re-checks the
-- relation on the elaborated type.
lintConstrained :: Text -> Type -> Either Text ()
lintConstrained name ty = case (name, ty) of
  ("outer", TFun (TTensor s1) (TFun (TTensor s2) (TTensor s3))) -> do
    ls <- maybe (Left "outer: the left operand's rank is not known") Right (closedLens s1)
    require (s3 == appendShape ls s2) ("outer: result shape " <> renderType (TTensor s3) <> " is not the concatenation of its operands")
  ("dot", TFun (TTensor sl) (TFun (TTensor sr) (TTensor s3))) -> do
    ls <- maybe (Left "dot: the left operand's rank is not known") Right (closedLens sl)
    (s1, n) <- maybe (Left "dot: the left operand is a number") Right (unsnoc ls)
    s2 <- case sr of
      SCons n' rest | n' == n -> Right rest
      _ -> Left "dot: the right operand's first length is not the left operand's last"
    require (s3 == appendShape s1 s2) "dot: result shape is not the contraction of its operands"
  (eqName, TFun t (TFun t' TBool))
    | eqName == "eq" || eqName == "ne" -> do
        require (t == t') (eqName <> ": operands differ in type")
        case t of
          TTensor _ -> Right ()
          TBool -> Right ()
          _ -> Left ("no equality on " <> renderType t)
  _ -> Left ("primitive " <> name <> " used at " <> renderType ty <> ", which is not a type it has")
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

-- | Whether a type is an instance of a scheme: one-way matching of the
-- scheme's quantified variables, each at its kind.
isInstanceOf :: Type -> Scheme -> Bool
isInstanceOf ty (Forall vs pat) = case matchType pat ty Map.empty of
  Just _ -> True
  Nothing -> False
  where
    quantified v = v `elem` map fst vs
    matchType p t m = case (p, t) of
      (TVar v, _) | quantified v -> bindArg v (AType t) m
      (TFun a b, TFun c d) -> matchType a c m >>= matchType b d
      (TTensor a, TTensor b) -> matchShape a b m
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
    bindArg v arg m = case Map.lookup v m of
      Nothing -> Just (Map.insert v arg m)
      Just existing -> if existing == arg then Just m else Nothing

-- Rendering --------------------------------------------------------------------------

-- | Print Typed Core with every annotation visible: @Λt0. \(x : t0) -> x@,
-- @f @Num 1@, @let g : Vec (n1 + 1) -> Num = … in …@.
renderTTerm :: (Hash -> Maybe Int -> Text) -> Vec n Text -> TTerm n -> Text
renderTTerm namer = go 0
  where
    go :: Int -> Vec m Text -> TTerm m -> Text
    go prec ctx = \case
      TVr i -> lookupCtx i ctx
      TRef h idx -> namer h idx
      TPrimApp p _ [] -> p
      TPrimApp p _ args -> paren (prec > 10) (T.unwords (p : map (go 11 ctx) args))
      TLit (LTensor [] [r]) -> showD r
      TLit (LTensor dims rs) -> nested dims rs
      TLit (LBool b) -> if b then "true" else "false"
      TLam (Hint h) ty b -> paren (prec > 0) ("\\(" <> h <> " : " <> renderTypeIds ty <> ") -> " <> go 0 (VCons h ctx) b)
      TApp f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
      TLet (Hint h) sc e b ->
        paren (prec > 0) ("let " <> h <> " : " <> renderSchemeIds sc <> " = " <> go 0 ctx e <> " in " <> go 0 (VCons h ctx) b)
      TIf c t e -> paren (prec > 0) ("if " <> go 0 ctx c <> " then " <> go 0 ctx t <> " else " <> go 0 ctx e)
      TPow b n -> paren (prec > 9) (go 10 ctx b <> "^" <> T.pack (show n))
      TNoise Bound k -> "noise " <> T.pack (show k)
      TNoise Stat k -> "gauss " <> T.pack (show k)
      TUncertain k x e -> paren (prec > 5) (go 6 ctx x <> (if k == Bound then " ± " else " ±σ ") <> go 6 ctx e)
      TPack ts -> "[" <> T.intercalate ", " (map (go 0 ctx) ts) <> "]"
      TProj b i -> go 11 ctx b <> "." <> T.pack (show i)
      TTyLam v k b -> paren (prec > 0) ("Λ" <> varName v k <> ". " <> go 0 ctx b)
      TTyApp b arg -> paren (prec > 10) (go 10 ctx b <> " @" <> renderArg arg)
      TCycle vars members bodies ->
        let ctx' = vecAppend (vecMap (\(Hint h, _) -> h) members) ctx
            binders = T.concat ["Λ" <> varName v k <> ". " | (v, k) <- vars]
         in binders
              <> T.intercalate "; " [h <> " : " <> renderTypeIds ty <> " = " <> go 0 ctx' b | ((Hint h, ty), b) <- zip (vecToList members) (vecToList bodies)]
    paren b s = if b then "(" <> s <> ")" else s
    varName v = \case
      KType -> "t" <> T.pack (show v)
      KLen -> "n" <> T.pack (show v)
      KShape -> "s" <> T.pack (show v)
    showD r = T.pack (show (fromRational r :: Double))
    nested dims rs = case dims of
      [] -> maybe "[]" showD (nth 0 rs)
      [_] -> "[" <> T.intercalate ", " (map showD rs) <> "]"
      d : rest ->
        let stride = product rest
         in "[" <> T.intercalate ", " [nested rest (take stride (drop (i * stride) rs)) | i <- [0 .. d - 1]] <> "]"
