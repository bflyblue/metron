{-# LANGUAGE PatternSynonyms #-}

{- | Typed Core (design §5.3, core.md): Core after inference and elaboration,
explicitly typed in the manner of System F and GHC's Core. Every binder
carries its type, polymorphism is explicit through one kinded abstraction
form and one kinded application form, and a primitive carries the type it
is used at. The interpreter runs this; a compiler would start from it.

'lint' is the counterpart of GHC's Core Lint: a plain type checker (no
inference) that validates an elaborated term. Elaboration bugs surface
there, not in the evaluator.
-}
module Metron.TCore (
  TTerm (
    TLam,
    TVr,
    TRef,
    TPrimApp,
    TLit,
    TLamWith,
    TApp,
    TLet,
    TCon,
    TCase,
    TPow,
    TSample,
    TPack,
    TProj,
    TTyLam,
    TTyApp,
    TCycle
  ),
  lintClosed,
  renderTTerm,
  patternText,
  TAlt (..),
) where

import Control.Monad (forM_)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet (
  empty,
  fromDistinctAscList,
  singleton,
  toAscList,
 )
import Data.Map.Strict qualified as Map (
  findWithDefault,
  fromList,
  insert,
 )
import Data.Maybe (fromMaybe)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T (
  concat,
  intercalate,
  pack,
  unwords,
 )
import Metron.Builtin (
  distributionHash,
  pattern BoolT,
  pattern ConsC,
  pattern FalseC,
  pattern NilC,
  pattern TrueC,
  pattern TupleC,
 )
import Metron.Core (
  ConRef,
  Fin (..),
  Hash,
  Hint (..),
  Label,
  Lit (..),
  Nat (..),
  Plus,
  Vec (..),
  finToInt,
  renderLabel,
  vecAppend,
  vecLength,
  vecMap,
  vecToList,
 )
import Metron.Dimension (dimMul, dimOne, dimPow)
import Metron.Primitive.Types (
  StaticArg (ConArg, ListArg, LitArg),
  primScheme,
  primSchemeFor,
 )
import Metron.Type (
  Arg (..),
  Axis,
  Frame (space),
  Kind (..),
  Len (LLit, LRank, LVar),
  Scheme (..),
  Shape (SCons, SNil),
  Space (dim, shape),
  Type (TData, TFun, TOver, TPoint, TTensor),
  TypeDef,
  TypeLookup (schemesOf, typeDefOf),
  VarId,
  appendShape,
  closedLens,
  conText,
  dataConstructors,
  equalityArgs,
  freeVars,
  numD,
  renderArg,
  renderScheme,
  renderSchemeIds,
  renderType,
  renderTypeIds,
  selfType,
  substOnce,
  varArg,
  vecT,
 )
import Metron.Type.Match (isInstanceOf)

{- | Typed Core terms in a scope of @n@ term variables. Type-level variables
are identified by number and bound by 'TTyLam' with their kind.
-}
data TTerm (n :: Nat) where
  TVr :: Fin n -> TTerm n
  TRef :: Hash -> Maybe Int -> Hint -> TTerm n
  -- | A saturated primitive at a specific type (an instance of 'primScheme').
  TPrimApp :: Text -> Type -> [TTerm n] -> TTerm n
  {- | A constant at the axes of its positions: a literal is polymorphic in
  its axes (design §3.9, decision 5), so its frame is the one its use gave
  it.
  -}
  TLit :: Lit -> [Axis] -> TTerm n
  {- | A function of one argument. The last field is the set of variables
  free in the body, by de Bruijn index: computed once, when first asked
  for, and shared by every evaluation of the term, so that a closure keeps
  only the variables it uses (design §8). Built and matched as 'TLam'.
  -}
  TLamWith :: Hint -> Type -> TTerm (S n) -> IntSet -> TTerm n
  TApp :: TTerm n -> TTerm n -> TTerm n
  -- | The bound term has the scheme; its abstractions are explicit in it.
  TLet :: Hint -> Scheme -> TTerm n -> TTerm (S n) -> TTerm n
  -- | A constructor at its result type (@Nil@ alone fixes no element type).
  TCon :: ConRef -> Type -> [TTerm n] -> TTerm n
  -- | A case at its result type.
  TCase :: TTerm n -> Type -> [TAlt n] -> TTerm n
  TPow :: TTerm n -> Integer -> TTerm n
  TSample :: Label -> TTerm n -> TTerm n
  {- | A stack of tensors of the given element type, along the axes its new
  leading position has. The element type is kept even with no elements,
  where nothing else says what the stack holds (design §3.3).
  -}
  TPack :: Axis -> Type -> [TTerm n] -> TTerm n
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

-- | A function of one argument, its free variables found when first needed.
pattern TLam :: Hint -> Type -> TTerm (S n) -> TTerm n
pattern TLam h ty body <- TLamWith h ty body _
  where
    TLam h ty body = TLamWith h ty body (freeIndices body)

{-# COMPLETE
  TVr
  , TRef
  , TPrimApp
  , TLit
  , TLam
  , TApp
  , TLet
  , TCon
  , TCase
  , TPow
  , TSample
  , TPack
  , TProj
  , TTyLam
  , TTyApp
  , TCycle
  #-}

-- | The variables free in a term, by their de Bruijn index in its scope.
freeIndices :: TTerm n -> IntSet
freeIndices = go 0
 where
  go :: Int -> TTerm m -> IntSet
  go d = \case
    TVr i ->
      let j = finToInt i in if j >= d then IntSet.singleton (j - d) else IntSet.empty
    TRef{} -> IntSet.empty
    TPrimApp _ _ args -> foldMap (go d) args
    TLit{} -> IntSet.empty
    -- A nested function's set is shifted out of its binder, and shared.
    TLamWith _ _ _ inner -> IntSet.fromDistinctAscList [j - d - 1 | j <- IntSet.toAscList inner, j > d]
    TApp f a -> go d f <> go d a
    TLet _ _ e b -> go d e <> go (d + 1) b
    TCon _ _ args -> foldMap (go d) args
    TCase s _ alts -> go d s <> foldMap (\(TAlt _ bs b) -> go (d + vecLength bs) b) alts
    TPow t _ -> go d t
    TSample _ a -> go d a
    TPack _ _ ts -> foldMap (go d) ts
    TProj t _ -> go d t
    TTyLam _ _ b -> go d b
    TTyApp b _ -> go d b
    TCycle _ bs bodies -> foldMap (go (d + vecLength bs)) (vecToList bodies)

-- Primitive signatures ------------------------------------------------------------

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
    let static = \case
          TLit l _ -> Just (LitArg l)
          TCon NilC _ [] -> Just (ListArg [])
          TCon ConsC _ [x, rest] -> case static rest of
            Just (ListArg xs) -> Just (ListArg (static x : xs))
            _ -> Nothing
          TCon c _ [] -> Just (ConArg c)
          _ -> Nothing
        literals = map static args
        instanceOf general =
          require
            (ty `isInstanceOf` general)
            ( "primitive "
                <> name
                <> " used at "
                <> renderType ty
                <> ", not an instance of "
                <> renderScheme general
            )
    case (primScheme name, primSchemeFor look.typeDefOf name literals) of
      (Just general, _) -> instanceOf general
      -- contract, permute and slice: the scheme the literal positions determine.
      (_, Just general) -> general >>= instanceOf
      _ -> lintConstrained look name ty
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
  TLit (LTensor (dims, rs)) axes -> do
    require
      (length rs == product dims)
      "tensor literal has the wrong number of values for its shape"
    require
      (length axes == length dims)
      "tensor literal has the wrong number of axes for its shape"
    mono (TTensor (foldr (\(k, a) -> SCons (LLit k) a) SNil (zip dims axes)) dimOne)
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
      let fts = fromMaybe [] (lookup c table)
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
      -- A power of a number (design §4.3).
      TTensor SNil d -> mono (numD (dimPow n d))
      _ -> Left "power of a non-number"
  TSample _ x -> do
    tx <- monoOf x
    case tx of
      TData h [ADim d] | h == distributionHash -> mono (numD d)
      _ -> Left "sample needs a scalar distribution"
  TPack ax ty ts -> do
    tys <- mapM monoOf ts
    case ty of
      TTensor sh d -> do
        require
          (all (== ty) tys)
          "pack of tensors with different shapes or dimensions from its element type"
        mono (TTensor (SCons (LLit (length ts)) ax sh) d)
      t -> Left ("pack of non-tensors of type " <> renderType t)
  TProj t i -> do
    tt <- monoOf t
    case tt of
      TTensor (SCons (LLit k) _ rest) d | i < k -> mono (TTensor rest d)
      TTensor (SCons (LVar _ k) _ rest) d | i < k -> mono (TTensor rest d)
      TTensor (SCons (LRank _ k) _ rest) d | i < k -> mono (TTensor rest d)
      -- A coordinate of a point on a frame (design §3.10, F5): an amount.
      TPoint f
        | SCons l _ SNil <- f.space.shape
        , case l of LLit k -> i < k; LVar _ k -> i < k; LRank _ k -> i < k ->
            mono (TTensor SNil f.space.dim)
      _ -> Left ("projection ." <> T.pack (show i) <> " from " <> renderType tt)
  TTyLam v k body -> do
    Forall vs t <- lint look ctx body
    pure (Forall ((v, k) : vs) t)
  TTyApp body arg -> do
    Forall vs t <- lint look ctx body
    case vs of
      (v, k) : rest -> do
        require (kindOf arg == k) "type application at the wrong kind"
        -- Capture-avoiding: the argument's variables come from the run
        -- that elaborated the term and can share ids with the variables
        -- still to be applied, which are renamed apart first. (Axis
        -- variables, numbered from one base in every run, always can.)
        let argVars = map fst (freeVars (TData selfType [arg]))
            clashing = [(w, kw) | (w, kw) <- rest, w `elem` argVars]
            base = maximum (0 : map fst vs ++ map fst (freeVars t) ++ argVars) + 1
            renamed = Map.fromList [(w, i) | ((w, _), i) <- zip clashing [base ..]]
            rename w = Map.findWithDefault w w renamed
            renaming = Map.fromList [(w, varArg kw (rename w)) | (w, kw) <- clashing]
        pure
          ( Forall
              [(rename w, kw) | (w, kw) <- rest]
              (substOnce (Map.insert v arg renaming) t)
          )
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
    AAxis _ -> KAxis
    AFrame _ -> KFrame
    ASpace _ -> KSpace

{- | The primitives whose types are relations rather than schemes (design
§4.2). Inference solved or defaulted their constraints; lint re-checks the
relation on the elaborated type.
-}
lintConstrained :: TypeLookup -> Text -> Type -> Either Text ()
lintConstrained look name ty = case (name, ty) of
  -- Ordinary arithmetic takes amounts; unit syntax is elaborated separately.
  ("outer", TFun (TTensor s1 d1) (TFun (TTensor s2 d2) (TTensor s3 d3))) -> do
    if s2 == SNil
      then require (s3 == s1) "outer: a scalar right operand preserves the left shape"
      else do
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
    -- The contracted positions share their length and their axes.
    s2 <- case sr of
      SCons n' a' rest | (n', a') == n -> Right rest
      _ ->
        Left
          "dot: the right operand's first length and axes are not the left operand's last"
    require
      (s3 == appendShape s1 s2)
      "dot: result shape is not the contraction of its operands"
    require
      (d3 == dimMul d1 d2)
      "dot: result dimension is not the product of its operands'"
  (eqName, TFun t (TFun t' BoolT))
    | eqName `elem` ["eq", "ne"] -> do
        require (t == t') (eqName <> ": operands differ in type")
        equatable look.typeDefOf t
    | eqName `elem` ["lt", "le", "gt", "ge"] -> do
        require (t == t') (eqName <> ": operands differ in type")
        case t of
          TTensor SNil _ -> Right ()
          TPoint f | f.space.shape == SNil -> Right ()
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
    TLit (LTensor ([], [r])) _ -> showD r
    TLit (LTensor (dims, rs)) _ -> nested dims rs
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
      (TrueC, []) -> "true"
      (FalseC, []) -> "false"
      (TupleC _, _) -> "(" <> T.intercalate ", " (map (go 0 ctx) args) <> ")"
      (NilC, []) -> "{}"
      (ConsC, [x, xs]) -> paren (prec > 4) (go 5 ctx x <> " : " <> go 4 ctx xs)
      _ ->
        paren
          (prec > 10 && not (null args))
          (T.unwords (conText c : map (go 11 ctx) args))
    TCase sc _ [TAlt FalseC VNil e, TAlt TrueC VNil t] ->
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
    TSample l x -> paren (prec > 10) ("sample " <> go 11 ctx x <> renderLabel l)
    TPack _ _ ts -> "[" <> T.intercalate ", " (map (go 0 ctx) ts) <> "]"
    TProj b i -> go 11 ctx b <> "." <> T.pack (show i)
    -- Axis variables print in a scheme's forall only (design §3.9): in
    -- Typed Core their abstractions and applications print as nothing.
    TTyLam _ KAxis b -> go prec ctx b
    TTyApp b (AAxis _) -> go prec ctx b
    TTyLam v k b -> paren (prec > 0) ("Λ" <> varName v k <> ". " <> go 0 ctx b)
    TTyApp b arg -> paren (prec > 10) (go 10 ctx b <> " @" <> renderArg arg)
    TCycle vars members bodies ->
      let ctx' = vecAppend (vecMap (\(Hint h, _) -> h) members) ctx
          binders = T.concat ["Λ" <> varName v k <> ". " | (v, k) <- vars, k /= KAxis]
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
    KAxis -> "x" <> T.pack (show v)
    KFrame -> "f" <> T.pack (show v)
    KSpace -> "sp" <> T.pack (show v)
  -- A whole number prints as one, so that a slice's or a contraction's
  -- positions read as positions: `slice 1 0 t`.
  showD r
    | denominator r == 1 = T.pack (show (numerator r))
    | otherwise = T.pack (show (fromRational r :: Double))
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
  (TrueC, []) -> "true"
  (FalseC, []) -> "false"
  (TupleC _, _) -> "(" <> T.intercalate ", " names <> ")"
  (NilC, []) -> "{}"
  (ConsC, [x, xs]) -> x <> " : " <> xs
  _ -> T.unwords (conText c : names)

{- | The types `==` is defined at (design §4.2): tensors, booleans, points,
and structured data whose components are: tuples, lists and declared types.
-}
equatable :: (Hash -> Maybe TypeDef) -> Type -> Either Text ()
equatable defs t = case t of
  TTensor _ _ -> Right ()
  TPoint _ -> Right ()
  TOver _ _ -> Right ()
  TData h as | Just ts <- equalityArgs defs h as -> mapM_ (equatable defs) ts
  _ -> Left ("no equality on " <> renderType t)
