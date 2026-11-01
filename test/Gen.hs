{- | A type-directed generator of surface programs (core.md §9).

Each program is built from a chosen closed type, so every case is
well-typed by construction and the property tests spend their budget on
deep shapes (nested lets, products of tensors, dimensions, higher-order
functions) instead of on discards.

Two things make "well-typed by construction" more than plain Hindley-Milner
here (design §4.2):

* The products and equality have deferred constraints, and at a let or at
  the top level an unsolved one is defaulted: the unseen part of the left
  operand of @*@ or @\@@ takes the least rank it can, so a left operand
  of unseen rank becomes a scalar for @*@ and a vector for @\@@, and one
  with leading lengths, such as @[[x]]@, keeps them with @x@ a scalar;
  both operands of a @*@ or @/@ whose role nothing fixes (design §3.10,
  U9) become scalars, and an unknown @==@ type @Num@. The generator tracks
  whether inference can see the rank of each expression it builds
  ('pinned'), and wraps an operand whose rank it cannot see and whose
  intended type is not the default (@e + 0 [m]@, @e && true@).
* Inference may find a more general type than the one a subterm was built
  for (@\\x -> 1@ built at @Num -> Num@ is @a -> Num@). That is harmless
  in HM, and 'instanceOf' is how the property checks the result: the
  intended type must be an instance of the inferred scheme.
-}
module Gen (
  genType,
  genTyped,
  genProgram,
  instanceOf,
  exprDepth,

  -- * Core terms
  Depth (..),
  SomeTerm (..),
  coreHashes,
  genCoreTerm,
  genSomeTerm,
  scopeNames,
) where

import Control.Monad (foldM)
import Data.Bifunctor (second)
import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import Metron.Builtin
import Metron.Core (
  Alt (..),
  ConRef (..),
  Fin (..),
  Hash (..),
  Hint,
  Label (..),
  Lit (..),
  Nat (..),
  NudgeKind (..),
  Plus,
  SomeVec (..),
  Term (..),
  Vec (..),
  vecFromList,
  vecTraverse,
 )
import Metron.Dimension
import Metron.Syntax qualified as S
import Metron.Type
import Test.QuickCheck

-- Types ---------------------------------------------------------------------------

{- | Tensors are kept to rank three and lengths one to three, so the largest
value has 27 elements and a product never builds anything bigger.
-}
maxRank :: Int
maxRank = 3

tensor :: [Int] -> Dim -> Type
tensor ls = TTensor (shapeOfDims ls)

-- | The literal lengths of a closed shape.
lensOf :: Shape -> Maybe [Int]
lensOf = \case
  SNil -> Just []
  SCons (LLit k) _ rest -> (k :) <$> lensOf rest
  _ -> Nothing

-- | A ground tensor type as lengths and dimension.
asTensor :: Type -> Maybe ([Int], Dim)
asTensor = \case
  TTensor sh d -> (,d) <$> lensOf sh
  _ -> Nothing

genLen :: Gen Int
genLen = choose (1, 3)

genShape :: Int -> Gen [Int]
genShape r = vectorOf r genLen

{- | Dimensionless half the time; otherwise one or two base dimensions to
small powers.
-}
genDim :: Gen Dim
genDim =
  frequency
    [ (4, pure dimOne)
    , (3, dimBase <$> elements [minBound .. maxBound])
    ,
      ( 2
      , do
          k <- choose (1, 2)
          atoms <-
            vectorOf k ((,) <$> elements [minBound .. maxBound] <*> elements [-2, -1, 1, 2])
          pure (dimFromAtoms [(Base b, e) | (b, e) <- atoms])
      )
    ]

{- | A closed target type: numbers with and without dimensions, vectors,
matrices, occasionally rank three, booleans, and functions over these.
-}
genType :: Int -> Gen Type
genType n =
  frequency
    $ [ (4, numD <$> genDim)
      , (3, tensor <$> genShape 1 <*> genDim)
      , (2, tensor <$> genShape 2 <*> genDim)
      , (1, tensor <$> genShape 3 <*> genDim)
      , (2, pure BoolT)
      ]
      ++ [(3, TFun <$> genType (n `div` 2) <*> genType (n `div` 2)) | n > 1]

-- | A small type for an argument or an intermediate value.
genArgType :: Gen Type
genArgType = genType 2

-- Scope ---------------------------------------------------------------------------

{- | A variable in scope: a monomorphic one at the type it was built for
(and whether inference sees its rank), or a polymorphic helper.
-}
data Binding
  = Mono Type Bool
  | Poly Helper

data Entry = Entry Text Binding

type Scope = [Entry]

-- | Bind a name, shadowing any earlier binding of it.
bindName :: Text -> Binding -> Scope -> Scope
bindName x b sc = Entry x b : filter (\(Entry y _) -> y /= x) sc

{- | Binder names. None is a primitive or a unit, and the pool is small so
that shadowing is common.
-}
genName :: Gen Text
genName = elements ["x", "y", "z", "u", "v", "w", "f", "g", "p", "q"]

-- Helpers for let-polymorphism ------------------------------------------------------

{- | Closed polymorphic functions with known schemes, bound by a let and used
at two types. A generated right-hand side is never relied on to be
polymorphic.
-}
data Helper
  = -- | @\\x -> x@ : a -> a
    HId
  | -- | @\\x -> x + x@ : Tensor s d -> Tensor s d
    HDouble
  | -- | @\\x -> -x@
    HNeg
  | -- | @\\x -> x ⊙ x@ : Tensor s d -> Tensor s [d^2]
    HSquare
  | -- | @\\x -> x * x@ : Quantity r d -> Quantity r [d^2], used at amounts
    HSq
  | -- | @\\f x -> f (f x)@
    HTwice
  | -- | @\\x y -> x@
    HConst
  | -- | @\\v -> v.0@ : Tensor (n + 1 : s) d -> Tensor s d
    HFirst
  | {- | @\\k v -> k * v@ : Quantity r d -> Quantity r d1 -> Quantity r [d
    d1], used at amounts: a role left open keeps both scalar (design
    §3.10, U9)
    -}
    HScale
  | {- | @\\k v -> 1 * k * v@ : Num d -> Tensor s d1 -> Tensor s [d1 d]: the
    literal fixes the role to an amount's, and the product's unknown-rank
    left operand defaults to a scalar (design §4.2)
    -}
    HScaleAmount
  | -- | @\\x f -> f x@
    HApplyTo
  | -- | @\\f g x -> f (g x)@
    HCompose
  | -- | @\\a b -> a == b@, defaulted to Num -> Num -> Bool
    HEq
  | -- | @\\v -> v \@ v@, defaulted to Vec n d -> Num [d^2]
    HNormSq
  deriving stock (Eq, Show, Enum, Bounded)

-- | Parameters and body.
helperDef :: Helper -> ([Text], S.Expr)
helperDef = \case
  HId -> (["x"], var "x")
  HDouble -> (["x"], binop S.Add (var "x") (var "x"))
  HNeg -> (["x"], mk (S.Neg (var "x")))
  HSquare -> (["x"], binop S.EMul (var "x") (var "x"))
  HSq -> (["x"], binop S.Outer (var "x") (var "x"))
  HTwice -> (["f", "x"], app (var "f") (app (var "f") (var "x")))
  HConst -> (["x", "y"], var "x")
  HFirst -> (["v"], mk (S.Proj (var "v") 0))
  HScale -> (["k", "v"], binop S.Outer (var "k") (var "v"))
  HScaleAmount ->
    (["k", "v"], binop S.Outer (binop S.Outer (mk (S.Num 1)) (var "k")) (var "v"))
  HApplyTo -> (["x", "f"], app (var "f") (var "x"))
  HCompose -> (["f", "g", "x"], app (var "f") (app (var "g") (var "x")))
  HEq -> (["a", "b"], binop S.Eq (var "a") (var "b"))
  HNormSq -> (["v"], binop S.Dot (var "v") (var "v"))

-- | Whether a use's result is pinned: always, never, or when one argument is.
data PinRule = Always | Never | ByArg Int

{- | The argument types at which a helper produces the target type, if it
can, and how the result's pinning follows from the arguments'.
-}
helperUse :: Helper -> Type -> Maybe (Gen [Type], PinRule)
helperUse h t = case h of
  HId -> Just (pure [t], ByArg 0)
  HDouble -> tensorOnly (pure [t], ByArg 0)
  HNeg -> tensorOnly (pure [t], ByArg 0)
  HSquare -> do
    (ls, d) <- asTensor t
    d' <- dimRoot 2 d
    Just (pure [tensor ls d'], ByArg 0)
  HSq -> do
    ([], d) <- asTensor t
    d' <- dimRoot 2 d
    Just (pure [numD d'], Always)
  HTwice -> Just (pure [TFun t t, t], ByArg 1)
  HConst -> Just ((\u -> [t, u]) <$> genArgType, ByArg 0)
  HFirst -> do
    (ls, d) <- asTensor t
    if length ls < maxRank
      then Just ((\k -> [tensor (k : ls) d]) <$> genLen, ByArg 0)
      else Nothing
  HScale -> do
    ([], d) <- asTensor t
    Just ((\d1 -> [numD d1, numD (dimDiv d d1)]) <$> genDim, ByArg 1)
  HScaleAmount -> do
    (ls, d) <- asTensor t
    Just ((\d1 -> [numD d1, tensor ls (dimDiv d d1)]) <$> genDim, ByArg 1)
  HApplyTo -> Just ((\a -> [a, TFun a t]) <$> genArgType, Never)
  HCompose ->
    Just ((\a b -> [TFun b t, TFun a b, a]) <$> genArgType <*> genArgType, Never)
  HEq -> if t == BoolT then Just (pure [numT, numT], Always) else Nothing
  HNormSq -> do
    ([], d) <- asTensor t
    d' <- dimRoot 2 d
    Just ((\k -> [tensor [k] d']) <$> genLen, Always)
 where
  tensorOnly r = asTensor t >> Just r

-- Syntax helpers -----------------------------------------------------------------------

noSpan :: S.Span
noSpan = S.Span (S.Pos 1 1) (S.Pos 1 1)

mk :: S.Node -> S.Expr
mk = S.Expr noSpan

var :: Text -> S.Expr
var = mk . S.Var

app :: S.Expr -> S.Expr -> S.Expr
app f a = mk (S.App f a)

apps :: S.Expr -> [S.Expr] -> S.Expr
apps = foldl app

binop :: S.Op -> S.Expr -> S.Expr -> S.Expr
binop op a b = mk (S.BinOp op a b)

lam :: [Text] -> S.Expr -> S.Expr
lam xs b = mk (S.Lam (map (S.Name noSpan) xs) b)

letIn :: Text -> [Text] -> S.Expr -> S.Expr -> S.Expr
letIn x ps rhs body = mk (S.Let (S.Name noSpan x) (map (S.Name noSpan) ps) rhs body)

-- | Nesting depth of a surface expression.
exprDepth :: S.Expr -> Int
exprDepth e =
  1 + case e.node of
    S.Num _ -> 0
    S.Bool _ -> 0
    S.Var _ -> 0
    S.Lam _ b -> exprDepth b
    S.App f a -> max (exprDepth f) (exprDepth a)
    S.Let _ _ r b -> max (exprDepth r) (exprDepth b)
    S.If c t f -> maximum (map exprDepth [c, t, f])
    S.BinOp _ a b -> max (exprDepth a) (exprDepth b)
    S.Neg a -> exprDepth a
    S.Labelled _ a -> exprDepth a
    S.Tuple es -> maximum (0 : map exprDepth es)
    S.List es -> maximum (0 : map exprDepth es)
    S.CaseOf s alts -> maximum (exprDepth s : map (exprDepth . snd) alts)
    S.Pow a _ -> exprDepth a
    S.SectionL _ a -> exprDepth a
    S.SectionR a _ -> exprDepth a
    S.Vec es -> maximum (0 : map exprDepth es)
    S.Proj a _ -> exprDepth a
    S.Slice a _ _ -> exprDepth a
    S.FieldOf a _ -> exprDepth a
    S.Record hd fs -> maximum (exprDepth hd : map (exprDepth . snd) fs)
    S.Ascribe a _ -> exprDepth a
    S.ChartForm cl ->
      maximum
        ( exprDepth cl.parent
            : map (maybe 0 exprDepth) [cl.origin, cl.step, cl.generators, cl.spin]
        )
    S.FromTo v c c1 -> maximum [exprDepth v, exprDepth c, exprDepth c1]
    S.UnitBody a -> exprDepth a
    S.UnitSyntax a -> exprDepth a

-- Literals and units ------------------------------------------------------------------

-- | Small integers and halves, so that printed numbers re-parse exactly.
genNum :: Gen Rational
genNum =
  frequency
    [ (4, fromInteger <$> choose (-3, 9))
    , (1, elements [1 / 2, 3 / 2, -(1 / 2), 1 / 4])
    ]

-- | A bracket literal of the given lengths.
literalOf :: Gen Rational -> [Int] -> Gen S.Expr
literalOf g = \case
  [] -> mk . S.Num <$> g
  k : rest -> mk . S.Vec <$> vectorOf k (literalOf g rest)

{- | Base units with powers for a ground dimension: @m * s^-2@, or with the
negative powers as a division, @m / s^2@.
-}
unitExpr :: Dim -> Gen S.Expr
unitExpr d = do
  let atoms = [(b, k) | (Base b, k) <- dimAtoms d]
      power b k =
        if k == 1
          then var (baseSymbol b)
          else mk (S.Pow (var (baseSymbol b)) (fromIntegral k))
      pos = [(b, k) | (b, k) <- atoms, k > 0]
      neg = [(b, k) | (b, k) <- atoms, k < 0]
  asDivision <- arbitrary
  pure $ case (asDivision, pos) of
    (True, p : ps) ->
      foldl
        (\acc (b, k) -> binop S.Div acc (power b (negate k)))
        (products (p : ps))
        neg
    _ -> products atoms
 where
  products =
    foldl1 (binop S.Outer)
      . map
        ( \(b, k) ->
            if k == 1
              then var (baseSymbol b)
              else mk (S.Pow (var (baseSymbol b)) (fromIntegral k))
        )

-- | A literal quantity: @[1, 2] m@, @3 (m/s^2)@, @5@ (design §3.10, U4).
quantity :: [Int] -> Dim -> Gen S.Expr
quantity ls d = do
  lit <- literalOf genNum ls
  if isDimOne d
    then pure lit
    else do
      u <- unitExpr d
      pure (binop S.Scale lit u)

-- | A zero of the given type whose rank inference sees, for pinning.
zeroOf :: [Int] -> Dim -> S.Expr
zeroOf ls d
  | isDimOne d = lit
  | otherwise =
      binop
        S.Scale
        lit
        ( foldl1
            (binop S.Outer)
            [mk (S.Pow (var (baseSymbol b)) (fromIntegral k)) | (Base b, k) <- dimAtoms d]
        )
 where
  lit = go ls
  go = \case
    [] -> mk (S.Num 0)
    k : rest -> mk (S.Vec (replicate k (go rest)))

-- The generator ---------------------------------------------------------------------------

{- | A generated expression and whether inference sees its rank (for a
tensor) or that it is a Bool, from the expression alone.
-}
data G = G {expr :: S.Expr, pinned :: Bool}

-- | Make an operand's rank visible to inference, if it is not already.
pin :: Type -> G -> G
pin t g
  | g.pinned = g
  | otherwise = case t of
      BoolT -> G (binop S.And g.expr (mk (S.Bool True))) True
      _ | Just (ls, d) <- asTensor t -> G (binop S.Add g.expr (zeroOf ls d)) True
      _ -> g

-- | A closed program of a random type, with that type.
genProgram :: Gen (Type, S.Expr)
genProgram = sized $ \size -> do
  t <- genType 4
  e <- genTyped t [] (size `div` 2 + 4)
  pure (t, e)

{- | An expression of the given closed type in a scope of variables of known
(monomorphic) types, of roughly the given size.
-}
genTyped :: Type -> [(Text, Type)] -> Int -> Gen S.Expr
genTyped t vars n = (.expr) <$> gen [Entry x (Mono ty False) | (x, ty) <- reverse vars] t n

gen :: Scope -> Type -> Int -> Gen G
gen sc t n
  | n <= 0 = leaf sc t
  | otherwise = frequency (common ++ specific)
 where
  common =
    [(2, leaf sc t)]
      ++ [(4, useVar sc t n) | not (null (calls sc t))]
      ++ [(4, useHelper sc t n) | not (null (helperCalls sc t))]
      ++ [ (2, letMono sc t n)
         , (1, letPoly sc t n)
         , (2, applyFresh sc t n)
         , (1, ifThen sc t n)
         ]
  specific = case t of
    BoolT -> boolProds sc n
    TFun a b -> funProds sc a b n
    _ -> case asTensor t of
      Just (ls, d) -> tensorProds sc ls d n
      Nothing -> []

-- | A literal, or a variable of the type.
leaf :: Scope -> Type -> Gen G
leaf sc t = frequency ((3, literal) : [(3, elements vars) | not (null vars)])
 where
  vars = [G (var x) p | Entry x (Mono ty p) <- sc, ty == t]
  literal = case t of
    BoolT -> (\b -> G (mk (S.Bool b)) True) <$> arbitrary
    TFun a b -> do
      x <- genName
      body <- leaf (bindName x (Mono a False) sc) b
      pure (G (lam [x] body.expr) False)
    _ -> case asTensor t of
      Just (ls, d) -> (`G` True) <$> quantity ls d
      Nothing -> error ("Gen.leaf: not a closed type: " <> show t)

-- | Monomorphic variables that produce the type after some arguments.
calls :: Scope -> Type -> [(Text, [Type], Bool)]
calls sc t =
  [ (x, args, p && null args) | Entry x (Mono ty p) <- sc, Just args <- [argsFor ty]
  ]
 where
  argsFor ty
    | ty == t = Just []
    | TFun a r <- ty = (a :) <$> argsFor r
    | otherwise = Nothing

useVar :: Scope -> Type -> Int -> Gen G
useVar sc t n = do
  (x, args, p) <- elements (calls sc t)
  as <- mapM (\a -> gen sc a (n `div` (length args + 1))) args
  pure (G (apps (var x) (map (.expr) as)) p)

helperCalls :: Scope -> Type -> [(Text, Gen [Type], PinRule)]
helperCalls sc t = [(x, g, r) | Entry x (Poly h) <- sc, Just (g, r) <- [helperUse h t]]

useHelper :: Scope -> Type -> Int -> Gen G
useHelper sc t n = do
  (x, argTypes, rule) <- elements (helperCalls sc t)
  helperApply sc x argTypes rule n

helperApply :: Scope -> Text -> Gen [Type] -> PinRule -> Int -> Gen G
helperApply sc x argTypes rule n = do
  tys <- argTypes
  as <- mapM (\a -> gen sc a (n `div` (length tys + 1))) tys
  let p = case rule of
        Always -> True
        Never -> False
        ByArg i -> (as !! i).pinned
  pure (G (apps (var x) (map (.expr) as)) p)

{- | @let x = e in body@, monomorphic: the body sees @x@ at the type it was
built for. A function may be bound with parameters, @let f y = … in …@.
-}
letMono :: Scope -> Type -> Int -> Gen G
letMono sc t n = do
  x <- genName
  u <- frequency [(3, genArgType), (1, pure t)]
  (rhs, p) <- case u of
    TFun a b -> do
      withParam <- arbitrary
      if withParam
        then do
          y <- genName
          body <- gen (bindName y (Mono a False) sc) b (n `div` 2)
          pure (Left (y, body.expr), False)
        else (\g -> (Right g.expr, g.pinned)) <$> gen sc u (n `div` 2)
    _ -> (\g -> (Right g.expr, g.pinned)) <$> gen sc u (n `div` 2)
  body <- gen (bindName x (Mono u p) sc) t (n `div` 2)
  pure $ case rhs of
    Left (y, b) -> G (letIn x [y] b body.expr) body.pinned
    Right e -> G (letIn x [] e body.expr) body.pinned

{- | @let h = helper in let u = h … in let w = h … in body@: a polymorphic
helper used at two different types, and then possibly more in the body.
-}
letPoly :: Scope -> Type -> Int -> Gen G
letPoly sc t n = do
  h <- elements [minBound .. maxBound]
  hName <- genName
  let (params, hBody) = helperDef h
      sc1 = bindName hName (Poly h) sc
      quarter = n `div` 4
  -- Two result types the helper can produce, distinct when there are two
  -- (`HEq` only ever gives Bool), so that the helper is instantiated twice
  -- differently.
  u1 <- usable h
  u2 <- fromMaybe u1 <$> (usable h `suchThatMaybe` (/= u1))
  g1 <- useAt sc1 hName h u1 quarter
  -- The second use needs the helper in scope.
  n1 <- genName `suchThat` (/= hName)
  let sc2 = bindName n1 (Mono u1 g1.pinned) sc1
  g2 <- useAt sc2 hName h u2 quarter
  n2 <- genName
  let sc3 = bindName n2 (Mono u2 g2.pinned) sc2
  body <- gen sc3 t (n `div` 2)
  withParams <- arbitrary
  let def =
        if withParams
          then letIn hName params hBody
          else letIn hName [] (lam params hBody)
  pure (G (def (letIn n1 [] g1.expr (letIn n2 [] g2.expr body.expr))) body.pinned)
 where
  usable h =
    genArgType `suchThat` \u -> case helperUse h u of
      Just _ -> True
      Nothing -> False
  useAt s x h u m = case helperUse h u of
    Just (argTypes, rule) -> helperApply s x argTypes rule m
    Nothing -> error "Gen.letPoly: helper does not apply"

{- | @f a@ with @f@ built at a fresh function type @A -> t@: often a beta
redex, sometimes a section or a composition.
-}
applyFresh :: Scope -> Type -> Int -> Gen G
applyFresh sc t n = do
  a <- genArgType
  f <- gen sc (TFun a t) (n `div` 2)
  x <- gen sc a (n `div` 2)
  pure (G (app f.expr x.expr) False)

ifThen :: Scope -> Type -> Int -> Gen G
ifThen sc t n = do
  c <- gen sc BoolT (n `div` 3)
  a <- gen sc t (n `div` 3)
  b <- gen sc t (n `div` 3)
  pure (G (mk (S.If c.expr a.expr b.expr)) (a.pinned || b.pinned))

-- | Equality takes tensors of any shape and booleans.
genEqType :: Gen Type
genEqType =
  frequency
    [(4, tensor <$> (choose (0, 2) >>= genShape) <*> genDim), (1, pure BoolT)]

boolProds :: Scope -> Int -> [(Int, Gen G)]
boolProds sc n =
  [
    ( 3
    , do
        d <- genDim
        op <- elements [S.Lt, S.Le, S.Gt, S.Ge]
        a <- gen sc (numD d) half
        b <- gen sc (numD d) half
        pure (G (binop op a.expr b.expr) True)
    )
  ,
    ( 3
    , do
        ty <- genEqType
        op <- elements [S.Eq, S.Ne]
        a <- gen sc ty half
        b <- gen sc ty half
        -- An unknown equality type defaults to Num, so one operand must
        -- show its type unless Num is what was meant.
        let a' = if ty == numT then a else pin ty a
        swap <- arbitrary
        pure
          (G (if swap then binop op b.expr a'.expr else binop op a'.expr b.expr) True)
    )
  ,
    ( 2
    , do
        op <- elements [S.And, S.Or]
        a <- gen sc BoolT half
        b <- gen sc BoolT half
        pure (G (binop op a.expr b.expr) True)
    )
  , (1, (\a -> G (app (var "not") a.expr) True) <$> gen sc BoolT (n - 1))
  ]
 where
  half = n `div` 2

funProds :: Scope -> Type -> Type -> Int -> [(Int, Gen G)]
funProds sc a b n =
  [
    ( 5
    , do
        x <- genName
        body <- gen (bindName x (Mono a False) sc) b (n - 1)
        merge <- arbitrary
        pure $ case body.expr.node of
          S.Lam ns e | merge -> G (mk (S.Lam (S.Name noSpan x : ns) e)) False
          _ -> G (lam [x] body.expr) False
    )
  ,
    ( 1
    , do
        c <- genArgType
        f <- gen sc (TFun c b) (n `div` 2)
        g <- gen sc (TFun a c) (n `div` 2)
        pure (G (binop S.Compose f.expr g.expr) False)
    )
  ]
    ++ map (fmap (fmap (`G` False))) (sections ++ etas)
 where
  half = n `div` 2
  ta = asTensor a
  tb = asTensor b
  sections = case (ta, tb) of
    (Just (la, da), Just (lb, db)) ->
      [ ( 2
        , do
            op <- elements [S.Add, S.Sub]
            e <- gen sc a half
            left <- arbitrary
            pure (mk (if left then S.SectionL op e.expr else S.SectionR e.expr op))
        )
      | a == b
      ]
        ++ [ ( 1
             , (\e -> mk (S.SectionL S.EMul e.expr)) <$> gen sc (tensor la (dimDiv db da)) half
             )
           | la == lb
           ]
        ++ [ (1, (\e -> mk (S.SectionL S.Div e.expr)) <$> gen sc (numD (dimDiv da db)) half)
           | la == lb
           ]
        -- (* e) is \x -> x * e: x is a left operand nobody pins, so only
        -- when it is meant to be a scalar; e is pinned when it is a tensor,
        -- which fixes the role to an amount's (design §3.10, U9).
        ++ [ ( 1
             , do
                 let te = tensor lb (dimDiv db da)
                 e <- gen sc te half
                 pure (mk (S.SectionL S.Outer (if null lb then e else pin te e).expr))
             )
           | null la
           ]
        -- (e *) is \x -> e * x, with x's shape a suffix of the result's.
        ++ [ ( 1
             , do
                 let le = take (length lb - length la) lb
                     te = tensor le (dimDiv db da)
                 e <- pin te <$> gen sc te half
                 pure (mk (S.SectionR e.expr S.Outer))
             )
           | length lb >= length la
           , drop (length lb - length la) lb == la
           ]
    _ -> []
  etas =
    [(1, pure (var "neg")) | a == b, Just _ <- [ta]]
      ++ [(1, pure (var "abs")) | a == b, Just _ <- [ta]]
      ++ [(1, (\e -> app (var "add") e.expr) <$> gen sc a half) | a == b, Just _ <- [ta]]
      ++ [(1, pure (var "not")) | a == BoolT, b == BoolT]
      ++ [ (1, pure (var "transpose"))
         | Just ([r, c], d) <- [ta]
         , Just ([c', r'], d') <- [tb]
         , r == r'
         , c == c'
         , d == d'
         ]

tensorProds :: Scope -> [Int] -> Dim -> Int -> [(Int, Gen G)]
tensorProds sc ls d n =
  [
    ( 2
    , do
        op <- elements [S.Add, S.Sub]
        a <- gen sc t half
        b <- gen sc t half
        pure (G (binop op a.expr b.expr) (a.pinned || b.pinned))
    )
  , (1, (\a -> G (mk (S.Neg a.expr)) a.pinned) <$> gen sc t (n - 1))
  , (1, (\a -> G (app (var "abs") a.expr) a.pinned) <$> gen sc t (n - 1))
  ,
    ( 2
    , do
        d1 <- genDim
        a <- gen sc (tensor ls d1) half
        b <- gen sc (tensor ls (dimDiv d d1)) half
        pure (G (binop S.EMul a.expr b.expr) (a.pinned || b.pinned))
    )
  ,
    ( 1
    , do
        d1 <- genDim
        a <- gen sc (tensor ls (dimMul d d1)) half
        b <- gen sc (tensor ls d1) half
        pure (G (binop S.EDiv a.expr b.expr) (a.pinned || b.pinned))
    )
  ,
    ( 2
    , do
        d2 <- genDim
        a <- gen sc (tensor ls (dimMul d d2)) half
        b <- gen sc (numD d2) half
        pure (G (binop S.Div a.expr b.expr) a.pinned)
    )
  ,
    ( 3
    , do
        -- Tensor product: the shapes concatenate, the dimensions multiply.
        i <- choose (0, length ls)
        d1 <- genDim
        let (l1, l2) = splitAt i ls
            ta = tensor l1 d1
        a0 <- gen sc ta half
        let tb = tensor l2 (dimDiv d d1)
        b0 <- gen sc tb half
        -- An unseen left rank defaults to a scalar, and so do both operands
        -- when neither shows its role (design §3.10, U9): a tensor operand
        -- is pinned, which makes it an amount.
        let a = if null l1 then a0 else pin ta a0
            b = if null l2 then b0 else pin tb b0
        pure (G (binop S.Outer a.expr b.expr) (a.pinned && b.pinned))
    )
  , (2, vmapProd)
  ,
    ( 1
    , do
        a <- gen sc t (n - 1)
        u <-
          (`G` True)
            <$> if isDimOne d then pure (binop S.Div (var "m") (var "m")) else unitExpr d
        pure (G (binop S.To a.expr u.expr) a.pinned)
    )
  ]
    ++ [
         ( 2
         , do
             -- Contracting product: the left operand's last length against the
             -- right operand's first.
             k <- genLen
             i <- choose (max 0 (length ls - (maxRank - 1)), min (length ls) (maxRank - 1))
             d1 <- genDim
             let (l1, l2) = splitAt i ls
                 ta = tensor (l1 ++ [k]) d1
             a0 <- gen sc ta half
             b <- gen sc (tensor (k : l2) (dimDiv d d1)) half
             -- An unseen left rank defaults to a vector.
             let a = if null l1 then a0 else pin ta a0
             pure (G (binop S.Dot a.expr b.expr) (a.pinned && b.pinned))
         )
       ]
    ++ case ls of
      k : rest ->
        [
          ( 3
          , do
              es <- vectorOf k (gen sc (tensor rest d) (n `div` k))
              pure (G (mk (S.Vec (map (.expr) es))) (any (.pinned) es))
          )
        ]
      [] -> []
    ++ [ ( 2
         , do
             k <- genLen
             i <- choose (0, k - 1)
             a <- gen sc (tensor (k : ls) d) (n - 1)
             pure (G (mk (S.Proj a.expr i)) a.pinned)
         )
       | length ls < maxRank
       ]
    ++ [ ( 1
         , do
             -- A slice along a later axis: insert its length after the first
             -- `axis` lengths of the result.
             axis <- choose (1, length ls)
             k <- genLen
             i <- choose (0, k - 1)
             let (l1, l2) = splitAt axis ls
             a <- gen sc (tensor (l1 ++ k : l2) d) (n - 1)
             pure (G (mk (S.Slice a.expr axis i)) a.pinned)
         )
       | not (null ls)
       , length ls < maxRank
       ]
    ++ case ls of
      [] ->
        [
          ( 2
          , do
              (e, d') <- elements (powers d)
              a <- gen sc (numD d') (n - 1)
              pure (G (mk (S.Pow a.expr e)) True)
          )
        ]
          ++ [ ( 1
               , do
                   f <- elements ["floor", "ceil", "round"]
                   a <- gen sc numT (n - 1)
                   pure (G (app (var f) a.expr) True)
               )
             | isDimOne d
             ]
          ++ [
               ( 1
               , oneof
                   ( scalarUnimplemented
                       ++ concat [angles | isDimOne d]
                       ++ concat [inverses | d == dimBase Ang]
                   )
               )
             ]
      [r, c] ->
        [
          ( 1
          , (\a -> G (app (var "transpose") a.expr) True)
              <$> gen sc (tensor [c, r] d) (n - 1)
          )
        ]
          ++ [ ( 1
               , do
                   d1 <- genDim
                   a <- gen sc (tensor [r] d1) half
                   b <- gen sc (tensor [r] (dimDiv d d1)) half
                   pure (G (binop S.Wedge a.expr b.expr) True)
               )
             | r == c
             ]
          -- Typed, but evaluates to "not implemented".
          ++ [ ( 1
               , (\a -> G (app (var "inverse") a.expr) True)
                   <$> gen sc (tensor [r, r] (dimInv d)) (n - 1)
               )
             | r == c
             ]
      [3] ->
        [
          ( 1
          , (\a -> G (app (var "star") a.expr) True) <$> gen sc (tensor [3, 3] d) (n - 1)
          )
        ]
      _ -> []
 where
  t = tensor ls d
  half = n `div` 2
  vmapProd = do
    d1 <- genDim
    f <- gen sc (TFun (numD d1) (numD d)) half
    a <- gen sc (tensor ls d1) half
    pure (G (apps (var "vmap") [f.expr, a.expr]) a.pinned)
  -- Typed, but evaluate to "not implemented"; kept rare so that most
  -- programs evaluate to a value.
  scalarUnimplemented =
    [ do
        a <- gen sc t half
        b <- gen sc t half
        pure (G (binop (S.PlusMinus Bound) a.expr b.expr) True)
    , (\a -> G (app (var "sqrt") a.expr) True) <$> gen sc (numD (dimPow 2 d)) (n - 1)
    , do
        k <- genLen
        a <- gen sc (tensor [k] d) (n - 1)
        pure (G (app (var "norm") a.expr) True)
    ]
  -- Dimensionless results: exp and log of a number, sin and cos of an angle.
  angles = [transcendental, circular]
  transcendental = do
    f <- elements ["exp", "log"]
    a <- gen sc numT (n - 1)
    pure (G (app (var f) a.expr) True)
  circular = do
    f <- elements ["sin", "cos"]
    a <- gen sc (numD (dimBase Ang)) (n - 1)
    pure (G (app (var f) a.expr) True)
  -- Results in radians: the inverse functions.
  inverses = [arctan2, arctan]
  arctan2 = do
    d1 <- genDim
    a <- gen sc (numD d1) half
    b <- gen sc (numD d1) half
    pure (G (apps (var "atan2") [a.expr, b.expr]) True)
  arctan = do
    a <- gen sc numT (n - 1)
    pure (G (app (var "atan") a.expr) True)

-- | Exponents @e@ and bases @d'@ with @d'^e = d@.
powers :: Dim -> [(Integer, Dim)]
powers d =
  [(1, d), (-1, dimInv d)]
    ++ mapMaybe (\e -> (e,) <$> dimRoot (fromIntegral e) d) [2, 3, -2]

-- Checking the generator ----------------------------------------------------------------

{- | Whether a closed type is an instance of a scheme: one-way matching of
the quantified variables, each at its kind. Dimensions are matched after
the structure, as equations solved one unknown at a time, so a composite
such as @[d d1]@ met before its parts is solved once they are known.
-}
instanceOf :: Scheme -> Type -> Bool
instanceOf (Forall vs pat) target = case matchType pat target (Map.empty, []) of
  Nothing -> False
  Just (m, eqs) -> solveDims m eqs
 where
  quantified v = v `elem` map fst vs
  matchType p t st = case (p, t) of
    (TVar v, _) | quantified v -> bindArg v (AType t) st
    (TFun a b, TFun c d) -> matchType a c st >>= matchType b d
    -- A quantity of a role variable is an amount at an amount (design
    -- §3.10, U9).
    (TQty ra sa da, TQty rb sb db) ->
      second ((da, db) :) <$> (matchRole ra rb st >>= matchShape sa sb)
    (BoolT, BoolT) -> Just st
    _ -> Nothing
  matchShape p sh st = case (p, sh) of
    (SVar v, _) | quantified v -> bindArg v (AShape sh) st
    (SCons l a r, SCons l' a' r') -> matchLen l l' st >>= matchAxis a a' >>= matchShape r r'
    (SNil, SNil) -> Just st
    _ -> Nothing
  matchLen p l st = case (p, l) of
    (LVar v k, LLit j) | quantified v, j >= k -> bindArg v (ALen (LLit (j - k))) st
    (LLit a, LLit b) | a == b -> Just st
    _ -> Nothing
  matchRole p r st = case p of
    RVar v | quantified v -> bindArg v (ARole r) st
    _ | p == r -> Just st
    _ -> Nothing
  matchAxis p a st = case p of
    AVar v | quantified v -> bindArg v (AAxis a) st
    _ | p == a -> Just st
    _ -> Nothing
  bindArg v a (m, eqs) = case Map.lookup v m of
    Nothing -> Just (Map.insert v a m, eqs)
    Just a' | a' == a -> Just (m, eqs)
    _ -> Nothing
  solveDims :: Map VarId Arg -> [(Dim, Dim)] -> Bool
  solveDims m eqs
    | null eqs = True
    | otherwise = case foldM step (m, [], False) eqs of
        Nothing -> False
        Just (m', rest, progressed) -> progressed && solveDims m' rest
  step (m, rest, progressed) (p, actual) =
    let known = dimFromAtoms [(a, k) | (a, k) <- dimAtoms p, not (unbound m a)]
        known' = foldr dimMul dimOne [subst m a k | (a, k) <- dimAtoms known]
     in case [(v, k) | (DVar v, k) <- dimAtoms p, unbound m (DVar v)] of
          [] -> if known' == actual then Just (m, rest, True) else Nothing
          [(v, k)] -> do
            root <- dimRoot k (dimDiv actual known')
            Just (Map.insert v (ADim root) m, rest, True)
          _ -> Just (m, (p, actual) : rest, progressed)
  unbound m = \case
    DVar v -> quantified v && not (Map.member v m)
    Base _ -> False
  subst m a k = case a of
    DVar v | Just (ADim d) <- Map.lookup v m -> dimPow k d
    _ -> dimFromAtoms [(a, k)]

-- Core terms ------------------------------------------------------------------------

{- | The number of variables in scope, as a singleton, so that a generator
can build a well-scoped term in any scope.
-}
data Depth (n :: Nat) where
  DZ :: Depth Z
  DS :: Depth n -> Depth (S n)

data SomeDepth = forall n. SomeDepth (Depth n)

-- | A term in a scope of some size, with that size.
data SomeTerm = forall n. SomeTerm (Depth n) (Term n)

instance Show SomeTerm where
  show (SomeTerm _ t) = show t

depthOf :: Int -> SomeDepth
depthOf k
  | k <= 0 = SomeDepth DZ
  | otherwise = case depthOf (k - 1) of SomeDepth d -> SomeDepth (DS d)

depthPlus :: Vec k a -> Depth n -> Depth (Plus k n)
depthPlus ks d = case ks of
  VNil -> d
  VCons _ rest -> DS (depthPlus rest d)

-- | Every variable in scope.
fins :: Depth n -> [Fin n]
fins = \case
  DZ -> []
  DS d -> FZ : map FS (fins d)

-- | A name for each variable in scope, repeating so that printing primes some.
scopeNames :: Depth n -> Vec n Text
scopeNames = \case
  DZ -> VNil
  DS d -> VCons "x" (scopeNames d)

-- | Three hashes, so that references, rewrites and constructors collide.
coreHashes :: [Hash]
coreHashes = [Hash (BS.pack [i]) | i <- [0, 1, 2]]

{- | Primitive names, the reading markers among them, at any arity: the
traversal does not care whether a term would check.
-}
corePrims :: [Text]
corePrims = ["add", "neg", "scale", "pointOn", "§quantity:0", "§to:1", "§from:0", "eq"]

genHint :: Gen Hint
genHint = elements ["x", "y", "", "§s0", "_"]

genLabel :: Gen Label
genLabel =
  oneof
    [ Owner <$> word
    , Tag <$> word
    , Axes <$> word
    , SpaceLabel <$> word
    , FrameLabel <$> word <*> arbitrary
    ]
 where
  word = elements ["a", "b"]

genConRef :: Gen ConRef
genConRef = UserCon <$> elements coreHashes <*> choose (0, 2)

genCoreRef :: Gen (Term n)
genCoreRef =
  Ref
    <$> elements coreHashes
    <*> elements [Nothing, Just 0, Just 1, Just 2]
    <*> elements ["a", "b", "metre", ""]

{- | A well-scoped Core term of any shape (core.md §9): every constructor,
binders of every kind, references with and without cycle indices. Not
typed; for the walks that do not look at types.
-}
genCoreTerm :: forall n. Depth n -> Int -> Gen (Term n)
genCoreTerm d size
  | size <= 1 = atomic
  | otherwise = frequency [(1, atomic), (6, node)]
 where
  smaller = size * 2 `div` 3
  sub = genCoreTerm d smaller
  under :: Vec k Hint -> Gen (Term (Plus k n))
  under hs = genCoreTerm (depthPlus hs d) smaller
  some g = choose (0, 3) >>= (`vectorOf` g)
  kind = elements [Bound, Stat]
  atomic =
    oneof
      $ [Var <$> elements (fins d) | not (null (fins d))]
        ++ [ genCoreRef
           , (\r -> Lit (LTensor ([], [r]))) . fromInteger <$> choose (-3, 3)
           , pure (Lit (LTensor ([2], [1, 2])))
           , Noise <$> kind <*> genLabel <*> choose (1, 3)
           , (`PrimApp` []) <$> elements corePrims
           ]
  node =
    oneof
      [ PrimApp <$> elements corePrims <*> some sub
      , genHint >>= \h -> Lam h <$> under (VCons h VNil)
      , App <$> sub <*> sub
      , genHint >>= \h -> Let h <$> sub <*> under (VCons h VNil)
      , Con <$> genConRef <*> some sub
      , Case <$> sub <*> some alt
      , Pow <$> sub <*> choose (-3, 3)
      , Uncertain <$> kind <*> genLabel <*> sub <*> sub
      , Pack <$> some sub
      , Proj <$> sub <*> choose (0, 2)
      , cycleOf
      ]
  alt = do
    c <- genConRef
    k <- choose (0, 2)
    hs <- vectorOf k genHint
    case vecFromList hs of
      SomeVec v -> Alt c v <$> under v
  cycleOf = do
    k <- choose (1, 3)
    hs <- vectorOf k genHint
    case vecFromList hs of
      SomeVec v -> Cycle v <$> vecTraverse (const (under v)) v

-- | A Core term in a scope of zero to three variables.
genSomeTerm :: Gen SomeTerm
genSomeTerm = do
  k <- choose (0, 3)
  case depthOf k of
    SomeDepth d -> SomeTerm d <$> sized (genCoreTerm d . min 40)
