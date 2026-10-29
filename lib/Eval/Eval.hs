{- | A direct, environment-passing, call-by-need evaluator over Typed Core
(design §8). Type abstractions and applications are erased. Because terms
have been inferred and linted, the remaining type-error cases are
unreachable; they exist to keep the pattern matches total and are reported
as internal errors.

Tensors are one runtime shape: a flat row-major buffer of element thunks
beside the list of lengths, a dimension vector, and an optional display
unit (design §3.2.12). A number is the rank-zero case with a buffer of
one. Elements are magnitudes (design §3.2): exact rationals, or affine
forms once an approximation or a declared uncertainty has entered.
Magnitudes are always in SI base units; the display unit says how to
print them. The dimension vector and the display unit exist only for
printing: types are checked before evaluation.
-}
module Eval.Eval (
  Value (..),
  Closure (..),
  Elem,
  Thunk,
  EvalError (..),
  Config (..),
  defaultConfig,
  precisionOf,
  Runtime (..),
  UnitAtom (..),
  UnitHint (..),
  UnitFactor (..),
  Site (..),
  eval,
  evalClosed,
  evalAt,
  apply,
  scalar,
  render,
) where

import Control.Monad (foldM)
import Data.List (nub)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Eval.Affine
import Eval.Core
import Eval.Dimension
import Eval.TCore

{- | Evaluation parameters: the number of significant digits printed, and the
number of standard deviations a comparison must clear to be decided (design
§3.2.9).
-}
data Config = Config
  { precision :: Int
  , sigma :: Int
  }
  deriving stock (Show)

defaultConfig :: Config
defaultConfig = Config{precision = 20, sigma = 3}

-- | Working precision: the scale plus guard digits (design §3.2.8).
precisionOf :: Config -> Precision
precisionOf cfg = cfg.precision + 4

{- | What the evaluator needs from the codebase: the Typed Core behind a
reference, and whether a reference was declared a display unit.
-}
data Runtime = Runtime
  { typedOf :: Hash -> Maybe (TTerm Z)
  , isUnit :: Hash -> Maybe Int -> Bool
  }

data EvalError
  = DivideByZero
  | -- | a function applied to an enclosure that leaves its domain
    Domain Text
  | -- | a comparison or integer rounding the enclosure cannot settle
    Undecided Text
  | UnknownRef Hash
  | BadCycleIndex Int
  | Unsupported Text
  | -- | Unreachable for linted terms.
    Internal Text
  deriving stock (Eq, Show)

type Thunk = Either EvalError Value

-- | A tensor element, lazily.
type Elem = Either EvalError Magnitude

-- | The environment for a term in scope @n@.
type Env n = Vec n Thunk

{- | Where a node sits: the enclosing top-level definition and the path of
child indices down to it, innermost first. Declared uncertainty takes its
identity from here (design §3.2.4). Erased type nodes do not count, so
the path is the Core path and survives re-elaboration.
-}
data Site = Site {definition :: Hash, path :: [Int]}

-- | A factor of a display unit: a declared unit by reference, or a base unit.
data UnitAtom
  = UnitRef Hash (Maybe Int)
  | UnitBase Text
  deriving stock (Eq, Ord, Show)

{- | How to print a value: the unit atoms with exponents, the unit's
magnitude in base units, and its dimension (which must match the value's
for the hint to be used).
-}

{- | One named unit in a display hint, raised to a power, with the dimension
and magnitude of a single power of it.
-}
data UnitFactor = UnitFactor
  {atom :: UnitAtom, power :: Int, unitDim :: Dim, unitFactor :: Magnitude}
  deriving stock (Eq, Show)

data UnitHint = UnitHint
  { atoms :: [UnitFactor]
  -- ^ in order of first appearance, so @V A@ prints as written
  , factor :: Magnitude
  -- ^ the product of the atoms
  , dim :: Dim
  -- ^ the product of the atoms
  }
  deriving stock (Eq, Show)

data Value
  = -- | lengths, dimension, display unit, flat row-major elements in SI base units
    VTensor [Int] Dim (Maybe UnitHint) (Vector Elem)
  | VBool Bool
  | VClosure Closure

{- | A function value: a body under one binder, closed over its environment
and its site.
-}
data Closure = forall n. Closure Site (Env n) (TTerm (S n))

-- | Evaluate a closed term that belongs to no definition.
evalClosed :: Config -> Runtime -> TTerm Z -> Thunk
evalClosed cfg rt = evalAt cfg rt (Hash mempty)

-- | Evaluate a closed term as the body of the definition with the given hash.
evalAt :: Config -> Runtime -> Hash -> TTerm Z -> Thunk
evalAt cfg rt h = eval cfg rt (Site h []) VNil

eval :: Config -> Runtime -> Site -> Env n -> TTerm n -> Thunk
eval cfg rt = go
 where
  p = precisionOf cfg

  go :: Site -> Env m -> TTerm m -> Thunk
  go site env = \case
    TVr i -> lookupEnv i env
    TRef h mi -> case rt.typedOf h of
      Nothing -> Left (UnknownRef h)
      Just t -> do
        v <- case mi of
          Nothing -> go (Site h []) VNil t
          Just i -> case t of
            TCycle _ _ bodies -> case vecIndex i (cycleMembers h VNil bodies) of
              Just member -> member
              Nothing -> Left (BadCycleIndex i)
            _ -> Left (BadCycleIndex i)
        -- A declared unit is its own display unit (design §3.2.12).
        if rt.isUnit h mi then asUnit (UnitRef h mi) v else Right v
    TPrimApp prim _ args -> runPrim cfg rt prim (zipWith (\i a -> go (child i) env a) [0 ..] args)
    TLit (LTensor dims rs) -> Right (VTensor dims dimOne Nothing (V.fromList (map (Right . Exact) rs)))
    TLit (LBool b) -> Right (VBool b)
    TLam _ _ body -> Right (VClosure (Closure (child 0) env body))
    TApp f a -> do
      fv <- go (child 0) env f
      apply cfg rt fv (go (child 1) env a)
    TLet _ _ e body -> go (child 1) (VCons (go (child 0) env e) env) body
    TIf c t e -> do
      cv <- go (child 0) env c
      case cv of
        VBool True -> go (child 1) env t
        VBool False -> go (child 2) env e
        _ -> Left (Internal "if: condition is not a boolean")
    TPow t n -> do
      (x, d, hint) <- scalarFull =<< go (child 0) env t
      r <- arith (powM p x n)
      Right (num (dimPow (fromIntegral n) d) (hintPow p (fromIntegral n) =<< hint) r)
    -- Fresh unit nudges, one per component (design §3.2.5).
    TNoise k l n ->
      let count = fromInteger n
       in Right
            ( VTensor
                [count]
                dimOne
                Nothing
                (V.generate count (\i -> Right (unitNoise k (originOf site l i))))
            )
    TUncertain k l x e -> do
      (xv, d, hint) <- scalarFull =<< go (child 0) env x
      (ev, _, _) <- scalarFull =<< go (child 1) env e
      Right (num d hint (uncertain k (originOf site l 0) xv ev))
    -- Stack the component buffers; the shapes agree by lint. A component
    -- that fails to evaluate becomes a block of failing elements of the
    -- shape the other components have, so an error in one component is
    -- only raised when that component is used. The first component's
    -- display unit is kept.
    TPack ts ->
      let results = zipWith (\i t -> tensor =<< go (child i) env t) [0 ..] ts
          known = [(dims, d, hint) | Right (dims, d, hint, _) <- results]
       in case (results, known) of
            ([], _) -> Right (VTensor [0] dimOne Nothing V.empty)
            (_, (dims, d, hint) : _) ->
              let block = \case
                    Right (_, _, _, buf) -> buf
                    Left err -> V.replicate (product dims) (Left err)
               in Right (VTensor (length results : dims) d hint (V.concat (map block results)))
            (Left err : _, []) -> Left err
            (Right _ : _, []) -> Left (Internal "unreachable: a tensor with no shape")
    -- Slice out component i: a view, not a copy.
    TProj t i -> do
      (dims, d, hint, buf) <- tensor =<< go (child 0) env t
      case dims of
        k : rest
          | i < k ->
              let stride = product rest
               in Right (VTensor rest d hint (V.slice (i * stride) stride buf))
        _ -> Left (Internal ("projection ." <> tshow i <> " out of range"))
    -- Erasure.
    TTyLam _ _ b -> go site env b
    TTyApp b _ -> go site env b
    -- A cycle is not itself a value; it is reached through @TRef h (Just i)@.
    TCycle{} -> Left (BadCycleIndex (-1))
   where
    child i = site{path = i : site.path}

  -- Knot-tying: every member is evaluated in an environment that already
  -- contains all the members. 'vecMap' and 'vecAppend' inspect only the
  -- spine, so the recursion is productive.
  cycleMembers :: Hash -> Env m -> Vec k (TTerm (Plus k m)) -> Vec k Thunk
  cycleMembers h env bodies = members
   where
    members = vecMapIndexed (\i -> go (Site h [i]) (vecAppend members env)) bodies

{- | The identity of a declared nudge (design §3.2.4): where it sits, unless
it carries a tag.
-}
originOf :: Site -> Label -> Int -> Origin
originOf site l i = case l of
  Owner _ -> Declared site.definition (reverse site.path) i
  Tag t -> Tagged t i

vecMapIndexed :: forall a b k. (Int -> a -> b) -> Vec k a -> Vec k b
vecMapIndexed f = walk 0
 where
  walk :: forall m. Int -> Vec m a -> Vec m b
  walk _ VNil = VNil
  walk i (VCons x xs) = VCons (f i x) (walk (i + 1) xs)

tshow :: (Show a) => a -> Text
tshow = T.pack . show

lookupEnv :: Fin n -> Env n -> Thunk
lookupEnv i env = case (i, env) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupEnv j xs

-- | Apply a function value to an argument thunk.
apply :: Config -> Runtime -> Value -> Thunk -> Thunk
apply cfg rt f arg = case f of
  VClosure (Closure site env body) -> eval cfg rt site (VCons arg env) body
  _ -> Left (Internal "application of a non-function")

arith :: Either ArithError a -> Either EvalError a
arith = either (Left . convert) Right
 where
  convert = \case
    Eval.Affine.DivideByZero -> Eval.Eval.DivideByZero
    Eval.Affine.Domain msg -> Eval.Eval.Domain msg
    Eval.Affine.Undecided msg -> Eval.Eval.Undecided msg

-- Values ---------------------------------------------------------------------------

num :: Dim -> Maybe UnitHint -> Magnitude -> Value
num d hint r = VTensor [] d hint (V.singleton (Right r))

tensor :: Value -> Either EvalError ([Int], Dim, Maybe UnitHint, Vector Elem)
tensor = \case
  VTensor dims d hint buf -> Right (dims, d, hint, buf)
  _ -> Left (Internal "expected a tensor")

-- | The one element of a rank-zero tensor.
scalar :: Value -> Either EvalError Magnitude
scalar v = (\(x, _, _) -> x) <$> scalarFull v

scalarFull :: Value -> Either EvalError (Magnitude, Dim, Maybe UnitHint)
scalarFull = \case
  VTensor [] d hint buf | V.length buf == 1 -> (\x -> (x, d, hint)) <$> V.head buf
  _ -> Left (Internal "expected a number")

bool :: Value -> Either EvalError Bool
bool = \case
  VBool b -> Right b
  _ -> Left (Internal "expected a boolean")

{- | Make a scalar value its own display unit. Forces its magnitude, which
for a unit definition is a constant.
-}
asUnit :: UnitAtom -> Value -> Thunk
asUnit atom = \case
  VTensor [] d _ buf | V.length buf == 1 -> do
    x <- V.head buf
    Right (VTensor [] d (Just (UnitHint [UnitFactor atom 1 d x] x d)) buf)
  v -> Right v

-- Display units ----------------------------------------------------------------------

{- | A hint from its atoms: powers of zero go, units of one dimension that
appear with opposite signs cancel ( rad^-1@ is a number,  m^-1@ is
1000, ^2 m^-1@ is @), and the total factor and dimension are
recomputed from what is left. Nothing when a factor cannot be raised to its
power, which drops the hint.
-}
mkHint :: Precision -> [UnitFactor] -> Maybe UnitHint
mkHint p factors = do
  let kept = filter ((/= 0) . (.power)) (cancel factors)
  total <-
    foldM
      ( \acc u ->
          either
            (const Nothing)
            (Just . mulM p acc)
            (powM p u.unitFactor (fromIntegral u.power))
      )
      (Exact 1)
      kept
  pure
    ( UnitHint
        kept
        total
        (foldr (dimMul . (\u -> dimPow u.power u.unitDim)) dimOne kept)
    )
 where
  -- Within a dimension, mixed signs collapse onto the first-written unit
  -- with the net power.
  cancel us = concatMap reduce (groupOn (.unitDim) us)
  reduce group@(u : _)
    | any ((> 0) . (.power)) group && any ((< 0) . (.power)) group =
        [u{power = sum (map (.power) group)}]
  reduce group = group
  groupOn key xs = [[x | x <- xs, key x == k] | k <- nub (map key xs)]

hintMul :: Precision -> UnitHint -> UnitHint -> Maybe UnitHint
hintMul p a b = mkHint p (foldl merge a.atoms b.atoms)
 where
  merge acc u
    | any ((== u.atom) . (.atom)) acc =
        [if x.atom == u.atom then x{power = x.power + u.power} else x | x <- acc]
    | otherwise = acc ++ [u]

hintInv :: Precision -> UnitHint -> Maybe UnitHint
hintInv p a = mkHint p [u{power = negate u.power} | u <- a.atoms]

hintPow :: Precision -> Int -> UnitHint -> Maybe UnitHint
hintPow p k a = mkHint p [u{power = u.power * k} | u <- a.atoms]

{- | The display unit of a product or quotient of two values: combine when
both have one, keep the one that exists otherwise.
-}
combine ::
  (UnitHint -> UnitHint -> Maybe UnitHint) ->
  Maybe UnitHint ->
  Maybe UnitHint ->
  Maybe UnitHint
combine f (Just a) (Just b) = f a b
combine _ (Just a) Nothing = Just a
combine _ Nothing (Just b) = Just b
combine _ Nothing Nothing = Nothing

-- Primitives -------------------------------------------------------------------------

{- | Run a saturated primitive. Arguments are in source order and are forced
only as the primitive needs them; elementwise operations stay lazy per
element. Dimensions follow the rules of design §4.3, display units those
of §3.2.12, magnitudes those of §3.2.
-}
runPrim :: Config -> Runtime -> Text -> [Thunk] -> Thunk
runPrim cfg rt prim args = case (prim, args) of
  (unit, [])
    | Just b <- baseUnit unit ->
        Right
          ( num
              (dimBase b)
              ( Just
                  ( UnitHint
                      [UnitFactor (UnitBase unit) 1 (dimBase b) (Exact 1)]
                      (Exact 1)
                      (dimBase b)
                  )
              )
              (Exact 1)
          )
  -- Sum: the left operand's display unit wins.
  ("add", [a, b]) -> elementwise2 (pureOp addM) const (combine (\x _ -> Just x)) a b
  ("sub", [a, b]) -> elementwise2 (pureOp subM) const (combine (\x _ -> Just x)) a b
  ("neg", [a]) -> elementwise1 negM a
  ("abs", [a]) -> elementwise1 (absM p) a
  ("emul", [a, b]) -> elementwise2 (pureOp (mulM p)) dimMul (combine (hintMul p)) a b
  ("ediv", [a, b]) ->
    elementwise2
      (\x y -> arith (divM p x y))
      dimDiv
      (\h1 h2 -> combine (hintMul p) h1 (hintInv p =<< h2))
      a
      b
  -- Tensor product: ranks add, dimensions multiply, every pair of elements
  -- multiplied.
  ("outer", [a, b]) -> do
    (d1, dim1, h1, xs) <- tensor =<< a
    (d2, dim2, h2, ys) <- tensor =<< b
    Right
      ( VTensor
          (d1 ++ d2)
          (dimMul dim1 dim2)
          (combine (hintMul p) h1 h2)
          (V.concatMap (\x -> V.map (\y -> mulM p <$> x <*> y) ys) xs)
      )
  -- Contracting product: the left operand's last index against the right
  -- operand's first.
  ("dot", [a, b]) -> do
    (dl, dim1, h1, xs) <- tensor =<< a
    (dr, dim2, h2, ys) <- tensor =<< b
    case (reverse dl, dr) of
      (n : d1rev, n' : d2)
        | n == n' ->
            let d1 = reverse d1rev
                stride2 = product d2
                rows = product d1
                element k =
                  let (i, j) = k `divMod` stride2
                   in sumM
                        <$> sequence
                          [ mulM p <$> (xs V.! (i * n + c)) <*> (ys V.! (c * stride2 + j))
                          | c <- [0 .. n - 1]
                          ]
             in Right
                  ( VTensor
                      (d1 ++ d2)
                      (dimMul dim1 dim2)
                      (combine (hintMul p) h1 h2)
                      (V.generate (rows * stride2) element)
                  )
      _ -> Left (Internal "dot: operand shapes do not contract")
  ("div", [a, b]) -> do
    (dims, d1, h1, xs) <- tensor =<< a
    (k, d2, h2) <- scalarFull =<< b
    Right
      ( VTensor
          dims
          (dimDiv d1 d2)
          (combine (hintMul p) h1 (hintInv p =<< h2))
          (V.map (\x -> x >>= \x' -> arith (divM p x' k)) xs)
      )
  ("eq", [a, b]) -> VBool <$> equal a b
  ("ne", [a, b]) -> VBool . not <$> equal a b
  ("lt", [a, b]) -> compareWith (== LT) a b
  ("le", [a, b]) -> compareWith (/= GT) a b
  ("gt", [a, b]) -> compareWith (== GT) a b
  ("ge", [a, b]) -> compareWith (/= LT) a b
  -- Lazy in the second argument.
  ("and", [a, b]) -> do
    x <- bool =<< a
    if x then VBool <$> (bool =<< b) else Right (VBool False)
  ("or", [a, b]) -> do
    x <- bool =<< a
    if x then Right (VBool True) else VBool <$> (bool =<< b)
  ("not", [a]) -> VBool . not <$> (bool =<< a)
  ("floor", [a]) -> dimensionless (arith . floorM) a
  ("ceil", [a]) -> dimensionless (arith . ceilM) a
  ("round", [a]) -> dimensionless (arith . roundM) a
  -- Elementary functions (design §3.2.2). Their arguments are dimensionless
  -- by type, except sqrt, which halves the dimension.
  ("sqrt", [a]) -> do
    (x, d, _) <- scalarFull =<< a
    r <- arith (sqrtM p x)
    d2 <-
      maybe
        (Left (Internal "sqrt of a dimension that is not a square"))
        Right
        (dimRoot 2 d)
    Right (num d2 Nothing r)
  ("exp", [a]) -> dimensionless (Right . expM p) a
  ("log", [a]) -> dimensionless (arith . logM p) a
  ("sin", [a]) -> dimensionless (Right . sinM p) a
  ("cos", [a]) -> dimensionless (Right . cosM p) a
  ("tan", [a]) -> dimensionless (arith . tanM p) a
  ("asin", [a]) -> angle (arith . asinM p) a
  ("acos", [a]) -> angle (arith . acosM p) a
  ("atan", [a]) -> angle (Right . atanM p) a
  ("sinh", [a]) -> dimensionless (Right . sinhM p) a
  ("cosh", [a]) -> dimensionless (Right . coshM p) a
  ("tanh", [a]) -> dimensionless (arith . tanhM p) a
  ("atan2", [a, b]) -> do
    y <- scalar =<< a
    x <- scalar =<< b
    num (dimBase Ang) Nothing <$> arith (atan2M p y x)
  ("pi", []) -> Right (num dimOne Nothing (piM p))
  -- Euclidean norm of a vector.
  ("norm", [a]) -> do
    (_, d, _, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    r <- arith (sqrtM p (sumM [mulM p x x | x <- xs]))
    Right (num d Nothing r)
  ("det", [a]) -> do
    (dims, _, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        num dimOne Nothing <$> arith (determinant p n rows)
      _ -> Left (Internal "det of a non-square matrix")
  ("inverse", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        inv <- arith (invert p n rows)
        Right (VTensor [n, n] (dimInv d) Nothing (V.fromList (map Right (concat inv))))
      _ -> Left (Internal "inverse of a non-square matrix")
  -- Wedge product: the antisymmetrised outer product, (a ∧ b)ⱼₖ = aⱼbₖ − aₖbⱼ,
  -- stored as an ordinary matrix. Entries are thunks, so a consumer that
  -- reads three of the nine (the 3D Hodge star) computes only those.
  ("wedge", [a, b]) -> do
    (da, dim1, h1, xs) <- tensor =<< a
    (_, dim2, h2, ys) <- tensor =<< b
    case da of
      [n] ->
        Right
          ( VTensor
              [n, n]
              (dimMul dim1 dim2)
              (combine (hintMul p) h1 h2)
              ( V.generate
                  (n * n)
                  ( \k ->
                      let (j, i) = k `divMod` n
                       in (\x y x' y' -> subM (mulM p x y) (mulM p x' y'))
                            <$> (xs V.! j)
                            <*> (ys V.! i)
                            <*> (xs V.! i)
                            <*> (ys V.! j)
                  )
              )
          )
      _ -> Left (Internal "wedge of non-vectors")
  -- 3D Hodge star of a bivector: (⋆M) = (M₁₂, M₂₀, M₀₁).
  ("star", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    case dims of
      [3, 3] -> Right (VTensor [3] d hint (V.fromList [buf V.! 5, buf V.! 6, buf V.! 1]))
      _ -> Left (Internal "star of a non-3x3 matrix")
  ("transpose", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    case dims of
      [r, c] ->
        Right
          ( VTensor
              [c, r]
              d
              hint
              (V.generate (r * c) (\k -> let (j, i) = k `divMod` r in buf V.! (i * c + j)))
          )
      _ -> Left (Internal "transpose of a non-matrix")
  ("vmap", [f, a]) -> do
    fv <- f
    (dims, d, _, buf) <- tensor =<< a
    let results =
          V.map (\x -> apply cfg rt fv (Right (VTensor [] d Nothing (V.singleton x)))) buf
    -- The result dimension is a property of the function; read it off the
    -- first element, or keep the input's for an empty tensor.
    outDim <-
      if V.null results
        then Right d
        else (\(_, d', _) -> d') <$> (scalarFull =<< V.head results)
    Right (VTensor dims outDim Nothing (V.map (>>= scalar) results))
  -- Conversion: the value, displayed in the unit's terms. A unit expression
  -- without a display unit of its own (a bare number) clears the hint.
  ("to", [a, u]) -> do
    (dims, d, _, buf) <- tensor =<< a
    (_, _, uh) <- scalarFull =<< u
    Right (VTensor dims d uh buf)
  _
    | primArity prim == Just (length args) ->
        Left (Unsupported (prim <> ": not implemented yet"))
    | otherwise ->
        Left
          ( Internal
              ( "primitive "
                  <> prim
                  <> " is unknown or applied to the wrong number of arguments"
              )
          )
 where
  p = precisionOf cfg
  pureOp op x y = Right (op x y)
  elementwise1 op a = do
    (dims, d, hint, buf) <- tensor =<< a
    Right (VTensor dims d hint (V.map (fmap op) buf))
  elementwise2 op dimOp hintOp a b = do
    (dims, d1, h1, xs) <- tensor =<< a
    (_, d2, h2, ys) <- tensor =<< b
    Right
      ( VTensor
          dims
          (dimOp d1 d2)
          (hintOp h1 h2)
          (V.zipWith (\x y -> do x' <- x; y' <- y; op x' y') xs ys)
      )
  -- A scalar function whose result is a bare dimensionless number.
  dimensionless f a = do
    x <- scalar =<< a
    num dimOne Nothing <$> f x
  -- A scalar function whose result is an angle in radians.
  angle f a = do
    x <- scalar =<< a
    num (dimBase Ang) Nothing <$> f x
  compareWith decide a b = do
    x <- scalar =<< a
    y <- scalar =<< b
    VBool . decide <$> arith (compareM cfg.sigma p x y)
  -- Tensors of one shape (lint agrees) or two booleans: the equality
  -- instances of design §4.2. Tensors are equal when every component is
  -- decided equal (design §3.2.9).
  equal a b = do
    x <- a
    y <- b
    case (x, y) of
      (VTensor _ _ _ xs, VTensor _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        and <$> mapM (\(u, v) -> arith (equalM cfg.sigma p u v)) (zip xs' ys')
      (VBool m, VBool n) -> Right (m == n)
      _ -> Left (Internal "==: operands are not both tensors or both booleans")
  matrixRows n buf = do
    xs <- sequence (V.toList buf)
    pure (chunks n xs)
  chunks n xs
    | null xs = []
    | otherwise = let (r, rest) = splitAt n xs in r : chunks n rest

sumM :: [Magnitude] -> Magnitude
sumM = foldl' addM (Exact 0)

-- Linear algebra ----------------------------------------------------------------------

{- | A usable pivot: the entry of largest midpoint among those whose
enclosure excludes zero, by row position.
-}
pivotIn :: Int -> [Magnitude] -> Maybe Int
pivotIn from column =
  case [(abs (midpoint x), i) | (i, x) <- zip [0 ..] column, i >= from, excludesZero x] of
    [] -> Nothing
    cands -> Just (snd (maximum cands))
 where
  excludesZero x = midpoint x - radius x > 0 || midpoint x + radius x < 0

singular :: Text -> [Magnitude] -> ArithError
singular what column
  | all (== Exact 0) column = Eval.Affine.Domain (what <> " of a singular matrix")
  | otherwise =
      Eval.Affine.Undecided (what <> " of a matrix whose enclosure may be singular")

-- | Determinant by Gaussian elimination with partial pivoting on midpoints.
determinant :: Precision -> Int -> [[Magnitude]] -> Either ArithError Magnitude
determinant p n = go 0 (Exact 1)
 where
  go k acc rows
    | k == n = Right acc
    | otherwise =
        let column = map (!! k) rows
         in case pivotIn 0 column of
              Nothing
                | all (== Exact 0) column -> Right (Exact 0)
                | otherwise -> Left (singular "det" column)
              Just i -> do
                let pivotRow = rows !! i
                    others = [r | (j, r) <- zip [0 ..] rows, j /= i]
                    pv = pivotRow !! k
                    -- Moving row i to the front is i transpositions.
                    sign = if even i then 1 else -1
                reduced <- mapM (eliminate k pivotRow pv) others
                go (k + 1) (scaleM sign (mulM p acc pv)) reduced
  eliminate k pivotRow pv r = do
    f <- divM p (r !! k) pv
    pure (zipWith (\a b -> subM a (mulM p f b)) r pivotRow)

-- | Inverse by Gauss-Jordan elimination on the augmented matrix.
invert :: Precision -> Int -> [[Magnitude]] -> Either ArithError [[Magnitude]]
invert p n rows0 =
  go
    0
    [ r ++ [if i == j then Exact 1 else Exact 0 | j <- [0 .. n - 1]]
    | (i, r) <- zip [0 ..] rows0
    ]
 where
  go k rows
    | k == n = Right (map (drop n) rows)
    | otherwise =
        let column = map (!! k) rows
         in case pivotIn k column of
              Nothing -> Left (singular "inverse" (drop k column))
              Just i -> do
                let swapped = [rows !! swap j | j <- [0 .. n - 1]]
                    swap j
                      | j == k = i
                      | j == i = k
                      | otherwise = j
                    pivotRow = swapped !! k
                    pv = pivotRow !! k
                normalised <- mapM (\x -> divM p x pv) pivotRow
                let eliminate r = let f = r !! k in zipWith (\a b -> subM a (mulM p f b)) r normalised
                go
                  (k + 1)
                  [if j == k then normalised else eliminate r | (j, r) <- zip [0 ..] swapped]

{- | A plain rendering for tests. Forces every element. Exact magnitudes
print as @n/d@ in base units, affine ones as an approximate @mid±r@, and
dimensions are omitted; decimal output with units is "Eval.Pretty"'s job.
-}
render :: Value -> Either EvalError Text
render = \case
  VTensor dims _ _ buf -> do
    rs <- sequence (V.toList buf)
    pure (nested dims rs)
  VBool True -> Right "true"
  VBool False -> Right "false"
  VClosure _ -> Right "<function>"
 where
  magnitude = \case
    Exact r -> frac r
    m ->
      let c = collapse m
       in tshow (fromRational c.mid :: Double)
            <> "±"
            <> tshow (fromRational (c.bound + sigmaOf 6 c) :: Double)
  frac r
    | denominator r == 1 = tshow (numerator r)
    | otherwise = tshow (numerator r) <> "/" <> tshow (denominator r)
  nested dims rs = case dims of
    [] -> maybe "[]" magnitude (headMay rs)
    [_] -> brackets (map magnitude rs)
    d : rest ->
      let stride = product rest
       in brackets [nested rest (take stride (drop (i * stride) rs)) | i <- [0 .. d - 1]]
  brackets xs = "[" <> T.intercalate ", " xs <> "]"
  headMay = \case
    x : _ -> Just x
    [] -> Nothing
