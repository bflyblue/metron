-- | A direct, environment-passing, call-by-need evaluator over Typed Core
-- (design §8). Type abstractions and applications are erased. Because terms
-- have been inferred and linted, the remaining type-error cases are
-- unreachable; they exist to keep the pattern matches total and are reported
-- as internal errors.
--
-- Tensors are one runtime shape: a flat row-major buffer of element thunks
-- beside the list of lengths, a dimension vector, and an optional display
-- unit (design §3.2.12). A number is the rank-zero case with a buffer of
-- one. Magnitudes are always in SI base units; the display unit says how to
-- print them. The dimension vector and the display unit exist only for
-- printing: types are checked before evaluation.
module Eval.Eval
  ( Value (..)
  , Closure (..)
  , Elem
  , Thunk
  , EvalError (..)
  , Config (..)
  , defaultConfig
  , Runtime (..)
  , UnitAtom (..)
  , UnitHint (..)
  , eval
  , evalClosed
  , apply
  , scalar
  , render
  ) where

import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Eval.Core
import Eval.Dimension
import Eval.TCore

-- | Evaluation parameters. Nothing uses 'scale' yet; it is threaded now so
-- that affine arithmetic (design §3.2.8) slots in without a signature change.
data Config = Config
  { scale :: Int
  }
  deriving stock (Show)

defaultConfig :: Config
defaultConfig = Config {scale = 20}

-- | What the evaluator needs from the codebase: the Typed Core behind a
-- reference, and whether a reference was declared a display unit.
data Runtime = Runtime
  { typedOf :: Hash -> Maybe (TTerm Z)
  , isUnit :: Hash -> Maybe Int -> Bool
  }

data EvalError
  = DivideByZero
  | UnknownRef Hash
  | BadCycleIndex Int
  | Unsupported Text
  -- | Unreachable for linted terms.
  | Internal Text
  deriving stock (Eq, Show)

type Thunk = Either EvalError Value

-- | A tensor element, lazily.
type Elem = Either EvalError Rational

-- | The environment for a term in scope @n@.
type Env n = Vec n Thunk

-- | A factor of a display unit: a declared unit by reference, or a base unit.
data UnitAtom
  = UnitRef Hash (Maybe Int)
  | UnitBase Text
  deriving stock (Eq, Ord, Show)

-- | How to print a value: the unit atoms with exponents, the unit's
-- magnitude in base units, and its dimension (which must match the value's
-- for the hint to be used).
data UnitHint = UnitHint
  { atoms :: [(UnitAtom, Int)] -- ^ in order of first appearance, so @V A@ prints as written
  , factor :: Rational
  , dim :: Dim
  }
  deriving stock (Eq, Show)

data Value
  = -- | lengths, dimension, display unit, flat row-major elements in SI base units
    VTensor [Int] Dim (Maybe UnitHint) (Vector Elem)
  | VBool Bool
  | VClosure Closure

-- | A function value: a body under one binder, closed over its environment.
data Closure = forall n. Closure (Env n) (TTerm (S n))

-- | Evaluate a closed term.
evalClosed :: Config -> Runtime -> TTerm Z -> Thunk
evalClosed cfg rt = eval cfg rt VNil

eval :: Config -> Runtime -> Env n -> TTerm n -> Thunk
eval cfg rt = go
  where
    go :: Env m -> TTerm m -> Thunk
    go env = \case
      TVr i -> lookupEnv i env
      TRef h mi -> case rt.typedOf h of
        Nothing -> Left (UnknownRef h)
        Just t -> do
          v <- case mi of
            Nothing -> go VNil t
            Just i -> case t of
              TCycle _ _ bodies -> case vecIndex i (cycleMembers VNil bodies) of
                Just member -> member
                Nothing -> Left (BadCycleIndex i)
              _ -> Left (BadCycleIndex i)
          -- A declared unit is its own display unit (design §3.2.12).
          if rt.isUnit h mi then asUnit (UnitRef h mi) v else Right v
      TPrimApp p _ args -> runPrim cfg rt p (map (go env) args)
      TLit (LTensor dims rs) -> Right (VTensor dims dimOne Nothing (V.fromList (map Right rs)))
      TLit (LBool b) -> Right (VBool b)
      TLam _ _ body -> Right (VClosure (Closure env body))
      TApp f a -> do
        fv <- go env f
        apply cfg rt fv (go env a)
      TLet _ _ e body -> go (VCons (go env e) env) body
      TIf c t e -> do
        cv <- go env c
        case cv of
          VBool True -> go env t
          VBool False -> go env e
          _ -> Left (Internal "if: condition is not a boolean")
      TPow t n -> do
        (x, d, hint) <- scalarFull =<< go env t
        if x == 0 && n < 0
          then Left DivideByZero
          else
            Right
              (VTensor [] (dimPow (fromIntegral n) d) (hintPow (fromIntegral n) <$> hint) (V.singleton (Right (x ^^ n))))
      TNoise _ _ -> Left (Unsupported "noise: affine arithmetic is not implemented yet")
      TUncertain {} -> Left (Unsupported "±: affine arithmetic is not implemented yet")
      -- Stack the component buffers; the shapes agree by lint. A component
      -- that fails to evaluate becomes a block of failing elements of the
      -- shape the other components have, so an error in one component is
      -- only raised when that component is used. The first component's
      -- display unit is kept.
      TPack ts ->
        let results = map (tensor <=< go env) ts
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
        (dims, d, hint, buf) <- tensor =<< go env t
        case dims of
          k : rest
            | i < k ->
                let stride = product rest
                 in Right (VTensor rest d hint (V.slice (i * stride) stride buf))
          _ -> Left (Internal ("projection ." <> tshow i <> " out of range"))
      -- Erasure.
      TTyLam _ _ b -> go env b
      TTyApp b _ -> go env b
      -- A cycle is not itself a value; it is reached through @TRef h (Just i)@.
      TCycle {} -> Left (BadCycleIndex (-1))

    -- Knot-tying: every member is evaluated in an environment that already
    -- contains all the members. 'vecMap' and 'vecAppend' inspect only the
    -- spine, so the recursion is productive.
    cycleMembers :: Env m -> Vec k (TTerm (Plus k m)) -> Vec k Thunk
    cycleMembers env bodies = members
      where
        members = vecMap (go (vecAppend members env)) bodies

(<=<) :: (b -> Either e c) -> (a -> Either e b) -> a -> Either e c
(f <=< g) x = g x >>= f

tshow :: (Show a) => a -> Text
tshow = T.pack . show

lookupEnv :: Fin n -> Env n -> Thunk
lookupEnv i env = case (i, env) of
  (FZ, VCons x _) -> x
  (FS j, VCons _ xs) -> lookupEnv j xs

-- | Apply a function value to an argument thunk.
apply :: Config -> Runtime -> Value -> Thunk -> Thunk
apply cfg rt f arg = case f of
  VClosure (Closure env body) -> eval cfg rt (VCons arg env) body
  _ -> Left (Internal "application of a non-function")

-- Values ---------------------------------------------------------------------------

num :: Dim -> Maybe UnitHint -> Rational -> Value
num d hint r = VTensor [] d hint (V.singleton (Right r))

tensor :: Value -> Either EvalError ([Int], Dim, Maybe UnitHint, Vector Elem)
tensor = \case
  VTensor dims d hint buf -> Right (dims, d, hint, buf)
  _ -> Left (Internal "expected a tensor")

-- | The one element of a rank-zero tensor.
scalar :: Value -> Either EvalError Rational
scalar v = (\(x, _, _) -> x) <$> scalarFull v

scalarFull :: Value -> Either EvalError (Rational, Dim, Maybe UnitHint)
scalarFull = \case
  VTensor [] d hint buf | V.length buf == 1 -> (\x -> (x, d, hint)) <$> V.head buf
  _ -> Left (Internal "expected a number")

bool :: Value -> Either EvalError Bool
bool = \case
  VBool b -> Right b
  _ -> Left (Internal "expected a boolean")

-- | Make a scalar value its own display unit. Forces its magnitude, which
-- for a unit definition is a constant.
asUnit :: UnitAtom -> Value -> Thunk
asUnit atom = \case
  VTensor [] d _ buf | V.length buf == 1 -> do
    x <- V.head buf
    Right (VTensor [] d (Just (UnitHint [(atom, 1)] x d)) buf)
  v -> Right v

-- Display units ----------------------------------------------------------------------

hintMul :: UnitHint -> UnitHint -> UnitHint
hintMul a b = UnitHint (filter ((/= 0) . snd) (foldl merge a.atoms b.atoms)) (a.factor * b.factor) (dimMul a.dim b.dim)
  where
    merge acc (atom, k)
      | any ((== atom) . fst) acc = [(x, if x == atom then j + k else j) | (x, j) <- acc]
      | otherwise = acc ++ [(atom, k)]

hintInv :: UnitHint -> UnitHint
hintInv a = UnitHint [(x, negate k) | (x, k) <- a.atoms] (recip a.factor) (dimInv a.dim)

hintPow :: Int -> UnitHint -> UnitHint
hintPow k a = UnitHint (filter ((/= 0) . snd) [(x, j * k) | (x, j) <- a.atoms]) (a.factor ^^ k) (dimPow k a.dim)

-- | The display unit of a product or quotient of two values: combine when
-- both have one, keep the one that exists otherwise.
combine :: (UnitHint -> UnitHint -> UnitHint) -> Maybe UnitHint -> Maybe UnitHint -> Maybe UnitHint
combine f (Just a) (Just b) = Just (f a b)
combine _ (Just a) Nothing = Just a
combine _ Nothing (Just b) = Just b
combine _ Nothing Nothing = Nothing

-- Primitives -------------------------------------------------------------------------

-- | Run a saturated primitive. Arguments are in source order and are forced
-- only as the primitive needs them; elementwise operations stay lazy per
-- element. Dimensions follow the rules of design §4.3, display units those
-- of §3.2.12.
runPrim :: Config -> Runtime -> Text -> [Thunk] -> Thunk
runPrim cfg rt p args = case (p, args) of
  (unit, []) | Just b <- baseUnit unit -> Right (num (dimBase b) (Just (UnitHint [(UnitBase unit, 1)] 1 (dimBase b))) 1)
  -- Sum: the left operand's display unit wins.
  ("add", [a, b]) -> elementwise2 (+) const (\x y -> combine const x y) a b
  ("sub", [a, b]) -> elementwise2 (-) const (\x y -> combine const x y) a b
  ("neg", [a]) -> elementwise1 negate a
  ("abs", [a]) -> elementwise1 abs a
  ("emul", [a, b]) -> elementwise2 (*) dimMul (combine hintMul) a b
  ("ediv", [a, b]) -> do
    (dims, d1, h1, xs) <- tensor =<< a
    (_, d2, h2, ys) <- tensor =<< b
    Right (VTensor dims (dimDiv d1 d2) (combine hintMul h1 (hintInv <$> h2)) (V.zipWith (\x y -> x >>= \x' -> y >>= divide x') xs ys))
  -- Tensor product: ranks add, dimensions multiply, every pair of elements
  -- multiplied.
  ("outer", [a, b]) -> do
    (d1, dim1, h1, xs) <- tensor =<< a
    (d2, dim2, h2, ys) <- tensor =<< b
    Right (VTensor (d1 ++ d2) (dimMul dim1 dim2) (combine hintMul h1 h2) (V.concatMap (\x -> V.map (\y -> (*) <$> x <*> y) ys) xs))
  -- Contracting product: the left operand's last index against the right
  -- operand's first.
  ("dot", [a, b]) -> do
    (dl, dim1, h1, xs) <- tensor =<< a
    (dr, dim2, h2, ys) <- tensor =<< b
    case (reverse dl, dr) of
      (n : d1rev, n' : d2) | n == n' ->
        let d1 = reverse d1rev
            stride2 = product d2
            rows = product d1
            element k =
              let (i, j) = k `divMod` stride2
               in sum <$> sequence [(*) <$> (xs V.! (i * n + c)) <*> (ys V.! (c * stride2 + j)) | c <- [0 .. n - 1]]
         in Right (VTensor (d1 ++ d2) (dimMul dim1 dim2) (combine hintMul h1 h2) (V.generate (rows * stride2) element))
      _ -> Left (Internal "dot: operand shapes do not contract")
  ("div", [a, b]) -> do
    (dims, d1, h1, xs) <- tensor =<< a
    (k, d2, h2) <- scalarFull =<< b
    Right (VTensor dims (dimDiv d1 d2) (combine hintMul h1 (hintInv <$> h2)) (V.map (\x -> x >>= (`divide` k)) xs))
  ("eq", [a, b]) -> VBool <$> equal a b
  ("ne", [a, b]) -> VBool . not <$> equal a b
  ("lt", [a, b]) -> compareWith (<) a b
  ("le", [a, b]) -> compareWith (<=) a b
  ("gt", [a, b]) -> compareWith (>) a b
  ("ge", [a, b]) -> compareWith (>=) a b
  -- Lazy in the second argument.
  ("and", [a, b]) -> do
    x <- bool =<< a
    if x then VBool <$> (bool =<< b) else Right (VBool False)
  ("or", [a, b]) -> do
    x <- bool =<< a
    if x then Right (VBool True) else VBool <$> (bool =<< b)
  ("not", [a]) -> VBool . not <$> (bool =<< a)
  ("floor", [a]) -> num dimOne Nothing . fromInteger . floor <$> (scalar =<< a)
  ("ceil", [a]) -> num dimOne Nothing . fromInteger . ceiling <$> (scalar =<< a)
  ("round", [a]) -> num dimOne Nothing . fromInteger . round <$> (scalar =<< a)
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
              (combine hintMul h1 h2)
              (V.generate (n * n) (\k -> let (j, i) = k `divMod` n in (\x y x' y' -> x * y - x' * y') <$> (xs V.! j) <*> (ys V.! i) <*> (xs V.! i) <*> (ys V.! j)))
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
      [r, c] -> Right (VTensor [c, r] d hint (V.generate (r * c) (\k -> let (j, i) = k `divMod` r in buf V.! (i * c + j))))
      _ -> Left (Internal "transpose of a non-matrix")
  ("vmap", [f, a]) -> do
    fv <- f
    (dims, d, _, buf) <- tensor =<< a
    let results = V.map (\x -> apply cfg rt fv (Right (VTensor [] d Nothing (V.singleton x)))) buf
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
    | primArity p == Just (length args) -> Left (Unsupported (p <> ": not implemented yet"))
    | otherwise -> Left (Internal ("primitive " <> p <> " is unknown or applied to the wrong number of arguments"))
  where
    elementwise1 op a = do
      (dims, d, hint, buf) <- tensor =<< a
      Right (VTensor dims d hint (V.map (fmap op) buf))
    elementwise2 op dimOp hintOp a b = do
      (dims, d1, h1, xs) <- tensor =<< a
      (_, d2, h2, ys) <- tensor =<< b
      Right (VTensor dims (dimOp d1 d2) (hintOp h1 h2) (V.zipWith (\x y -> op <$> x <*> y) xs ys))
    divide x y = if y == 0 then Left DivideByZero else Right (x / y)
    compareWith op a b = do
      x <- scalar =<< a
      y <- scalar =<< b
      Right (VBool (op x y))
    -- Tensors of one shape (lint agrees) or two booleans: the equality
    -- instances of design §4.2.
    equal a b = do
      x <- a
      y <- b
      case (x, y) of
        (VTensor _ _ _ xs, VTensor _ _ _ ys) -> do
          xs' <- sequence (V.toList xs)
          ys' <- sequence (V.toList ys)
          Right (xs' == ys')
        (VBool m, VBool n) -> Right (m == n)
        _ -> Left (Internal "==: operands are not both tensors or both booleans")

-- | A plain rendering for tests. Forces every element. Rationals print as
-- @n/d@ in base units and dimensions are omitted; decimal output with units
-- is "Eval.Pretty"'s job.
render :: Value -> Either EvalError Text
render = \case
  VTensor dims _ _ buf -> do
    rs <- sequence (V.toList buf)
    pure (nested dims rs)
  VBool True -> Right "true"
  VBool False -> Right "false"
  VClosure _ -> Right "<function>"
  where
    frac r
      | denominator r == 1 = tshow (numerator r)
      | otherwise = tshow (numerator r) <> "/" <> tshow (denominator r)
    nested dims rs = case dims of
      [] -> maybe "[]" frac (headMay rs)
      [_] -> brackets (map frac rs)
      d : rest ->
        let stride = product rest
         in brackets [nested rest (take stride (drop (i * stride) rs)) | i <- [0 .. d - 1]]
    brackets xs = "[" <> T.intercalate ", " xs <> "]"
    headMay = \case
      x : _ -> Just x
      [] -> Nothing
