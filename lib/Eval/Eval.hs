-- | A direct, environment-passing, call-by-need evaluator over Typed Core
-- (design §8). Type abstractions and applications are erased. Because terms
-- have been inferred and linted, the remaining type-error cases are
-- unreachable; they exist to keep the pattern matches total and are reported
-- as internal errors.
--
-- Tensors are one runtime shape: a flat row-major buffer of element thunks
-- beside the list of lengths and a dimension vector. A number is the
-- rank-zero case with a buffer of one. Projection is a slice, elementwise
-- arithmetic is a zip over the buffer, and laziness per component comes
-- from the element thunks. The dimension vector exists only for printing:
-- types are checked before evaluation.
module Eval.Eval
  ( Value (..)
  , Closure (..)
  , Elem
  , Thunk
  , EvalError (..)
  , Config (..)
  , defaultConfig
  , Lookup
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

-- | How the evaluator finds the Typed Core behind a 'TRef'. The codebase
-- supplies this; tests supply a map.
type Lookup = Hash -> Maybe (TTerm Z)

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

data Value
  = -- | lengths, dimension, flat row-major elements in SI base units
    VTensor [Int] Dim (Vector Elem)
  | VBool Bool
  | VClosure Closure

-- | A function value: a body under one binder, closed over its environment.
data Closure = forall n. Closure (Env n) (TTerm (S n))

-- | Evaluate a closed term.
evalClosed :: Config -> Lookup -> TTerm Z -> Thunk
evalClosed cfg look = eval cfg look VNil

eval :: Config -> Lookup -> Env n -> TTerm n -> Thunk
eval cfg look = go
  where
    go :: Env m -> TTerm m -> Thunk
    go env = \case
      TVr i -> lookupEnv i env
      TRef h mi -> case look h of
        Nothing -> Left (UnknownRef h)
        Just t -> case mi of
          Nothing -> go VNil t
          Just i -> case t of
            TCycle _ _ bodies -> case vecIndex i (cycleMembers VNil bodies) of
              Just member -> member
              Nothing -> Left (BadCycleIndex i)
            _ -> Left (BadCycleIndex i)
      TPrimApp p _ args -> runPrim cfg look p (map (go env) args)
      TLit (LTensor dims rs) -> Right (VTensor dims dimOne (V.fromList (map Right rs)))
      TLit (LBool b) -> Right (VBool b)
      TLam _ _ body -> Right (VClosure (Closure env body))
      TApp f a -> do
        fv <- go env f
        apply cfg look fv (go env a)
      TLet _ _ e body -> go (VCons (go env e) env) body
      TIf c t e -> do
        cv <- go env c
        case cv of
          VBool True -> go env t
          VBool False -> go env e
          _ -> Left (Internal "if: condition is not a boolean")
      TPow t n -> do
        (x, d) <- scalarWithDim =<< go env t
        if x == 0 && n < 0
          then Left DivideByZero
          else Right (VTensor [] (dimPow (fromIntegral n) d) (V.singleton (Right (x ^^ n))))
      TNoise _ _ -> Left (Unsupported "noise: affine arithmetic is not implemented yet")
      TUncertain {} -> Left (Unsupported "±: affine arithmetic is not implemented yet")
      -- Stack the component buffers; the shapes agree by lint. A component
      -- that fails to evaluate becomes a block of failing elements of the
      -- shape the other components have, so an error in one component is
      -- only raised when that component is used.
      TPack ts ->
        let results = map (tensor <=< go env) ts
            known = [(dims, d) | Right (dims, d, _) <- results]
         in case (results, known) of
              ([], _) -> Right (VTensor [0] dimOne V.empty)
              (_, (dims, d) : _) ->
                let block = \case
                      Right (_, _, buf) -> buf
                      Left err -> V.replicate (product dims) (Left err)
                 in Right (VTensor (length results : dims) d (V.concat (map block results)))
              (Left err : _, []) -> Left err
              (Right _ : _, []) -> Left (Internal "unreachable: a tensor with no shape")
      -- Slice out component i: a view, not a copy.
      TProj t i -> do
        (dims, d, buf) <- tensor =<< go env t
        case dims of
          k : rest
            | i < k ->
                let stride = product rest
                 in Right (VTensor rest d (V.slice (i * stride) stride buf))
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
apply :: Config -> Lookup -> Value -> Thunk -> Thunk
apply cfg look f arg = case f of
  VClosure (Closure env body) -> eval cfg look (VCons arg env) body
  _ -> Left (Internal "application of a non-function")

-- Values ---------------------------------------------------------------------------

num :: Dim -> Rational -> Value
num d r = VTensor [] d (V.singleton (Right r))

tensor :: Value -> Either EvalError ([Int], Dim, Vector Elem)
tensor = \case
  VTensor dims d buf -> Right (dims, d, buf)
  _ -> Left (Internal "expected a tensor")

-- | The one element of a rank-zero tensor.
scalar :: Value -> Either EvalError Rational
scalar v = fst <$> scalarWithDim v

scalarWithDim :: Value -> Either EvalError (Rational, Dim)
scalarWithDim = \case
  VTensor [] d buf | V.length buf == 1 -> (,d) <$> V.head buf
  _ -> Left (Internal "expected a number")

bool :: Value -> Either EvalError Bool
bool = \case
  VBool b -> Right b
  _ -> Left (Internal "expected a boolean")

-- Primitives -------------------------------------------------------------------------

-- | Run a saturated primitive. Arguments are in source order and are forced
-- only as the primitive needs them; elementwise operations stay lazy per
-- element. Dimensions follow the rules of design §4.3.
runPrim :: Config -> Lookup -> Text -> [Thunk] -> Thunk
runPrim cfg look p args = case (p, args) of
  (unit, []) | Just b <- baseUnit unit -> Right (num (dimBase b) 1)
  ("add", [a, b]) -> elementwise2 (+) const a b
  ("sub", [a, b]) -> elementwise2 (-) const a b
  ("neg", [a]) -> elementwise1 negate a
  ("abs", [a]) -> elementwise1 abs a
  ("emul", [a, b]) -> elementwise2 (*) dimMul a b
  ("ediv", [a, b]) -> do
    (dims, d1, xs) <- tensor =<< a
    (_, d2, ys) <- tensor =<< b
    Right (VTensor dims (dimDiv d1 d2) (V.zipWith (\x y -> x >>= \x' -> y >>= divide x') xs ys))
  -- Tensor product: ranks add, dimensions multiply, every pair of elements
  -- multiplied.
  ("outer", [a, b]) -> do
    (d1, dim1, xs) <- tensor =<< a
    (d2, dim2, ys) <- tensor =<< b
    Right (VTensor (d1 ++ d2) (dimMul dim1 dim2) (V.concatMap (\x -> V.map (\y -> (*) <$> x <*> y) ys) xs))
  -- Contracting product: the left operand's last index against the right
  -- operand's first.
  ("dot", [a, b]) -> do
    (dl, dim1, xs) <- tensor =<< a
    (dr, dim2, ys) <- tensor =<< b
    case (reverse dl, dr) of
      (n : d1rev, n' : d2) | n == n' ->
        let d1 = reverse d1rev
            stride2 = product d2
            rows = product d1
            element k =
              let (i, j) = k `divMod` stride2
               in sum <$> sequence [(*) <$> (xs V.! (i * n + c)) <*> (ys V.! (c * stride2 + j)) | c <- [0 .. n - 1]]
         in Right (VTensor (d1 ++ d2) (dimMul dim1 dim2) (V.generate (rows * stride2) element))
      _ -> Left (Internal "dot: operand shapes do not contract")
  ("div", [a, b]) -> do
    (dims, d1, xs) <- tensor =<< a
    (k, d2) <- scalarWithDim =<< b
    Right (VTensor dims (dimDiv d1 d2) (V.map (\x -> x >>= (`divide` k)) xs))
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
  ("floor", [a]) -> num dimOne . fromInteger . floor <$> (scalar =<< a)
  ("ceil", [a]) -> num dimOne . fromInteger . ceiling <$> (scalar =<< a)
  ("round", [a]) -> num dimOne . fromInteger . round <$> (scalar =<< a)
  ("cross", [a, b]) -> do
    (_, dim1, xs) <- tensor =<< a
    (_, dim2, ys) <- tensor =<< b
    xs' <- sequence (V.toList xs)
    ys' <- sequence (V.toList ys)
    case (xs', ys') of
      ([x0, x1, x2], [y0, y1, y2]) ->
        Right (VTensor [3] (dimMul dim1 dim2) (V.fromList (map Right [x1 * y2 - x2 * y1, x2 * y0 - x0 * y2, x0 * y1 - x1 * y0])))
      _ -> Left (Internal "cross of non-3-vectors")
  ("transpose", [a]) -> do
    (dims, d, buf) <- tensor =<< a
    case dims of
      [r, c] -> Right (VTensor [c, r] d (V.generate (r * c) (\k -> let (j, i) = k `divMod` r in buf V.! (i * c + j))))
      _ -> Left (Internal "transpose of a non-matrix")
  ("vmap", [f, a]) -> do
    fv <- f
    (dims, d, buf) <- tensor =<< a
    let results = V.map (\x -> apply cfg look fv (Right (VTensor [] d (V.singleton x)))) buf
    -- The result dimension is a property of the function; read it off the
    -- first element, or keep the input's for an empty tensor.
    outDim <-
      if V.null results
        then Right d
        else snd <$> (scalarWithDim =<< V.head results)
    Right (VTensor dims outDim (V.map (>>= scalar) results))
  -- Conversion keeps the value; display units arrive with the prelude.
  ("to", [a, _]) -> a
  _
    | primArity p == Just (length args) -> Left (Unsupported (p <> ": not implemented yet"))
    | otherwise -> Left (Internal ("primitive " <> p <> " is unknown or applied to the wrong number of arguments"))
  where
    elementwise1 op a = do
      (dims, d, buf) <- tensor =<< a
      Right (VTensor dims d (V.map (fmap op) buf))
    elementwise2 op dimOp a b = do
      (dims, d1, xs) <- tensor =<< a
      (_, d2, ys) <- tensor =<< b
      Right (VTensor dims (dimOp d1 d2) (V.zipWith (\x y -> op <$> x <*> y) xs ys))
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
        (VTensor _ _ xs, VTensor _ _ ys) -> do
          xs' <- sequence (V.toList xs)
          ys' <- sequence (V.toList ys)
          Right (xs' == ys')
        (VBool m, VBool n) -> Right (m == n)
        _ -> Left (Internal "==: operands are not both tensors or both booleans")

-- | A plain rendering for tests. Forces every element. Rationals print as
-- @n/d@ and dimensions are omitted; decimal output with units is
-- "Eval.Pretty"'s job.
render :: Value -> Either EvalError Text
render = \case
  VTensor dims _ buf -> do
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
