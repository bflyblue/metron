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
  ScaleHint (..),
  Preferences,
  hintPow,
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
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Eval.Affine hiding (Builtin)
import Eval.Core
import Eval.Dimension
import Eval.TCore
import Eval.Type (conText)

{- | Evaluation parameters: the number of significant digits printed, the
number of standard deviations a comparison must clear to be decided (design
§3.2.9), and whether output uses the unicode spellings.
-}
data Config = Config
  { precision :: Int
  , sigma :: Int
  , unicode :: Bool
  -- ^ print with the unicode spellings of design §2.8 (@:set unicode on@, §7.3)
  }
  deriving stock (Show)

defaultConfig :: Config
defaultConfig = Config{precision = 20, sigma = 3, unicode = False}

-- | Working precision: the scale plus guard digits (design §3.2.8).
precisionOf :: Config -> Precision
precisionOf cfg = cfg.precision + 4

{- | What the evaluator needs from the codebase: the Typed Core behind a
reference, and whether a reference was declared a display unit.
-}
data Runtime = Runtime
  { typedOf :: Hash -> Maybe (TTerm Z)
  , unitName :: Hash -> Maybe Int -> Text -> Maybe Text
  -- ^ given a reference and the name written for it, the unit name it is a unit under, if any (design §3.2.12)
  , scaleName :: Hash -> Maybe Int -> Text -> Maybe Text
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
  = UnitNamed Text
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
  , pinned :: Bool
  -- ^ set by @to@: an explicit choice that a display preference must not override (design §3.2.12)
  }
  deriving stock (Eq, Show)

{- | How a point is written and printed (design §3.6): a step unit, an origin
as an amount from the base origin, and the declared name if any.
-}
data ScaleHint = ScaleHint
  { name :: Maybe UnitAtom
  , step :: Magnitude
  , stepHint :: Maybe UnitHint
  -- ^ the step's own display unit, which differences inherit
  , origin :: Vector Magnitude
  -- ^ the origin as an amount from the base origin, one magnitude per component
  , dims :: [Int]
  , dim :: Dim
  }
  deriving stock (Eq, Show)

data Value
  = -- | lengths, dimension, display unit, flat row-major elements in SI base units
    VTensor [Int] Dim (Maybe UnitHint) (Vector Elem)
  | -- | a point of the affine space over a tensor type: lengths, dimension, the scale it was written on, and its position as an amount from the base origin
    VPoint [Int] Dim (Maybe ScaleHint) (Vector Elem)
  | VScale ScaleHint
  | VBool Bool
  | -- | a constructor other than the booleans, with its fields as thunks (design §8)
    VData ConRef [Thunk]
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
    TRef h mi (Hint written) -> case rt.typedOf h of
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
        case (rt.unitName h mi written, rt.scaleName h mi written) of
          (Just u, _) -> asUnit (UnitNamed u) v
          (_, Just s) -> asScale (UnitNamed s) v
          _ -> Right v
    TPrimApp prim _ args -> runPrim cfg rt prim (zipWith (\i a -> go (child i) env a) [0 ..] args)
    TLit (LTensor (dims, rs)) -> Right (VTensor dims dimOne Nothing (V.fromList (map (Right . Exact) rs)))
    -- Data (design §8): fields stay thunks; a case forces only the scrutinee.
    TCon (Builtin "True") _ [] -> Right (VBool True)
    TCon (Builtin "False") _ [] -> Right (VBool False)
    TCon c _ args -> Right (VData c (zipWith (\i a -> go (child i) env a) [0 ..] args))
    TCase sc _ alts -> do
      v <- go (child 0) env sc
      let (c, fields) = case v of
            VBool True -> (Builtin "True", [])
            VBool False -> (Builtin "False", [])
            VData c' fs -> (c', fs)
            _ -> (Builtin "", [])
      case [(i, alt) | (i, alt@(TAlt c' _ _)) <- zip [1 ..] alts, c' == c] of
        (i, TAlt _ bs body) : _ -> go (child i) (vecAppend (attach bs fields) env) body
        [] -> Left (Internal ("case: no alternative for " <> conText c))
    TLam _ _ body -> Right (VClosure (Closure (child 0) env body))
    TApp f a -> do
      fv <- go (child 0) env f
      apply cfg rt fv (go (child 1) env a)
    TLet _ _ e body -> go (child 1) (VCons (go (child 0) env e) env) body
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
    -- One independent nudge per component, the component index in its
    -- identity (design §3.4); a scalar uncertainty applies to every component.
    TUncertain k l x e -> do
      (dims, d, hint, xs) <- tensor =<< go (child 0) env x
      (edims, _, _, es) <- tensor =<< go (child 1) env e
      case (dims, edims) of
        -- v ±σ P: v + cholesky P · gauss n, one statistical nudge per
        -- component, identified by this site (design §3.5).
        ([n], [en, _]) | en == n -> do
          pRows <- chunksOf n <$> sequence (V.toList es)
          lrows <- arith (choleskyRows (precisionOf cfg) pRows)
          let noise j = unitNoise k (originOf site l j)
              component i =
                ( \vi ->
                    foldl
                      addM
                      vi
                      [mulM (precisionOf cfg) lij (noise j) | (j, lij) <- zip [0 ..] (lrows !! i)]
                )
                  <$> (xs V.! i)
          Right (VTensor dims d hint (V.generate n component))
        _ ->
          let errAt i = if null edims then es V.! 0 else es V.! i
           in Right
                ( VTensor
                    dims
                    d
                    hint
                    (V.imap (\i xm -> uncertain k (originOf site l i) <$> xm <*> errAt i) xs)
                )
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
      v <- go (child 0) env t
      case v of
        VTensor dims d hint buf -> slice dims (\rest -> VTensor rest d hint) buf
        -- A component of a point is a point on the sliced scale (design §3.6).
        VPoint dims d sc buf -> slice dims (\rest -> VPoint rest d (sliceScale <$> sc)) buf
        _ -> Left (Internal "projection from a non-tensor")
     where
      slice :: [Int] -> ([Int] -> Vector a -> Value) -> Vector a -> Thunk
      slice dims mk buf = case dims of
        k : rest
          | i < k ->
              let stride = product rest
               in Right (mk rest (V.slice (i * stride) stride buf))
        _ -> Left (Internal ("projection ." <> tshow i <> " out of range"))
      sliceScale sc = case sc.dims of
        _ : rest ->
          let stride = product rest
           in sc{origin = V.slice (i * stride) stride sc.origin, dims = rest}
        [] -> sc
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

point :: Value -> Either EvalError ([Int], Dim, Maybe ScaleHint, Vector Elem)
point = \case
  VPoint dims d sc buf -> Right (dims, d, sc, buf)
  _ -> Left (Internal "expected a point")

scaleOf :: Value -> Either EvalError ScaleHint
scaleOf = \case
  VScale s -> Right s
  _ -> Left (Internal "expected a scale")

-- | A number or a point: what the comparisons order.
ordered :: Value -> Either EvalError Magnitude
ordered = \case
  VPoint [] _ _ buf | V.length buf == 1 -> V.head buf
  v -> scalar v

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
    Right (VTensor [] d (Just (UnitHint [UnitFactor atom 1 d x] x d False)) buf)
  v -> Right v

-- | Name a scale value after the definition it came from.
asScale :: UnitAtom -> Value -> Thunk
asScale atom = \case
  VScale s -> Right (VScale s{name = Just atom})
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
        False
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

{- | The unit a sum prints in: the smaller of its operands', so that a + b and
b + a print alike (design §3.2.12); the left one when they are equal.
-}
smallerUnit :: UnitHint -> UnitHint -> Maybe UnitHint
smallerUnit a b = Just (if midpoint b.factor < midpoint a.factor then b else a)

{- | Display preferences (design §3.2.12): a unit per exact dimension, used
for a value whose own unit was not chosen with @to@.
-}
type Preferences = Map Dim UnitHint

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
                      False
                  )
              )
              (Exact 1)
          )
  -- Sum: the left operand's display unit wins.
  ("add", [a, b]) -> elementwise2 (pureOp addM) const (combine smallerUnit) a b
  ("sub", [a, b]) -> elementwise2 (pureOp subM) const (combine smallerUnit) a b
  ("neg", [a]) -> elementwise1 negM a
  ("abs", [a]) -> elementwise1 (absM p) a
  -- The parts of an enclosure as the printer collapses it (design §3.2.9,
  -- §3.2.10), each exact but sd: the midpoint, the bound radius
  -- Σ_bound |cᵢ| + slack, and the standard deviation √(Σ_stat cᵢ²), exact
  -- when the variance is a square and otherwise an enclosure of the root.
  ("mid", [a]) -> elementwise1 (Exact . midpoint) a
  ("bound", [a]) -> elementwise1 (\x -> Exact (collapse x).bound) a
  ("sd", [a]) -> do
    (dims, d, hint, buf) <- tensor =<< a
    let root x = arith (sqrtM p (Exact (collapse x).variance))
    Right (VTensor dims d hint (V.map (>>= root) buf))
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
    (_, d, hint, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    r <- arith (sqrtM p (sumM [mulM p x x | x <- xs]))
    Right (num d hint r)
  ("det", [a]) -> do
    (dims, _, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        num dimOne Nothing <$> arith (determinant p n rows)
      _ -> Left (Internal "det of a non-square matrix")
  ("cholesky", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    case dims of
      [n, n'] | n == n' -> do
        rows <- matrixRows n buf
        l <- arith (choleskyRows p rows)
        d2 <-
          maybe
            (Left (Internal "cholesky of a dimension that is not a square"))
            Right
            (dimRoot 2 d)
        Right (VTensor [n, n] d2 Nothing (V.fromList (map Right (concat l))))
      _ -> Left (Internal "cholesky of a non-square matrix")
  -- Σ cᵢ cᵢᵀ over the statistical nudges (design §3.5): exact, from the
  -- coefficients.
  ("covariance", [a]) -> do
    (dims, d, _, buf) <- tensor =<< a
    xs <- sequence (V.toList buf)
    let n = case dims of
          [k] -> k
          _ -> V.length buf
        cols = map statCoefficients xs
        cov i j = Exact (sum (Map.elems (Map.intersectionWith (*) (cols !! i) (cols !! j))))
    Right
      ( VTensor
          [n, n]
          (dimPow 2 d)
          Nothing
          (V.fromList [Right (cov i j) | i <- [0 .. n - 1], j <- [0 .. n - 1]])
      )
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
  -- Contraction (design §4.2): the sum over the diagonal of two positions
  -- of equal length, an affine sum, so shared nudges correlate as in norm.
  ("contract", [i, j, a]) -> do
    pos <- concat <$> mapM positions [i, j]
    (dims, d, hint, buf) <- tensor =<< a
    case pos of
      [x, y]
        | let lo = min x y
        , let hi = max x y
        , lo /= hi
        , hi < length dims
        , dims !! lo == dims !! hi ->
            let st = strides dims
                dropped = [(l, s) | (q, l, s) <- zip3 [0 ..] dims st, q /= lo, q /= hi]
                outDims = map fst dropped
                diagonal = st !! lo + st !! hi
                element k =
                  let base = sum (zipWith (*) (unflatten outDims k) (map snd dropped))
                   in sumM <$> sequence [buf V.! (base + c * diagonal) | c <- [0 .. dims !! lo - 1]]
             in Right (VTensor outDims d hint (V.generate (product outDims) element))
      _ -> Left (Internal "contract: positions out of range or of different lengths")
  -- Index permutation: position q of the result is position p_q of the
  -- operand; lengths after the permuted ones stay where they are.
  ("permute", [ps, a]) -> do
    perm <- positions ps
    (dims, d, hint, buf) <- tensor =<< a
    let (front, rest) = splitAt (length perm) dims
    if length front /= length perm || any (>= length front) perm
      then Left (Internal "permute: positions out of range")
      else
        let st = strides dims
            outFront = map (front !!) perm
            block = product rest
            element k =
              let (q, r) = k `divMod` block
               in buf V.! (sum (zipWith (*) (unflatten outFront q) (map (st !!) perm)) + r)
         in Right
              ( VTensor
                  (outFront ++ rest)
                  d
                  hint
                  (V.generate (product outFront * block) element)
              )
  -- A slice along axis k at position i (design §2.10): a strided gather of
  -- the result's components, which are not forced.
  ("slice", [k, i, a]) -> do
    axis <- positions k
    pos <- positions i
    (dims, d, hint, buf) <- tensor =<< a
    case (axis, pos) of
      ([ax], [at])
        | (before, len : after) <- splitAt ax dims
        , at < len ->
            let inner = product after
                element q =
                  let (o, r) = q `divMod` inner
                   in buf V.! ((o * len + at) * inner + r)
             in Right
                  ( VTensor
                      (before ++ after)
                      d
                      hint
                      (V.generate (product before * inner) element)
                  )
      _ -> Left (Internal "slice: axis or position out of range")
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
    Right (VTensor dims d ((\h -> h{pinned = True}) <$> uh) buf)
  -- Points and scales (design §3.6).
  ("mkScale", [st, o]) -> do
    (stepM, d, stepHint) <- scalarFull =<< st
    (odims, _, _, obuf) <- tensor =<< o
    originM <- sequence obuf
    Right (VScale (ScaleHint Nothing stepM stepHint originM odims d))
  ("pointOn", [s, x]) -> do
    sc <- scaleOf =<< s
    (_, _, _, ks) <- tensor =<< x
    Right
      ( VPoint
          sc.dims
          sc.dim
          (Just sc)
          (V.zipWith (\o k -> (\k' -> addM o (mulM p k' sc.step)) <$> k) sc.origin ks)
      )
  ("pointAdd", [pt, v]) -> do
    (dims, d, sc, buf) <- point =<< pt
    (_, _, _, vs) <- tensor =<< v
    Right (VPoint dims d sc (V.zipWith (\m dv -> addM <$> m <*> dv) buf vs))
  -- The amount between two points, in the step unit of their common scale.
  ("pointSub", [pt, q]) -> do
    (dims, d, sc1, m1) <- point =<< pt
    (_, _, sc2, m2) <- point =<< q
    let hint = case (sc1, sc2) of
          (Just a, Just b) | a.name == b.name -> a.stepHint
          _ -> Nothing
    Right (VTensor dims d hint (V.zipWith (\x y -> subM <$> x <*> y) m1 m2))
  ("toScale", [pt, s]) -> do
    (dims, d, _, buf) <- point =<< pt
    sc <- scaleOf =<< s
    Right (VPoint dims d (Just sc) buf)
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
    x <- ordered =<< a
    y <- ordered =<< b
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
      (VData c xs, VData c' ys)
        | c == c' && length xs == length ys -> and <$> mapM (uncurry equal) (zip xs ys)
        | otherwise -> Right False
      (VPoint _ _ _ xs, VPoint _ _ _ ys) -> do
        xs' <- sequence (V.toList xs)
        ys' <- sequence (V.toList ys)
        and <$> mapM (\(u, v) -> arith (equalM cfg.sigma p u v)) (zip xs' ys')
      _ ->
        Left
          (Internal "==: operands are not both tensors, both booleans or both points")
  matrixRows n buf = do
    xs <- sequence (V.toList buf)
    pure (chunks n xs)
  chunks n xs
    | null xs = []
    | otherwise = let (r, rest) = splitAt n xs in r : chunks n rest

sumM :: [Magnitude] -> Magnitude
sumM = foldl' addM (Exact 0)

-- Index arithmetic ----------------------------------------------------------------------

{- | The literal index positions of @contract@, @permute@ or @slice@: a number or a
vector of exact naturals (the desugarer admits nothing else).
-}
positions :: Thunk -> Either EvalError [Int]
positions t = do
  (_, _, _, buf) <- tensor =<< t
  xs <- sequence (V.toList buf)
  mapM natural xs
 where
  natural = \case
    Exact r | denominator r == 1, r >= 0 -> Right (fromIntegral (numerator r))
    _ -> Left (Internal "an index position is not a literal natural number")

-- | The row-major strides of a shape.
strides :: [Int] -> [Int]
strides = drop 1 . scanr (*) 1

-- | The multi-index of a row-major offset into a shape.
unflatten :: [Int] -> Int -> [Int]
unflatten dims k = zipWith (\s n -> (k `div` s) `mod` n) (strides dims) dims

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
  VPoint dims _ _ buf -> ("point " <>) . nested dims <$> sequence (V.toList buf)
  VScale _ -> Right "<scale>"
  VBool True -> Right "true"
  VBool False -> Right "false"
  VData c fields -> do
    parts <- mapM (>>= render) fields
    pure
      ( case c of
          Builtin "Tuple" -> "(" <> T.intercalate ", " parts <> ")"
          _ -> T.unwords (conText c : parts)
      )
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

chunksOf :: Int -> [a] -> [[a]]
chunksOf n xs
  | null xs = []
  | otherwise = let (r, rest) = splitAt n xs in r : chunksOf n rest

{- | Cholesky–Banachiewicz on enclosures (design §3.5): @L Lᵀ = P@ with @L@
lower triangular. A pivot whose enclosure reaches zero or below means the
matrix may not be positive definite, which is a domain error.
-}
choleskyRows :: Precision -> [[Magnitude]] -> Either ArithError [[Magnitude]]
choleskyRows p a = go 0 []
 where
  n = length a
  go i done
    | i == n = Right done
    | otherwise = do
        row <- rowFor i done
        go (i + 1) (done ++ [row])
  rowFor i done = do
    let entry j prev
          | j > i = Right (Exact 0)
          | otherwise = do
              let rowJ = if j == i then prev else done !! j
                  s = foldl addM (Exact 0) [mulM p (prev !! k) (rowJ !! k) | k <- [0 .. j - 1]]
                  rest = subM ((a !! i) !! j) s
              if i == j
                then sqrtM p rest
                else divM p rest ((done !! j) !! j)
    foldM (\acc j -> (\x -> acc ++ [x]) <$> entry j acc) [] [0 .. n - 1]

{- | Pair the fields of a constructor with an alternative's binders; the
counts agree by lint.
-}
attach :: Vec k a -> [Thunk] -> Vec k Thunk
attach bs fields = case bs of
  VNil -> VNil
  VCons _ rest -> case fields of
    f : fs -> VCons f (attach rest fs)
    [] -> VCons (Left (Internal "case: missing field")) (attach rest [])
