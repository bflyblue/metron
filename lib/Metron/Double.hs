{-# LANGUAGE MagicHash #-}

{- | The double backend (design §8.2): scalars are IEEE 754 doubles,
computed in the operation order of the formula, as the same formula
ported to Haskell computes them. A literal, an exact rational, is rounded
to the nearest double where it enters. @1/0@ is @Infinity@, @sqrt (-1)@ is
@NaN@ and overflow is infinite; a number that is not finite remembers
where the first NaN or infinity appeared.

Each number carries its ordinary round-to-nearest result, which is the
value shown and which alone decides every comparison, and an estimate of
its error, chosen by @:set samples@:

* __0__, a running error bound (Wilkinson's and Higham's running error
  analysis): one more double per number, bounding the distance from the
  computed result to the exact result of the same formula on the exact
  literals. Each operation adds its own rounding under the standard model
  of floating point, @|fl(x ∘ y) − x ∘ y| ≤ u·|fl(x ∘ y)|@ with @u = 2⁻⁵³@,
  plus @2⁻¹⁰⁷⁴@ for a result in the subnormal range, and propagates its
  operands' bounds through the operation over the whole interval they
  allow. A library function adds 'libmUlps' units in the last place,
  since GHC takes @sin@, @exp@ and the rest from the C library, which does
  not round them correctly. The bound is computed in floating point and
  then widened by a relative @2⁻⁴⁸@, more than the few roundings of its
  own computation can lose.

* __N > 0__, N copies computed in lockstep with random rounding: each
  operation on each copy rounds the exact result down or up to a
  neighbouring double with equal probability (the CESTAC method behind
  CADNA). The direction of the exact result from the nearest double comes
  from an error-free transformation (TwoSum; a fused multiply-add for
  products, quotients and square roots); a library function's copy moves
  one unit in the last place up or down. The choices are a hash of the
  seed, the copy, the operation and its operands, so the same input gives
  the same estimate whatever order lazy values are forced in. The
  estimate is the copies' spread scaled by Student's t at 95 %: @τ·s/√N@.
  @:set rounding nearest@ rounds each copy to nearest instead.

With copies, a declared standard uncertainty is drawn (Monte Carlo, the
GUM's Supplement 1): @x ±σ e@ is @x + |e|·z@ in each copy, @z@ a standard
normal keyed by the nudge's identity, the copy and the seed, and @gauss@
and @noise@ are drawn likewise; @mid@ and @sd@ read the copies' mean and
deviation. Without copies they are refused, and @±@ always is.
-}
module Metron.Double (
  Dbl (..),
  Estimate (..),
  exactDbl,
  estimateOf,
  digitsOfDbl,
  maxDigits,
  showDouble,
  showEstimate,
  originNote,
  nextUpDouble,
  nextDownDouble,
  libmUlps,
  studentT,
) where

import Data.Bits (shiftR, testBit, xor)
import Data.ByteString qualified as BS
import Data.List (transpose)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word64)
import GHC.Exts (Double (D#), fmaddDouble#)
import GHC.Float (castDoubleToWord64, castWord64ToDouble, floatToDigits)
import Metron.Affine (
  ArithError (Domain),
  Magnitude (Exact),
  NudgeId (..),
  Origin,
  originId,
 )
import Metron.Core (NudgeKind (..))
import Metron.Dimension (dimMul, dimOne)
import Metron.Scalar (
  Backend (..),
  Batch (..),
  Decision (..),
  Own (..),
  Rel (..),
  Rounding (..),
  Scalar (..),
  Settings (..),
  Shape (..),
  lacks,
  needsSamples,
 )

-- The numbers ------------------------------------------------------------------------

-- | What a number carries besides its value: its error estimate.
data Estimate
  = -- | a running bound on the error (@samples 0@)
    ErrorBound !Double
  | -- | the copies under random rounding (@samples N@)
    Copies !(VU.Vector Double)
  deriving stock (Eq, Show)

{- | A double: the round-to-nearest IEEE result, its error estimate, and,
once it is not finite, the operation that first made a NaN or an
infinity.
-}
data Dbl = Dbl
  { value :: !Double
  , estimate :: !Estimate
  , origin :: !(Maybe Text)
  }
  deriving stock (Show)

-- | Equal values with equal estimates; where a NaN came from is not part of it.
instance Eq Dbl where
  a == b = a.value == b.value && a.estimate == b.estimate

-- | A double known exactly.
exactDbl :: Double -> Dbl
exactDbl v = Dbl v (ErrorBound 0) Nothing

-- | The unit roundoff, @2⁻⁵³@.
u :: Double
u = 1.1102230246251565e-16

-- | The smallest subnormal, @2⁻¹⁰⁷⁴@: the absolute error of an underflow is at most half of it.
eta :: Double
eta = 5.0e-324

-- | A bound computed in floating point, widened past its own roundings.
up :: Double -> Double
up x
  | isNaN x = 1 / 0
  | otherwise = x * (1 + 3.552713678800501e-15) + 4 * eta

{- | The error of each library function, in units in the last place of its
result: GHC calls the C library, whose functions are not correctly
rounded. The figures are chosen here, stated rather than guaranteed by
the library: one unit for the functions modern C libraries round within
one, two for the rest. They are not checked against a published table;
glibc's own test suite flags only errors above nine units. @sqrt@ is
correctly rounded by IEEE 754, half a unit.
-}
libmUlps :: Text -> Double
libmUlps = \case
  "sqrt" -> 0.5
  "exp" -> 1
  "log" -> 1
  "sin" -> 1
  "cos" -> 1
  "atan" -> 1
  "asin" -> 1
  "acos" -> 1
  "tan" -> 2
  "sinh" -> 2
  "cosh" -> 2
  "tanh" -> 2
  "atan2" -> 2
  _ -> 2

-- | @k@ units in the last place of @z@, at most: @ulp(z) ≤ 2u·|z|@, or @2⁻¹⁰⁷⁴@ below the normals.
ulpsOf :: Double -> Double -> Double
ulpsOf k z = k * (2 * u * abs z + eta)

finite :: Double -> Bool
finite x = not (isNaN x || isInfinite x)

nextUpDouble :: Double -> Double
nextUpDouble x
  | isNaN x || x == 1 / 0 = x
  | x == 0 = eta
  | x > 0 = castWord64ToDouble (castDoubleToWord64 x + 1)
  | otherwise = castWord64ToDouble (castDoubleToWord64 x - 1)

nextDownDouble :: Double -> Double
nextDownDouble = negate . nextUpDouble . negate

fmaDouble :: Double -> Double -> Double -> Double
fmaDouble (D# a) (D# b) (D# c) = D# (fmaddDouble# a b c)

-- Random rounding -------------------------------------------------------------------

-- | SplitMix's finaliser: a well-mixed 64-bit hash.
mix :: Word64 -> Word64
mix z0 =
  let z1 = (z0 `xor` (z0 `shiftR` 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
   in z2 `xor` (z2 `shiftR` 31)

-- | Whether copy @i@ rounds up at this operation on these operands.
coin :: Settings -> Int -> Word64 -> [Double] -> Bool
coin s i op xs =
  testBit
    ( mix
        ( foldl'
            (\h x -> mix (h + castDoubleToWord64 x))
            (mix (fromIntegral s.seed * 0x9e3779b97f4a7c15 + fromIntegral i) + op)
            xs
        )
    )
    63

{- | The copies of a constant whose nearest double is @r@ and whose exact
value lies on @side@ of it: each @r@ when rounding to nearest, else each
the neighbour its coin picks.
-}
constantCopies ::
  Settings -> Word64 -> [Double] -> Double -> Ordering -> VU.Vector Double
constantCopies s op xs r side = case s.rounding of
  RoundNearest -> VU.replicate s.batch.count r
  RoundRandom ->
    VU.generate
      s.batch.count
      (\i -> roundTo (coin s (s.batch.first + i) op xs) r side)

{- | The neighbour a random rounding chooses: the nearest double @r@ and the
side the exact result lies on.
-}
roundTo :: Bool -> Double -> Ordering -> Double
roundTo upward r = \case
  _ | not (finite r) -> r
  EQ -> r
  GT -> if upward then nextUpDouble r else r
  LT -> if upward then r else nextDownDouble r

-- | A library function's copy: one unit in the last place up or down.
wobble :: Bool -> Double -> Double
wobble upward r
  | not (finite r) = r
  | upward = nextUpDouble r
  | otherwise = nextDownDouble r

-- | The side of the nearest double the exact result of each operation lies on.
sumSide, productSide, quotientSide :: Double -> Double -> (Double, Ordering)
sumSide a b =
  let s = a + b
      bb = s - a
   in (s, if finite s then compare ((a - (s - bb)) + (b - bb)) 0 else EQ)
productSide a b =
  let p = a * b
   in (p, if finite p then compare (fmaDouble a b (negate p)) 0 else EQ)
quotientSide a b =
  let q = a / b
      r = fmaDouble (negate q) b a
   in (q, if finite q && b /= 0 then compare (r * signum b) 0 else EQ)

sqrtSide :: Double -> (Double, Ordering)
sqrtSide a =
  let r = sqrt a
   in (r, if finite r then compare (fmaDouble (negate r) r a) 0 else EQ)

-- | The copies of a number, @n@ of them; a number with a bound is its value @n@ times.
copiesOf :: Int -> Dbl -> VU.Vector Double
copiesOf n x = case x.estimate of
  Copies cs -> cs
  ErrorBound _ -> VU.replicate n x.value

-- | How many copies the operands carry, if any does.
copyCount :: [Dbl] -> Maybe Int
copyCount =
  listToMaybe
    . mapMaybe
      (\x -> case x.estimate of Copies cs -> Just (VU.length cs); _ -> Nothing)

-- Operations -------------------------------------------------------------------------

{- | Where a NaN or an infinity came from: an operand's, or this operation
when it made one from finite operands.
-}
originOf :: [Dbl] -> Double -> Text -> Maybe Text
originOf xs z described = case mapMaybe (.origin) xs of
  o : _ -> Just o
  []
    | not (finite z) && all (finite . (.value)) xs -> Just described
    | otherwise -> Nothing

{- | An operation of any arity. @fv@ gives the value, @fb@ the bound from the
operands' values and bounds and the value, @fc@ a copy from the copies'
operands and the coin; @op@ identifies it to the coin; @say@ writes it
for a NaN's origin.
-}
operation ::
  Settings ->
  Word64 ->
  ([Text] -> Text) ->
  ([Double] -> Double) ->
  ([(Double, Double)] -> Double -> Double) ->
  (Bool -> [Double] -> Double) ->
  [Dbl] ->
  Dbl
operation s op say fv fb fc xs =
  let z = fv (map (.value) xs)
      est = case copyCount xs of
        Nothing -> ErrorBound (boundOf [(x.value, b) | x <- xs, ErrorBound b <- [x.estimate]])
        Just n ->
          let columns = map (copiesOf n) xs
              -- To nearest, each copy is the operation itself; at random, the
              -- coin picks the neighbour.
              copy i =
                let ys = map (VU.! i) columns
                 in case s.rounding of
                      RoundNearest -> fv ys
                      RoundRandom -> fc (coin s (s.batch.first + i) op ys) ys
           in Copies (VU.generate n copy)
      -- Nothing to add is an exact result, which stays exact.
      boundOf bs
        | not (finite z) = 0 / 0
        | otherwise = let raw = fb bs z in if raw == 0 then 0 else up raw
   in Dbl z est (originOf xs z (say (map (showDouble . (.value)) xs)))

{- | An operation on two numbers whose exact result's side of the nearest
double is known. @exact@ says when that side being 'EQ' proves the
result exact: always for a sum, which is exact whenever it is subnormal;
for a product or a quotient only above the subnormals, where the
error-free transformation itself can underflow.
-}
binary ::
  Settings ->
  Word64 ->
  ([Text] -> Text) ->
  (Double -> Double -> (Double, Ordering)) ->
  (Double -> Double -> Double -> Bool) ->
  (Double -> Double -> Double -> Double -> Double -> Double) ->
  Dbl ->
  Dbl ->
  Dbl
binary s op say side exact fb x y =
  operation
    s
    op
    say
    (\case [a, b] -> fst (side a b); _ -> 0 / 0)
    ( \case
        [(a, ea), (b, eb)] -> \z ->
          fb a ea b eb z
            + (if snd (side a b) == EQ && exact a b z then 0 else u * abs z + eta)
        _ -> const (0 / 0)
    )
    (\c -> \case [a, b] -> uncurry (roundTo c) (side a b); _ -> 0 / 0)
    [x, y]

-- | The least positive normal double, @2⁻¹⁰²²@.
minNormal :: Double
minNormal = 2.2250738585072014e-308

infixOp :: Text -> [Text] -> Text
infixOp o = \case
  [a, b] -> a <> " " <> o <> " " <> b
  as -> T.unwords (o : as)

prefixOp :: Text -> [Text] -> Text
prefixOp f as = f <> " " <> T.unwords (map paren as)
 where
  paren t = if T.any (== '-') t then "(" <> t <> ")" else t

addD, subD, mulD :: Settings -> Dbl -> Dbl -> Dbl
addD s = binary s 1 (infixOp "+") sumSide (\_ _ _ -> True) (\_ ea _ eb _ -> ea + eb)
subD s =
  binary
    s
    2
    (infixOp "-")
    (\a b -> sumSide a (negate b))
    (\_ _ _ -> True)
    (\_ ea _ eb _ -> ea + eb)
mulD s =
  binary
    s
    3
    (infixOp "*")
    productSide
    (\a b z -> abs z >= minNormal || a == 0 || b == 0)
    (\a ea b eb _ -> abs a * eb + abs b * ea + ea * eb)

{- | @x / y@: the quotient of the intervals, unbounded when the divisor's
reaches zero.
-}
divD :: Settings -> Dbl -> Dbl -> Dbl
divD s =
  binary
    s
    4
    (infixOp "/")
    quotientSide
    (\a _ z -> abs z >= minNormal || a == 0)
    bound
 where
  bound a ea b eb _
    | ea == 0 && eb == 0 = 0
    | abs b > eb = (ea * abs b + abs a * eb) / (abs b * (abs b - eb))
    | otherwise = 1 / 0

-- | Exact operations: the value and every copy changed alike, the bound kept.
exactly1 :: (Double -> Double) -> Dbl -> Dbl
exactly1 f x =
  Dbl
    (f x.value)
    ( case x.estimate of
        ErrorBound e -> ErrorBound e
        Copies cs -> Copies (VU.map f cs)
    )
    x.origin

{- | A library function, given how its operand's interval spreads into its
result: the propagated error from the value, the bound and the computed
result. Its own rounding is 'libmUlps'.
-}
libm ::
  Settings ->
  Word64 ->
  Text ->
  (Double -> Double) ->
  (Double -> Double -> Double -> Double) ->
  Dbl ->
  Dbl
libm s op name f spread =
  unary1
    s
    op
    name
    f
    (\x ex z -> spread x ex z + ulpsOf (libmUlps name) z)
    (\c a -> wobble c (f a))

unary1 ::
  Settings ->
  Word64 ->
  Text ->
  (Double -> Double) ->
  (Double -> Double -> Double -> Double) ->
  (Bool -> Double -> Double) ->
  Dbl ->
  Dbl
unary1 s op name f fb fc x =
  operation
    s
    op
    (prefixOp name)
    (\case [a] -> f a; _ -> 0 / 0)
    (\case [(a, ea)] -> fb a ea; _ -> const (0 / 0))
    (\c -> \case [a] -> fc c a; _ -> 0 / 0)
    [x]

{- | The error a function's result inherits from an operand known within
@e@ of @x@, for a function monotone on the interval, which lies inside
its domain @inside@: the larger change at its ends, each end's own
library error included. Unbounded when the interval leaves the domain.
-}
monotone ::
  Text ->
  (Double -> Bool) ->
  (Double -> Double) ->
  Double ->
  Double ->
  Double ->
  Double
monotone name inside f x e z
  | e == 0 = 0
  | not (inside lo && inside hi) = 1 / 0
  | otherwise =
      maximum [abs (f end - z) + ulpsOf k (f end) | end <- [lo, hi]] + ulpsOf k z
 where
  k = libmUlps name
  lo = nextDownDouble (x - e)
  hi = nextUpDouble (x + e)

-- | As 'monotone', for a convex function whose least value, @atMin@, is at @0@.
convexAtZero ::
  Text -> (Double -> Double) -> Double -> Double -> Double -> Double
convexAtZero name f x e z
  | e == 0 = 0
  | lo <= 0 && hi >= 0 =
      max (monotone name (const True) f x e z) (abs (z - f 0) + ulpsOf k z)
  | otherwise = monotone name (const True) f x e z
 where
  k = libmUlps name
  lo = nextDownDouble (x - e)
  hi = nextUpDouble (x + e)

-- | @sin@ or @cos@ moved by @h@: at most @|h|·|f′(x)| + h²/2@, and never more than 2.
periodic :: (Double -> Double) -> Double -> Double -> Double -> Double
periodic derivative x e _ = min 2 (e * (abs (derivative x) + 4 * u + e / 2))

sqrtD :: Settings -> Dbl -> Dbl
sqrtD s =
  unary1
    s
    5
    "sqrt"
    sqrt
    (\x e z -> spread x e z + u * abs z)
    (\c a -> uncurry (roundTo c) (sqrtSide a))
 where
  spread x e z
    | e == 0 = 0
    | x < 0 = 0 / 0
    | otherwise =
        let lo = max 0 (nextDownDouble (x - e))
            hi = nextUpDouble (x + e)
         in maximum [abs (sqrt end - z) + u * sqrt end | end <- [lo, hi]] + u * z

expD
  , logD
  , sinD
  , cosD
  , tanD
  , asinD
  , acosD
  , atanD
  , sinhD
  , coshD
  , tanhD ::
    Settings -> Dbl -> Dbl
expD s = libm s 6 "exp" exp (monotone "exp" (const True) exp)
logD s = libm s 7 "log" log (monotone "log" (> 0) log)
sinD s = libm s 8 "sin" sin (periodic cos)
cosD s = libm s 9 "cos" cos (periodic sin)
tanD s = libm s 10 "tan" tan spread
 where
  -- Monotone between two poles; unbounded across one.
  spread x e z
    | e == 0 = 0
    | e >= 1 || signum (cos (x - e)) /= signum (cos (x + e)) || cos (x - e) == 0 =
        1 / 0
    | otherwise = monotone "tan" (const True) tan x e z
asinD s = libm s 11 "asin" asin (monotone "asin" (\v -> v >= -1 && v <= 1) asin)
acosD s = libm s 12 "acos" acos (monotone "acos" (\v -> v >= -1 && v <= 1) acos)
atanD s = libm s 13 "atan" atan (monotone "atan" (const True) atan)
sinhD s = libm s 14 "sinh" sinh (monotone "sinh" (const True) sinh)
coshD s = libm s 15 "cosh" cosh (convexAtZero "cosh" cosh)
tanhD s = libm s 16 "tanh" tanh (monotone "tanh" (const True) tanh)

{- | @atan2 y x@: its gradient has length @1/r@, so a box of half-sides
@ey@, @ex@ moves it by at most @(ex + ey)/r_min@; a box that reaches the
origin or crosses the branch cut along the negative x-axis may move it
by up to @2π@.
-}
atan2D :: Settings -> Dbl -> Dbl -> Dbl
atan2D s y0 x0 =
  operation
    s
    17
    (prefixOp "atan2")
    (\case [a, b] -> atan2 a b; _ -> 0 / 0)
    (\case [(a, ea), (b, eb)] -> bound a ea b eb; _ -> const (0 / 0))
    (\c -> \case [a, b] -> wobble c (atan2 a b); _ -> 0 / 0)
    [y0, x0]
 where
  bound y ey x ex z
    | ey == 0 && ex == 0 = ulpsOf (libmUlps "atan2") z
    | x - ex <= 0 && y - ey <= 0 && y + ey >= 0 = 2 * pi
    | rmin <= 0 = 2 * pi
    | otherwise = min (2 * pi) ((ex + ey) / rmin) + ulpsOf (libmUlps "atan2") z
   where
    rmin = sqrt (x * x + y * y) * (1 - 4 * u) - (ex + ey)

{- | Rounding to a whole number, as Haskell's @floor@, @ceiling@ and
@round@ (to even at a half) do; not a finite number stays as it is. Its
error is how far the whole number can move across the operand's interval.
-}
rounding :: Settings -> Word64 -> Text -> (Double -> Integer) -> Dbl -> Dbl
rounding s op name f =
  unary1 s op name g (\x e z -> if e == 0 then 0 else spread x e z) (const g)
 where
  g v = if finite v then fromInteger (f v) else v
  spread x e _
    | not (finite lo && finite hi) = 1 / 0
    | otherwise =
        let at v = toRational (f v)
            here = at x
         in fromRational (max (abs (at hi - here)) (abs (here - at lo))) + 1
   where
    lo = nextDownDouble (x - e)
    hi = nextUpDouble (x + e)

{- | @x ^ n@ by the multiplications Haskell's @^@ makes (repeated squaring),
and a negative power its reciprocal, as @^^@: the same rounding errors
as the ported formula.
-}
powD :: Settings -> Dbl -> Integer -> Dbl
powD s x n
  | n < 0 = divD s (exactDbl 1) (powD s x (negate n))
  | n == 0 = exactDbl 1
  | otherwise = go x n
 where
  go b k
    | even k = go (mulD s b b) (k `quot` 2)
    | k == 1 = b
    | otherwise = acc (mulD s b b) (k `quot` 2) b
  acc b k z
    | even k = acc (mulD s b b) (k `quot` 2) z
    | k == 1 = mulD s b z
    | otherwise = acc (mulD s b b) (k `quot` 2) (mulD s b z)

-- | The correctly rounded fused multiply-add @a·b + c@, one rounding.
fmaD :: Settings -> Dbl -> Dbl -> Dbl -> Dbl
fmaD s a b c =
  operation
    s
    18
    (prefixOp "fma")
    (\case [x, y, z] -> fmaDouble x y z; _ -> 0 / 0)
    ( \case
        [(x, ex), (y, ey), (_, ez)] -> \z -> abs x * ey + abs y * ex + ex * ey + ez + u * abs z
        _ -> const (0 / 0)
    )
    ( \cn -> \case
        [x, y, z] ->
          let r = fmaDouble x y z
              side =
                if finite r
                  then compare (toRational x * toRational y + toRational z) (toRational r)
                  else EQ
           in roundTo cn r side
        _ -> 0 / 0
    )
    [a, b, c]

{- | A literal: the nearest double to the exact rational. Its error is the
rounding itself, exactly; its copies each round down or up to one of the
two doubles around it.
-}
literalD :: Settings -> Rational -> Dbl
literalD s r =
  Dbl
    v
    est
    (if finite v then Nothing else Just "a literal beyond the largest double")
 where
  v = fromRational r :: Double
  side = if finite v then compare r (toRational v) else EQ
  est
    | s.samples > 0 =
        Copies (constantCopies s 0 [v] v side)
    | side == EQ || not (finite v) = ErrorBound 0
    | otherwise = ErrorBound (roundedUp (abs (r - toRational v)))
  roundedUp q = let d = fromRational q in if toRational d < q then nextUpDouble d else d

-- | π to the nearest double, which is below π by about @1.2246·10⁻¹⁶@.
piD :: Settings -> Dbl
piD s
  | s.samples > 0 =
      Dbl
        pi
        (Copies (constantCopies s 19 [] pi GT))
        Nothing
  | otherwise = Dbl pi (ErrorBound 1.2246467991473533e-16) Nothing

-- Declared uncertainty: Monte Carlo ---------------------------------------------------

{- | A declared unknown's key: the first eight bytes of its content-addressed
identity (design §3.2.4), the SHA-256 the affine backend names the same
nudge by. One hash per declared component, not per copy.
-}
drawKey :: NudgeKind -> Origin -> Rational -> Word64
drawKey k o m =
  let NudgeId bytes = originId k o m
   in BS.foldl' (\h b -> h * 256 + fromIntegral b) 0 (BS.take 8 bytes)

{- | Copy @i@'s draw of the unknown with this key: a standard normal, by
Box–Muller on two uniforms hashed from the key, the seed and the copy
with SplitMix's finaliser. @u₁@ lies in @(0, 1]@, so its logarithm is
finite; only the cosine of the pair is used, so each draw depends on its
own key, seed and copy and nothing else, and the order lazy values are
forced in cannot change it.
-}
standardNormal :: Settings -> Word64 -> Int -> Double
standardNormal s key i =
  let base = mix (mix (key + fromIntegral s.seed * 0x9e3779b97f4a7c15) + fromIntegral i)
      uniform w = (fromIntegral (w `shiftR` 11) + 1) * 1.1102230246251565e-16
      u1 = uniform (mix (base + 1))
      u2 = uniform (mix (base + 2))
   in sqrt (-(2 * log u1)) * cos (2 * pi * u2)

{- | A unit unknown: 0, drawn as a standard normal in each copy. Its value
is 0, so a formula's IEEE result is its result at the nominal inputs.
-}
drawn :: Settings -> NudgeKind -> Origin -> Rational -> Dbl
drawn s k o m =
  let key = drawKey k o m
   in Dbl
        0
        (Copies (VU.generate s.batch.count (standardNormal s key . (s.batch.first +))))
        Nothing

{- | @noise n@ / @gauss n@, one component: drawn in each copy, as the
design has it for both (design §8.2), with copies; refused without.
-}
noiseD :: Settings -> NudgeKind -> Origin -> Either ArithError Dbl
noiseD s k o
  | s.samples > 0 = Right (drawn s k o 0)
  | otherwise = Left (Domain (needsSamples (noiseName k)))

noiseName :: NudgeKind -> Text
noiseName = \case
  Bound -> "noise"
  Stat -> "gauss"

{- | @x ±σ e@: @x + |e|·z@ in each copy, @z@ drawn under the identity the
affine backend gives the nudge, so the same unknown has the same draw
wherever it appears in a copy and @x - x@ is 0 in every copy. The sum and
the product round as the copies do. @±@, a bound, has no distribution
and stays refused (design §8.2).
-}
uncertainD ::
  Settings -> NudgeKind -> Origin -> Dbl -> Dbl -> Either ArithError Dbl
uncertainD s k o x e = case k of
  Bound -> refused "±"
  Stat
    | s.samples > 0 ->
        Right (addD s x (mulD s (exactly1 abs e) (drawn s k o midpoint)))
    | otherwise -> Left (Domain (needsSamples "±σ"))
 where
  midpoint = if finite x.value then toRational x.value else 0

{- | The copies' mean, or their sample standard deviation (with @N − 1@),
as a number known exactly; refused without copies.
-}
copyStatistic ::
  Text -> (VU.Vector Double -> Double) -> Settings -> Dbl -> Either ArithError Dbl
copyStatistic name f s x = case x.estimate of
  Copies cs -> Right (exactDbl (f cs))
  ErrorBound _
    | s.samples > 0 -> Right (exactDbl (f (VU.singleton x.value)))
    | otherwise -> Left (Domain (needsSamples name))

meanOf :: VU.Vector Double -> Double
meanOf cs = VU.sum cs / fromIntegral (VU.length cs)

deviationOf :: VU.Vector Double -> Double
deviationOf cs
  | n < 2 = 0
  | otherwise =
      sqrt (VU.sum (VU.map (\c -> (c - m) * (c - m)) cs) / fromIntegral (n - 1))
 where
  n = VU.length cs
  m = meanOf cs

-- Comparisons -------------------------------------------------------------------------

relation :: Rel -> Double -> Double -> Bool
relation = \case
  Lt -> (<)
  Le -> (<=)
  Gt -> (>)
  Ge -> (>=)

relText :: Rel -> Text
relText = \case
  Lt -> "<"
  Le -> "<="
  Gt -> ">"
  Ge -> ">="

{- | The IEEE result decides; with copies, a comparison they disagree about
is lost in rounding.
-}
decide ::
  Settings -> Text -> (Double -> Double -> Bool) -> Dbl -> Dbl -> Decision
decide s what holds x y =
  let result = holds x.value y.value
      lost = case copyCount [x, y] of
        Nothing -> Nothing
        Just n
          | VU.any (/= result) (VU.zipWith holds (copiesOf n x) (copiesOf n y)) ->
              Just
                ( "the comparison "
                    <> showDouble x.value
                    <> " "
                    <> what
                    <> " "
                    <> showDouble y.value
                    <> " goes both ways across the "
                    <> T.pack (show s.samples)
                    <> " samples: the condition is lost in rounding"
                )
          | otherwise -> Nothing
   in Decision{holds = result, lost}

-- Estimates ----------------------------------------------------------------------------

{- | Student's t at 97.5 % (a two-sided 95 % interval) for @k@ degrees of
freedom; past 30, the first terms of its expansion about the normal.
-}
studentT :: Int -> Double
studentT k = case drop (k - 1) table of
  t : _ | k >= 1 -> t
  _ -> 1.959964 + 2.372 / fromIntegral (max 1 k)
 where
  table =
    [ 12.706
    , 4.303
    , 3.182
    , 2.776
    , 2.571
    , 2.447
    , 2.365
    , 2.306
    , 2.262
    , 2.228
    , 2.201
    , 2.179
    , 2.160
    , 2.145
    , 2.131
    , 2.120
    , 2.110
    , 2.101
    , 2.093
    , 2.086
    , 2.080
    , 2.074
    , 2.069
    , 2.064
    , 2.060
    , 2.056
    , 2.052
    , 2.048
    , 2.045
    , 2.042
    ]

{- | The error estimate: the bound, or the copies' spread scaled by
Student's t, @τ·s/√N@.
-}
estimateOf :: Dbl -> Double
estimateOf x = case x.estimate of
  ErrorBound e -> e
  Copies cs
    | n < 2 -> 0
    | otherwise ->
        studentT (n - 1) * sqrt (var / fromIntegral (n - 1)) / sqrt (fromIntegral n)
   where
    n = VU.length cs
    m = VU.sum cs / fromIntegral n
    var = VU.sum (VU.map (\c -> (c - m) * (c - m)) cs)

-- | The most significant decimal digits a double has, @log₁₀ 2⁵³@.
maxDigits :: Double
maxDigits = 15.954589770191003

-- | The significant digits the estimate leaves: @−log₁₀ (error / |x|)@, from 0 to 'maxDigits'.
digitsOfDbl :: Dbl -> Double
digitsOfDbl x
  | not (finite v) || not (finite e) = 0
  | e == 0 = maxDigits
  | v == 0 = 0
  | otherwise = max 0 (min maxDigits (negate (logBase 10 (e / abs v))))
 where
  v = x.value
  e = estimateOf x

-- | The number of doubles from one to the other.
ulpsBetween :: Double -> Double -> Double
ulpsBetween a b
  | isNaN a || isNaN b = 0 / 0
  | otherwise = fromInteger (abs (ordinal a - ordinal b))
 where
  ordinal x =
    let w = castDoubleToWord64 x
     in if testBit w 63
          then negate (toInteger (w - 0x8000000000000000))
          else toInteger w

-- Printing ----------------------------------------------------------------------------

{- | A double as Haskell's @show@ would choose its digits, the shortest
that read back to it, written as Metron writes numbers: a whole number
without a point, scientific notation outside @[10⁻⁴, 10¹⁵)@.
-}
showDouble :: Double -> Text
showDouble x
  | isNaN x = "NaN"
  | isInfinite x = if x > 0 then "Infinity" else "-Infinity"
  | x < 0 || isNegativeZero x = "-" <> showDouble (negate x)
  | x == 0 = "0"
  | otherwise =
      let (ds, e) = floatToDigits 10 x
          digits = T.pack (concatMap show ds)
          n = T.length digits
       in if e > 15 || e < -3
            then
              T.take 1 digits
                <> (if n > 1 then "." <> T.drop 1 digits else "")
                <> "e"
                <> T.pack (show (e - 1))
            else
              if e <= 0
                then "0." <> T.replicate (negate e) "0" <> digits
                else
                  if n <= e
                    then digits <> T.replicate (e - n) "0"
                    else T.take e digits <> "." <> T.drop e digits

{- | An error estimate to two significant digits, rounded up when it is a
bound, so that what prints is still one.
-}
showEstimate :: Bool -> Double -> Text
showEstimate isBound e
  | not (finite e) || e == 0 = showDouble e
  | otherwise =
      let k = floor (logBase 10 e) :: Int
          scaled = toRational e / 10 ^^ (k - 1)
          m = (if isBound then ceiling scaled else round scaled) :: Integer
          (m', k') = if m >= 100 then ((m + 9) `div` 10, k + 1) else (m, k)
       in twoDigits m' k'
 where
  -- @m@, two digits, times @10^(k−1)@: scientific outside @[10⁻⁴, 10¹⁵)@.
  twoDigits m k
    | k < -4 || k >= 15 =
        T.take 1 ds <> "." <> T.drop 1 ds <> "e" <> T.pack (show k)
    | k >= 1 = T.pack (show (m * 10 ^ (k - 1)))
    | k == 0 = T.take 1 ds <> "." <> T.drop 1 ds
    | otherwise = "0." <> T.replicate (negate k - 1) "0" <> ds
   where
    ds = T.pack (show m)

-- | Where the first NaN or infinity among some numbers came from, if one did.
originNote :: [Dbl] -> Maybe Text
originNote xs = case [(x.value, o) | x <- xs, not (finite x.value), Just o <- [x.origin]] of
  (v, o) : _ ->
    Just
      ( (if isNaN v then "the first NaN came from " else "the first infinity came from ")
          <> o
      )
  [] -> Nothing

-- Linear algebra -------------------------------------------------------------------------

{- | The determinant by Gaussian elimination with partial pivoting on the
values; a zero pivot makes it zero.
-}
determinantD :: Settings -> [[Dbl]] -> Dbl
determinantD s = go (exactDbl 1)
 where
  go acc = \case
    [] -> acc
    rows ->
      case pivotOf rows of
        Nothing -> exactDbl 0
        Just (k, prow) ->
          let others = [r | (i, r) <- zip [0 :: Int ..] rows, i /= k]
              p = headOr prow
              sign = if even k then id else negD
              reduced =
                [ zipWith
                    (\a b -> subD s a (mulD s (divD s (headOr r) p) b))
                    (drop 1 r)
                    (drop 1 prow)
                | r <- others
                ]
           in go (sign (mulD s acc p)) reduced
  negD = exactly1 negate

headOr :: [Dbl] -> Dbl
headOr = \case
  x : _ -> x
  [] -> exactDbl 0

-- | The row whose first entry is largest in magnitude, if it is not zero.
pivotOf :: [[Dbl]] -> Maybe (Int, [Dbl])
pivotOf rows = case [(abs (headOr r).value, (i, r)) | (i, r) <- zip [0 ..] rows] of
  [] -> Nothing
  cs ->
    let (best, choice) = foldl1 (\a b -> if fst b > fst a then b else a) cs
     in if best == 0 || isNaN best then Nothing else Just choice

{- | The inverse by Gauss–Jordan elimination with partial pivoting on the
values. A zero pivot divides by zero, as IEEE arithmetic does.
-}
invertD :: Settings -> Int -> [[Dbl]] -> [[Dbl]]
invertD s n a = map (drop n) (eliminate 0 augmented)
 where
  augmented =
    [ row ++ [exactDbl (if i == j then 1 else 0) | j <- [0 .. n - 1]]
    | (i, row) <- zip [0 :: Int ..] a
    ]
  eliminate c rows
    | c >= n = rows
    | otherwise =
        let (above, rest) = splitAt c rows
            k = maybe 0 fst (pivotOf (map (drop c) rest))
            prow = rowAt rest k
            others = above ++ [r | (i, r) <- zip [0 ..] rest, i /= k]
            p = entryAt prow c
            prow' = map (\x -> divD s x p) prow
            clear r = let f = entryAt r c in zipWith (\x y -> subD s x (mulD s f y)) r prow'
            (before, after) = splitAt c (map clear others)
         in eliminate (c + 1) (before ++ [prow'] ++ after)

-- | The @i@-th element, or the default past the end (unreachable for a square matrix).
atOr :: a -> [a] -> Int -> a
atOr d xs i = case drop i xs of
  x : _ -> x
  [] -> d

entryAt :: [Dbl] -> Int -> Dbl
entryAt = atOr (exactDbl (0 / 0))

rowAt :: [[Dbl]] -> Int -> [Dbl]
rowAt = atOr []

{- | The matrix exponential by scaling and squaring: the matrix halved until
its norm is at most ½, twenty terms of the series, then squared back.
Halving and doubling by powers of two are exact.
-}
matrixExpD :: Settings -> Int -> [[Dbl]] -> [[Dbl]]
matrixExpD s n a = atOr series (iterate square series) halvings
 where
  norm = maximum (0 : [sum [abs x.value | x <- row] | row <- a])
  halvings =
    if norm <= 0.5 || not (finite norm)
      then 0
      else ceiling (logBase 2 (norm / 0.5)) :: Int
  scaled = [[mulD s x (exactDbl (2 ^^ negate halvings)) | x <- row] | row <- a]
  identity =
    [ [exactDbl (if i == j then 1 else 0) | j <- [0 .. n - 1]]
    | i <- [0 .. n - 1 :: Int]
    ]
  product' x y =
    [ [foldl' (addD s) (exactDbl 0) (zipWith (mulD s) row col) | col <- transpose y]
    | row <- x
    ]
  series =
    fst
      ( foldl'
          ( \(acc, term) k ->
              let term' =
                    [ [divD s v (exactDbl (fromIntegral k)) | v <- row] | row <- product' term scaled
                    ]
               in (zipWith (zipWith (addD s)) acc term', term')
          )
          (identity, identity)
          [1 .. 20 :: Int]
      )
  square m = product' m m

{- | The lower Cholesky factor, @L Lᵀ = A@, of a matrix whose entries are
symmetric in value. A negative pivot gives a NaN, as @sqrt@ does.
-}
choleskyD :: Settings -> Text -> [[Dbl]] -> Either ArithError [[Dbl]]
choleskyD s what a
  | or
      [ (entryAt (rowAt a i) j).value /= (entryAt (rowAt a j) i).value
      | i <- [0 .. n - 1]
      , j <- [i + 1 .. n - 1]
      ] =
      Left (Domain what)
  | otherwise = Right (foldl' row [] [0 .. n - 1])
 where
  n = length a
  row done i =
    let entry j
          | j > i = exactDbl 0
          | j == i =
              sqrtD s (subD s (entryAt (rowAt a i) i) (dotTo j (rowAt cur i) (rowAt cur i)))
          | otherwise =
              divD
                s
                (subD s (entryAt (rowAt a i) j) (dotTo j (rowAt cur i) (rowAt done j)))
                (entryAt (rowAt done j) j)
        cur = done ++ [new]
        new = map entry [0 .. n - 1]
     in done ++ [new]
  dotTo j xs ys = foldl' (addD s) (exactDbl 0) (take j (zipWith (mulD s) xs ys))

-- The instance --------------------------------------------------------------------------

refused :: Text -> Either ArithError a
refused what = Left (Domain (lacks DoubleBackend what))

instance Scalar Dbl where
  backendOf = DoubleBackend
  literal = literalD
  exactly x
    | finite x.value && estimateOf x == 0 = Just (toRational x.value)
    | otherwise = Nothing
  addM = addD
  subM = subD
  mulM = mulD
  negM = exactly1 negate
  absM _ = exactly1 abs
  divM s x y = Right (divD s x y)
  powM s x n = Right (powD s x n)
  sqrtM s = Right . sqrtD s
  logM s = Right . logD s
  tanM s = Right . tanD s
  asinM s = Right . asinD s
  acosM s = Right . acosD s
  expM = expD
  sinM = sinD
  cosM = cosD
  atanM = atanD
  sinhM = sinhD
  coshM = coshD
  tanhM = tanhD
  atan2M s y x = Right (atan2D s y x)
  piM = piD
  floorM s = Right . rounding s 20 "floor" floor
  ceilM s = Right . rounding s 21 "ceil" ceiling
  roundM s = Right . rounding s 22 "round" round
  relate s rel x y = Right (decide s (relText rel) (relation rel) x y)
  equalM s x y = Right (decide s "==" (==) x y)
  sizeOf _ = Nothing
  stepProblem step
    | step.value == 0 = Just "its step is zero"
    | not (finite step.value) = Just ("its step is " <> showDouble step.value)
    | otherwise = Nothing
  hintFactor x
    | finite x.value = Exact (toRational x.value)
    | otherwise = Exact 0
  noiseM = noiseD
  uncertainM = uncertainD
  determinantM s _ rows = Right (determinantD s rows)
  invertM s n rows = Right (invertD s n rows)
  matrixExpM s n rows = Right (matrixExpD s n rows)
  choleskyM = choleskyD
  own = \case
    -- The error estimate itself, as a number known exactly.
    "errorOf" -> Just (Each Keep False (\_ x -> Right (exactDbl (estimateOf x))))
    "digitsOf" -> Just (Each Bare False (\_ x -> Right (exactDbl (digitsOfDbl x))))
    -- The next double up, of the value and of every copy: a function of the
    -- double, so its error is the operand's.
    "nextUp" ->
      Just
        ( Each
            Keep
            False
            ( \_ x ->
                Right
                  ( Dbl
                      (nextUpDouble x.value)
                      ( case x.estimate of
                          ErrorBound e -> ErrorBound e
                          Copies cs -> Copies (VU.map nextUpDouble cs)
                      )
                      x.origin
                  )
            )
        )
    "ulps" ->
      Just
        ( Combine
            (const dimOne)
            ( \_ -> \case [a, b] -> exactDbl (ulpsBetween a.value b.value); _ -> exactDbl (0 / 0)
            )
        )
    -- The gap from 1 to the next double, 2⁻⁵².
    "eps" -> Just (Constant (\_ -> exactDbl 2.220446049250313e-16))
    "fma" ->
      Just
        ( Combine
            (\case d1 : d2 : _ -> dimMul d1 d2; _ -> dimOne)
            (\s -> \case [a, b, c] -> fmaD s a b c; _ -> exactDbl (0 / 0))
        )
    "isNaN" -> Just (Test (isNaN . (.value)))
    "isInfinite" -> Just (Test (isInfinite . (.value)))
    -- The copies' mean and deviation (design §8.2): with declared σ drawn,
    -- a Monte Carlo estimate of the mean and the standard uncertainty.
    "mid" -> Just (Each Keep False (copyStatistic "mid" meanOf))
    "sd" -> Just (Each Keep False (copyStatistic "sd" deviationOf))
    _ -> Nothing
