{-# LANGUAGE MagicHash #-}

-- | IEEE arithmetic with separately indexed input and rounding runs.
module Metron.Double (
  Dbl (..),
  Estimate (..),
  Layout (..),
  carriesDraws,
  showDouble,
  originNote,
  sampleNote,
  clusterNote,
  copiesOf,
) where

import Control.Monad (foldM)
import Data.Bits (testBit)
import Data.ByteString.Char8 qualified as BS
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (transpose)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Unboxed qualified as VU
import GHC.Exts (Double (D#), fmaddDouble#)
import GHC.Float (castDoubleToWord64, castWord64ToDouble, floatToDigits)
import Metron.Dimension (dimMul, dimOne)
import Metron.Numerical.Error (ArithError (..))
import Metron.Numerical.Identity (SourceId (..), originId)
import Metron.Numerical.Sampling qualified as Sampling
import Metron.Numerical.Statistics qualified as Stats
import Metron.Remark (Cause (..))
import Metron.Scalar

-- Each group is [ordinary, rounding 0, ..., rounding R-1].
data Layout = Layout {rounds :: !Int, sampled :: !Bool}
  deriving stock (Eq, Show)
instance Semigroup Layout where
  a <> b = Layout (max a.rounds b.rounds) (a.sampled || b.sampled)
instance Monoid Layout where mempty = Layout 0 False

data Estimate = NoSamples | Copies !Layout !(VU.Vector Double)
  deriving stock (Eq, Show)
data Dbl = Dbl {value :: !Double, estimate :: !Estimate, origin :: !(Maybe Text)}
  deriving stock (Show)
instance Eq Dbl where
  a == b = a.value == b.value && a.estimate == b.estimate

layoutOf :: Dbl -> Layout
layoutOf x = case x.estimate of NoSamples -> mempty; Copies l _ -> l
carriesDraws :: Dbl -> Bool
carriesDraws = (.sampled) . layoutOf
anyCopy :: (Double -> Bool) -> Dbl -> Bool
anyCopy f x = case x.estimate of
  NoSamples -> False
  Copies _ cs -> VU.any f cs
exactDbl :: Double -> Dbl
exactDbl v = Dbl v NoSamples Nothing
finite :: Double -> Bool
finite x = not (isNaN x || isInfinite x)
predicate :: (Double -> Bool) -> Dbl -> Decision
predicate f x = Decision (f x.value) $ case x.estimate of
  NoSamples -> Nothing
  Copies _ cs -> Just (Outcomes Draws mempty (VU.map f cs))
eta :: Double
eta = 5e-324
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

-- Inputs and roundings use separate key domains; operand values are not identities.
coin :: Settings -> Int -> Int -> Bool
coin s global op =
  let (i, j) = global `divMod` (s.rounds + 1)
   in testBit
        ( Sampling.roundingWord
            s.seed
            (s.occurrence <> BS.pack (":" ++ show op))
            0
            i
            (j - 1)
        )
        0
randomAt :: Settings -> Int -> Bool
randomAt s global = s.rounding == RoundRandom && s.rounds > 0 && global `mod` (s.rounds + 1) /= 0
roundTo :: Bool -> Double -> Ordering -> Double
roundTo upward r = \case
  _ | not (finite r) -> r
  EQ -> r
  GT -> if upward then nextUpDouble r else r
  LT -> if upward then r else nextDownDouble r
wobble :: Bool -> Double -> Double
wobble upward r
  | not (finite r) = r
  | upward = nextUpDouble r
  | otherwise = nextDownDouble r

copiesOf :: Int -> Dbl -> VU.Vector Double
copiesOf n x = case x.estimate of Copies _ cs -> cs; NoSamples -> VU.replicate n x.value

-- A constant broadcasts by value when reading one realization. Constructing
-- its whole broadcast vector here would allocate once per output element.
copyAt :: Int -> Dbl -> Double
copyAt i x = case x.estimate of Copies _ cs -> cs VU.! i; NoSamples -> x.value
copyCount :: [Dbl] -> Maybe Int
copyCount xs = listToMaybe [VU.length cs | x <- xs, Copies _ cs <- [x.estimate]]
originOf :: [Dbl] -> Double -> Text -> Maybe Text
originOf xs z description = case mapMaybe (.origin) xs of
  o : _ -> Just o
  []
    | not (finite z) && all (finite . (.value)) xs -> Just description
    | otherwise -> Nothing
operation ::
  Settings ->
  Int ->
  Text ->
  ([Double] -> Double) ->
  (Bool -> [Double] -> Double) ->
  [Dbl] ->
  Dbl
operation s op name ordinary stochastic xs =
  let v = ordinary (map (.value) xs)
      estimate = case copyCount xs of
        Nothing -> NoSamples
        Just n ->
          Copies
            (foldMap layoutOf xs)
            ( VU.generate n $ \k ->
                let global = globalOf s.copies k; ys = map (copyAt k) xs
                 in if randomAt s global then stochastic (coin s global op) ys else ordinary ys
            )
   in Dbl v estimate (originOf xs v name)
binary ::
  Settings ->
  Int ->
  Text ->
  (Double -> Double -> (Double, Ordering)) ->
  Dbl ->
  Dbl ->
  Dbl
binary s op name side x y =
  operation
    s
    op
    name
    (\case [a, b] -> fst (side a b); _ -> 0 / 0)
    (\c -> \case [a, b] -> uncurry (roundTo c) (side a b); _ -> 0 / 0)
    [x, y]
addD, subD, mulD, divD :: Settings -> Dbl -> Dbl -> Dbl
addD s = binary s 1 "+" sumSide
subD s = binary s 2 "-" (\a b -> sumSide a (negate b))
mulD s = binary s 3 "*" productSide
divD s = binary s 4 "/" quotientSide
exactly1 :: (Double -> Double) -> Dbl -> Dbl
exactly1 f x =
  Dbl
    (f x.value)
    (case x.estimate of NoSamples -> NoSamples; Copies l cs -> Copies l (VU.map f cs))
    x.origin
unary ::
  Settings ->
  Int ->
  Text ->
  (Double -> Double) ->
  (Bool -> Double -> Double) ->
  Dbl ->
  Dbl
unary s op name f random x =
  operation
    s
    op
    name
    (\case [a] -> f a; _ -> 0 / 0)
    (\c -> \case [a] -> random c a; _ -> 0 / 0)
    [x]
libm :: Settings -> Int -> Text -> (Double -> Double) -> Dbl -> Dbl
libm s op name f = unary s op name f (\c x -> wobble c (f x))
sqrtD :: Settings -> Dbl -> Dbl
sqrtD s = unary s 5 "sqrt" sqrt (\c a -> uncurry (roundTo c) (sqrtSide a))
fmaD :: Settings -> Dbl -> Dbl -> Dbl -> Dbl
fmaD s a b c =
  operation
    s
    18
    "fma"
    (\case [x, y, z] -> fmaDouble x y z; _ -> 0 / 0)
    ( \up -> \case
        [x, y, z] ->
          let v = fmaDouble x y z
              side =
                if all finite [x, y, z, v]
                  then compare (toRational x * toRational y + toRational z) (toRational v)
                  else EQ
           in roundTo up v side
        _ -> 0 / 0
    )
    [a, b, c]
literalD :: Settings -> Rational -> Dbl
literalD s r = constantD s 0 v side
 where
  v = fromRational r; side = if finite v then compare r (toRational v) else EQ
constantD :: Settings -> Int -> Double -> Ordering -> Dbl
constantD s op v side = Dbl v estimate (if finite v then Nothing else Just "literal conversion")
 where
  estimate
    | s.rounds > 0 =
        Copies
          (Layout s.rounds False)
          ( VU.generate (memberCount s.copies) $ \k ->
              let global = globalOf s.copies k
               in if randomAt s global then roundTo (coin s global op) v side else v
          )
    | otherwise = NoSamples

ordinaryCopies :: Dbl -> VU.Vector Double
ordinaryCopies x = case x.estimate of
  NoSamples -> VU.singleton x.value
  Copies l cs -> VU.ifilter (\i _ -> i `mod` (l.rounds + 1) == 0) cs
statistic ::
  Text ->
  (Stats.InputSummary -> Maybe Rational) ->
  Settings ->
  Dbl ->
  Either ArithError Dbl
statistic name f s x
  | s.rounds > 0 =
      Left (Domain "rounding analysis of a sample reduction is not supported")
  | not (carriesDraws x) = Left (Domain (name <> " needs sampled inputs"))
  | not (VU.all finite values) =
      Left (Domain (name <> " is unavailable: nonfinite input components"))
  | otherwise = do
      summary <- Stats.summariseInputs s.precision (map toRational (VU.toList values))
      maybe
        (Left (Domain (name <> " needs at least two input samples")))
        (Right . exactDbl . fromRational)
        (f summary)
 where
  values = ordinaryCopies x

sampleNote :: ([Text] -> Text) -> [Dbl] -> Maybe Text
sampleNote layout xs
  | null copied || (not l.sampled && l.rounds == 0) = Nothing
  | otherwise = Just (T.intercalate "; " (inputNotes ++ roundingNotes))
 where
  copied = [(grid, cs) | x <- xs, Copies grid cs <- [x.estimate]]
  l = foldMap fst copied
  n = maximum (0 : map (VU.length . snd) copied)
  starts = [0, l.rounds + 1 .. n - 1]
  groups x = [[copyAt j x | j <- [i .. min (n - 1) (i + l.rounds)]] | i <- starts]
  ordinary x = map (`copyAt` x) starts
  finiteInputs = all (all finite . ordinary) xs
  summaries = [Stats.summariseInputs 24 (map toRational (ordinary x)) | x <- xs]
  shown f = layout [either (const "unavailable") f q | q <- summaries]
  showR = showDouble . fromRational
  inputNotes
    | not l.sampled = []
    | not finiteInputs =
        [ "Monte Carlo: statistics unavailable; "
            <> tshow (sum [length (filter (not . finite) (ordinary x)) | x <- xs])
            <> " nonfinite input components"
        ]
    | otherwise =
        [ "Monte Carlo: mean "
            <> shown (showR . (.mean))
            <> ", sd "
            <> shown (maybe "unavailable" showR . (.deviation))
            <> ", outcome 95% ["
            <> shown (showR . (.lower95))
            <> ", "
            <> shown (showR . (.upper95))
            <> "]; "
            <> tshow (n `div` (l.rounds + 1))
            <> " input samples"
        ]
  roundingSummaries =
    [ Stats.summariseRounding
        24
        [(toRational v, map toRational vs) | v : vs <- groups x]
    | x <- xs
    ]
  shownR f = layout [either (const "unavailable") f q | q <- roundingSummaries]
  roundingNotes
    | l.rounds == 0 = []
    | not (all (VU.all finite . copiesOf n) xs) =
        ["stochastic rounding: diagnostics unavailable; nonfinite runs present"]
    | otherwise =
        [ "stochastic rounding: typical spread "
            <> shownR (showR . (.typicalSpread))
            <> ", RMS displacement "
            <> shownR (showR . (.baselineDisplacement))
            <> ", "
            <> tshow l.rounds
            <> " repetitions per input"
            <> ( if all (either (const False) (not . (.variationObserved))) roundingSummaries
                   then "; no variation observed"
                   else ""
               )
            <> "; distribution generation excluded; libm perturbations are heuristic"
        ]
clusterNote :: ([Text] -> Text) -> [Dbl] -> Text
clusterNote layout xs = fromMaybe "" (sampleNote layout xs)
tshow :: (Show a) => a -> Text
tshow = T.pack . show

instance Scalar Dbl where
  backendOf = DoubleBackend
  literal = literalD
  exactly x
    | finite x.value
        && VU.all
          (== x.value)
          (case x.estimate of NoSamples -> VU.empty; Copies _ cs -> cs) =
        Just (toRational x.value)
    | otherwise = Nothing
  addM = addD
  subM = subD
  mulM = mulD
  negM = exactly1 negate
  absM _ = exactly1 abs
  divM s x y = Right (divD s x y)
  powM s x n = Right (powD s x n)
  sqrtM s = Right . sqrtD s
  logM s = Right . libm s 7 "log" log
  tanM s = Right . libm s 10 "tan" tan
  asinM s = Right . libm s 11 "asin" asin
  acosM s = Right . libm s 12 "acos" acos
  asinhM s = Right . libm s 23 "asinh" asinh
  expM s = libm s 6 "exp" exp
  sinM s = libm s 8 "sin" sin
  cosM s = libm s 9 "cos" cos
  atanM s = libm s 13 "atan" atan
  sinhM s = libm s 14 "sinh" sinh
  coshM s = libm s 15 "cosh" cosh
  tanhM s = libm s 16 "tanh" tanh
  atan2M s y x =
    Right
      ( operation
          s
          17
          "atan2"
          (\case [a, b] -> atan2 a b; _ -> 0 / 0)
          (\c -> \case [a, b] -> wobble c (atan2 a b); _ -> 0 / 0)
          [y, x]
      )
  piM s = constantD s 19 pi GT
  floorM _ = Right . exactly1 (whole floor)
  ceilM _ = Right . exactly1 (whole ceiling)
  roundM _ = Right . exactly1 (whole round)
  relate _ rel x y = Right (decide (case rel of Lt -> (<); Le -> (<=); Gt -> (>); Ge -> (>=)) x y)
  equalM _ x y = Right (decide (==) x y)
  sizeOf _ = Nothing
  stepProblem x
    | x.value == 0 || anyCopy (== 0) x = Just "its step is zero"
    | not (finite x.value) || anyCopy (not . finite) x =
        Just "its step is not finite"
    | otherwise = Nothing
  hintFactor x = if finite x.value then toRational x.value else 0
  distributionParameter x =
    if finite x.value && not (carriesDraws x)
      then Just (toRational x.value)
      else Nothing
  sampleM s origin distribution = do
    let SourceId identity = originId origin
        input i = Sampling.draw s.precision s.seed identity i distribution
        convert global r =
          let v = fromRational r; side = if finite v then compare r (toRational v) else EQ
           in if randomAt s global then roundTo (coin s global 24) v side else v
    let globals = map (globalOf s.copies) [0 .. memberCount s.copies - 1]
        indices = IntSet.toAscList (IntSet.fromList (0 : map (`div` (s.rounds + 1)) globals))
    draws <- IntMap.fromList <$> traverse (\i -> (i,) <$> input i) indices
    let drawn i =
          maybe (Left (Domain "missing input realization")) Right (IntMap.lookup i draws)
    baseline <- drawn 0
    values <-
      traverse
        (\global -> convert global <$> drawn (global `div` (s.rounds + 1)))
        globals
    Right
      ( Dbl
          (fromRational baseline)
          (Copies (Layout s.rounds True) (VU.fromList values))
          Nothing
      )
  determinantM s _ rows = Right (determinantD s rows)
  invertM s n rows = Right (invertD s n rows)
  matrixExpM s n rows = Right (matrixExpD s n rows)
  choleskyM = choleskyD
  restrictM places x = case x.estimate of
    Copies l cs -> x{estimate = Copies l (VU.backpermute cs places)}
    NoSamples -> x
  scatterM = scatterD
  own = \case
    "mean" -> Just (Each Keep False (statistic "mean" (Just . (.mean))))
    "sd" -> Just (Each Keep False (statistic "sd" (.deviation)))
    "covariance" -> Just (Covariance sampleCovariance)
    "crossCovariance" -> Just (Covariance sampleCovariance)
    "nextUp" -> Just (Each Keep False (\_ -> Right . exactly1 nextUpDouble))
    "eps" -> Just (Constant (\_ -> exactDbl 2.220446049250313e-16))
    "fma" ->
      Just
        ( Combine
            (\case a : b : _ -> dimMul a b; _ -> dimOne)
            (\s -> \case [a, b, c] -> fmaD s a b c; _ -> exactDbl (0 / 0))
        )
    "ulps" ->
      Just
        ( Combine
            (const dimOne)
            ( \_ -> \case [a, b] -> exactDbl (ulpsBetween a.value b.value); _ -> exactDbl (0 / 0)
            )
        )
    "isNaN" -> Just (Test (predicate isNaN))
    "isInfinite" -> Just (Test (predicate isInfinite))
    _ -> Nothing
sampleCovariance :: Settings -> [Dbl] -> [Dbl] -> [[Either ArithError Dbl]]
sampleCovariance s as bs = [[entry a b | b <- bs] | a <- as]
 where
  entry a b
    | s.rounds > 0 =
        Left (Domain "rounding analysis of a sample reduction is not supported")
    | not (carriesDraws a || carriesDraws b) =
        Left (Domain "covariance needs sampled inputs")
    | otherwise = do
        let n = fromMaybe 1 (copyCount [a, b])
            values x = VU.ifilter (\i _ -> i `mod` (s.rounds + 1) == 0) (copiesOf n x)
            xs = values a
            ys = values b
        if VU.all finite xs && VU.all finite ys
          then
            exactDbl . fromRational
              <$> Stats.covariance (map toRational (VU.toList xs)) (map toRational (VU.toList ys))
          else Left (Domain "covariance is unavailable: nonfinite input components")

whole :: (Double -> Integer) -> Double -> Double
whole f x = if finite x then fromInteger (f x) else x
decide :: (Double -> Double -> Bool) -> Dbl -> Dbl -> Decision
decide f x y =
  Decision
    (f x.value y.value)
    ( fmap
        (\n -> Outcomes Draws mempty (VU.zipWith f (copiesOf n x) (copiesOf n y)))
        (copyCount [x, y])
    )

sumSide, productSide, quotientSide :: Double -> Double -> (Double, Ordering)
sumSide a b =
  let s = a + b
      bb = s - a
   in (s, if finite s then compare ((a - (s - bb)) + (b - bb)) 0 else EQ)
productSide a b =
  let p = a * b
      residual = fmaDouble a b (negate p)
   in ( p
      , if finite p
          then
            if residual /= 0
              then compare residual 0
              else compare (toRational a * toRational b) (toRational p)
          else EQ
      )
quotientSide a b =
  let q = a / b
      r = fmaDouble (negate q) b a
   in ( q
      , if finite q && finite a && finite b && b /= 0
          then
            if r /= 0
              then compare (r * signum b) 0
              else compare (toRational a / toRational b) (toRational q)
          else EQ
      )

sqrtSide :: Double -> (Double, Ordering)
sqrtSide a =
  let r = sqrt a
      residual = fmaDouble (negate r) r a
   in ( r
      , if finite r
          then
            if residual /= 0
              then compare residual 0
              else compare (toRational a) (toRational r * toRational r)
          else EQ
      )

powD :: Settings -> Dbl -> Integer -> Dbl
powD s x n
  | n < 0 = divD s (exactDbl 1) (powD s x (negate n))
  | n == 0 = exactly1 (const 1) x
  | otherwise = go 0 x n
 where
  go depth b k
    | even k = go (depth + 1) (mulD (atIndex s depth) b b) (k `quot` 2)
    | k == 1 = b
    | otherwise = acc (depth + 1) (mulD (atIndex s depth) b b) (k `quot` 2) b
  acc depth b k z
    | even k = acc (depth + 1) (mulD (atIndex s (2 * depth)) b b) (k `quot` 2) z
    | k == 1 = mulD (atIndex s (2 * depth + 1)) b z
    | otherwise =
        acc
          (depth + 1)
          (mulD (atIndex s (2 * depth)) b b)
          (k `quot` 2)
          (mulD (atIndex s (2 * depth + 1)) b z)

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

originNote :: [Dbl] -> Maybe Text
originNote xs = case [(x.value, o) | x <- xs, not (finite x.value), Just o <- [x.origin]] of
  (v, o) : _ ->
    Just
      ( (if isNaN v then "the first NaN came from " else "the first infinity came from ")
          <> o
      )
  [] -> Nothing

-- Indexed contractions give every elementary operation its own random key.
dotD :: Settings -> [Dbl] -> [Dbl] -> Dbl
dotD s xs ys = foldl' step (exactDbl 0) (zip3 [0 ..] xs ys)
 where
  step acc (k, x, y) = let p = atIndex s k in addD p acc (mulD p x y)

determinantD :: Settings -> [[Dbl]] -> Dbl
determinantD _ [[x]] = x
determinantD s rows = if even (length rows) then result else exactly1 negate result
 where
  result = last (coefficients s rows)
  -- Berkowitz avoids pivot decisions and preserves every realization.
  coefficients _ [] = [exactDbl 1]
  coefficients cfg (r : rs) =
    let lower = map (drop 1) rs
        column = map headOr rs
        powers =
          take
            (length rs)
            ( scanl
                (\v k -> [dotD (atIndex (atIndex cfg k) i) row v | (i, row) <- zip [0 ..] lower])
                column
                [0 ..]
            )
        toeplitz =
          exactDbl 1
            : exactly1 negate (headOr r)
            : [ exactly1 negate (dotD (atIndex (atIndex cfg (-1)) k) (drop 1 r) v)
              | (k, v) <- zip [0 ..] powers
              ]
        previous = coefficients (atIndex cfg (-2)) lower
     in [ dotD
            (atIndex (atIndex cfg (-3)) k)
            [toeplitz !! (k - j) | (j, _) <- zip [0 ..] previous, j <= k]
            [c | (j, c) <- zip [0 ..] previous, j <= k]
        | k <- [0 .. length r]
        ]

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

{- | Gauss–Jordan inversion, pivoting separately on the nominal values and
each copy. Singular copies retain their IEEE nonfinite results.
-}
invertD :: Settings -> Int -> [[Dbl]] -> [[Dbl]]
invertD s n = perRealization (`invertRows` n) s

-- Pivoting and scaling decisions belong to each realization, including
-- diagnostic paths. Reassembly keeps the original global grid coordinates.
perRealization ::
  (Settings -> [[Dbl]] -> [[Dbl]]) -> Settings -> [[Dbl]] -> [[Dbl]]
perRealization kernel s a
  | Just count <- copyCount (concat a) =
      let nominal = kernel s (map (map (\x -> x{estimate = NoSamples})) a)
          sample i =
            let one x =
                  let v = copyAt i x
                   in x{value = v, estimate = Copies (layoutOf x) (VU.singleton v)}
                settings = s{samples = 1, copies = Range (globalOf s.copies i) 1}
             in kernel settings (map (map one) a)
          samples = map (concat . sample) [0 .. count - 1]
          joined =
            [ x
                { estimate =
                    Copies
                      (foldMap layoutOf (concat a))
                      (VU.fromList [copyAt 0 (row !! k) | row <- samples])
                }
            | (k, x) <- zip [0 ..] (concat nominal)
            ]
          n = length a
       in [take n (drop (i * n) joined) | i <- [0 .. n - 1]]
  | otherwise = kernel s a

invertRows :: Settings -> Int -> [[Dbl]] -> [[Dbl]]
invertRows s n a = map (drop n) (eliminate 0 augmented)
 where
  augmented =
    [ row ++ [exactDbl (if i == j then 1 else 0) | j <- [0 .. n - 1]]
    | (i, row) <- zip [0 :: Int ..] a
    ]
  eliminate c rows
    | c >= n = rows
    | otherwise =
        let (above, rest) = splitAt c rows
            k = maybe 0 fst (pivotOf (map (map pivotValue . drop c) rest))
            prow = rowAt rest k
            others = above ++ [r | (i, r) <- zip [0 ..] rest, i /= k]
            p = entryAt prow c
            prow' = zipWith (\j x -> divD (atIndex (atIndex s c) j) x p) [0 ..] prow
            clear i r =
              let f = entryAt r c
               in zipWith3
                    ( \j x y -> let cfg = atIndex (atIndex (atIndex s c) i) j in subD cfg x (mulD cfg f y)
                    )
                    [0 ..]
                    r
                    prow'
            (before, after) = splitAt c (zipWith clear [0 ..] others)
         in eliminate (c + 1) (before ++ [prow'] ++ after)
  pivotValue x = case x.estimate of
    Copies _ cs | VU.length cs == 1 -> x{value = cs VU.! 0}
    _ -> x

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
matrixExpD s n = perRealization (`matrixExpRows` n) s

matrixExpRows :: Settings -> Int -> [[Dbl]] -> [[Dbl]]
matrixExpRows s n a =
  foldl' (\m k -> product' (atIndex s (100 + k)) m m) series [0 .. halvings - 1]
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
  product' cfg x y =
    [ [ foldl'
          ( \acc (k, u, v) ->
              let p = atIndex (atIndex cfg (i * n + j)) k
               in addD p acc (mulD p u v)
          )
          (exactDbl 0)
          (zip3 [0 ..] row col)
      | (j, col) <- zip [0 ..] (transpose y)
      ]
    | (i, row) <- zip [0 ..] x
    ]
  series =
    fst
      ( foldl'
          ( \(acc, term) k ->
              let term' =
                    [ [ divD (atIndex (atIndex (atIndex s k) i) j) v (exactDbl (fromIntegral k))
                      | (j, v) <- zip [0 ..] row
                      ]
                    | (i, row) <- zip [0 ..] (product' (atIndex s k) term scaled)
                    ]
               in ( [ [ addD (atIndex (atIndex (atIndex s (-k)) i) j) x y
                      | (j, x, y) <- zip3 [0 ..] ar tr
                      ]
                    | (i, ar, tr) <- zip3 [0 ..] acc term'
                    ]
                  , term'
                  )
          )
          (identity, identity)
          [1 .. 20 :: Int]
      )

{- | The lower Cholesky factor, @L Lᵀ = A@. Symmetry and positive pivots
must hold nominally and in every copy; invalid matrices are refused.
-}
choleskyD :: Settings -> Text -> [[Dbl]] -> Either ArithError [[Dbl]]
choleskyD s what a
  | or
      [ not (same (entryAt (rowAt a i) j) (entryAt (rowAt a j) i))
      | i <- [0 .. n - 1]
      , j <- [i + 1 .. n - 1]
      ] =
      Left (Domain what)
  | otherwise = foldM row [] [0 .. n - 1]
 where
  n = length a
  same x y =
    x.value == y.value
      && maybe True (\k -> copiesOf k x == copiesOf k y) (copyCount [x, y])
  positive x =
    x.value > 0 && case x.estimate of
      NoSamples -> True
      Copies _ cs -> VU.all (> 0) cs
  row done i = do
    let entry prev j
          | j > i = Right (prev ++ [exactDbl 0])
          | otherwise =
              let other = if j == i then prev else rowAt done j
                  p = atIndex (atIndex s i) j
                  rest = subD p (entryAt (rowAt a i) j) (dotD p (take j prev) (take j other))
               in if j == i
                    then
                      if positive rest
                        then Right (prev ++ [sqrtD p rest])
                        else
                          Left
                            ( Domain
                                "cholesky needs a positive-definite matrix: a pivot is nonpositive"
                            )
                    else Right (prev ++ [divD p rest (entryAt (rowAt done j) j)])
    new <- foldM entry [] [0 .. n - 1]
    pure (done ++ [new])

-- Splitting the copies ------------------------------------------------------------------

{- | The numbers the groups of a split computed, put back together copy by
copy (design §8.2): each group's copies at their places among @n@. The
value is the nominal group's, the IEEE result at the nominal inputs; an
evaluation off the nominal path has none, and its value is a NaN, the
same in every batch, which nothing reads. Only draws split the copies,
so the result is a Monte Carlo sample: its copies carry draws, whatever
each group's did (a group's literal, alone, carries none).
-}
scatterD :: Settings -> Int -> Maybe Dbl -> [(VU.Vector Int, Dbl)] -> Dbl
scatterD settings n nominal parts =
  Dbl
    (maybe (0 / 0) (.value) nominal)
    ( Copies
        (Layout settings.rounds settings.inputSampling <> foldMap (layoutOf . snd) parts)
        ( VU.update
            (VU.replicate n (0 / 0))
            (VU.concat [VU.zip ps (copiesOf (VU.length ps) x) | (ps, x) <- parts])
        )
    )
    (nominal >>= (.origin))
