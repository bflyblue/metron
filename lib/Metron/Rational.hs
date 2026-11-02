-- | Rational coefficients and input samples, without affine forms.
module Metron.Rational (Rat (..)) where

import Data.List (transpose)
import Data.Maybe (fromMaybe, isNothing)
import Data.Text (Text)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Metron.Numerical.Approx qualified as Approx
import Metron.Numerical.Error (ArithError (..))
import Metron.Numerical.Identity (SourceId (..), originId)
import Metron.Numerical.Rational qualified as R
import Metron.Numerical.Sampling qualified as Sampling
import Metron.Numerical.Statistics qualified as Stats
import Metron.Remark (Cause (Draws))
import Metron.Scalar

data Rat = Rat
  { value :: !Rational
  , samples :: !(Maybe (V.Vector Rational))
  }
  deriving stock (Eq, Show)

plain :: Rational -> Rat
plain x = Rat x Nothing

unary :: (Rational -> Rational) -> Rat -> Rat
unary f x = Rat (f x.value) (fmap (V.map f) x.samples)

countOf :: [Rat] -> Maybe Int
countOf xs = case [V.length v | x <- xs, Just v <- [x.samples]] of
  n : _ -> Just n
  [] -> Nothing

values :: Int -> Rat -> V.Vector Rational
values n x = fromMaybe (V.replicate n x.value) x.samples

binary :: (Rational -> Rational -> Rational) -> Rat -> Rat -> Rat
binary f x y = Rat (f x.value y.value) $ do
  n <- countOf [x, y]
  pure (V.zipWith f (values n x) (values n y))

unaryM ::
  (Rational -> Either ArithError Rational) -> Rat -> Either ArithError Rat
unaryM f x = Rat <$> f x.value <*> traverse (traverse f) x.samples

binaryM ::
  (Rational -> Rational -> Either ArithError Rational) ->
  Rat ->
  Rat ->
  Either ArithError Rat
binaryM f x y = do
  nominal <- f x.value y.value
  samples <- case countOf [x, y] of
    Nothing -> Right Nothing
    Just n -> Just <$> V.zipWithM f (values n x) (values n y)
  Right (Rat nominal samples)

relation :: (Rational -> Rational -> Bool) -> Rat -> Rat -> Decision
relation f x y = Decision (f x.value y.value) $ do
  n <- countOf [x, y]
  let each = VU.fromList (V.toList (V.zipWith f (values n x) (values n y)))
  pure (Outcomes Draws mempty each)

statistic ::
  (Stats.InputSummary -> Maybe Rational) ->
  Settings ->
  Rat ->
  Either ArithError Rat
statistic f s x = case x.samples of
  Nothing -> Left (Domain "input statistics need sampled inputs")
  Just xs -> do
    summary <- Stats.summariseInputs s.precision (V.toList xs)
    maybe
      (Left (Domain "this input statistic needs more samples"))
      (Right . plain)
      (f summary)

-- Each matrix sample chooses its own pivots. No nominal decision discards a sample.
matrices ::
  ([[Rational]] -> Either ArithError [[Rational]]) ->
  [[Rat]] ->
  Either ArithError [[Rat]]
matrices f rows = do
  nominal <- f (map (map (.value)) rows)
  case countOf (concat rows) of
    Nothing -> Right (map (map plain) nominal)
    Just n -> do
      copies <-
        traverse (\i -> f (map (map (\x -> values n x V.! i)) rows)) [0 .. n - 1]
      let columns = transpose (map concat copies)
          joined = zipWith (\v xs -> Rat v (Just (V.fromList xs))) (concat nominal) columns
          width = case nominal of row : _ -> length row; [] -> 0
      Right [take width (drop (i * width) joined) | i <- [0 .. length nominal - 1]]

instance Scalar Rat where
  backendOf = RationalBackend
  literal _ = plain
  exactly x = if isNothing x.samples then Just x.value else Nothing
  distributionParameter = exactly
  addM _ = binary (+)
  subM _ = binary (-)
  mulM _ = binary (*)
  negM = unary negate
  absM _ = unary abs
  divM _ = binaryM R.divide
  powM _ x n = unaryM (`R.power` n) x
  sqrtM s = unaryM (R.squareRoot s.precision)
  logM s = unaryM (R.logarithm s.precision)
  tanM s = unaryM (R.tangent s.precision)
  asinM s = unaryM (R.arcSine s.precision)
  acosM s = unaryM (R.arcCosine s.precision)
  asinhM s = unaryM (R.inverseHyperbolicSine s.precision)
  expM s = unary (R.exponential s.precision)
  sinM s = unary (R.sine s.precision)
  cosM s = unary (R.cosine s.precision)
  atanM s = unary (R.arcTangent s.precision)
  sinhM s = unary (R.hyperbolicSine s.precision)
  coshM s = unary (R.hyperbolicCosine s.precision)
  tanhM s = unary (R.hyperbolicTangent s.precision)
  atan2M s = binaryM (R.arcTangent2 s.precision)
  piM s = plain (R.piAt s.precision)
  floorM _ = Right . unary (fromInteger . floor)
  ceilM _ = Right . unary (fromInteger . ceiling)
  roundM _ = Right . unary (fromInteger . round)
  relate _ rel x y =
    Right (relation (case rel of Lt -> (<); Le -> (<=); Gt -> (>); Ge -> (>=)) x y)
  equalM _ x y = Right (relation (==) x y)
  sizeOf = Just . (.value)
  stepProblem x
    | x.value == 0 || maybe False (V.any (== 0)) x.samples = Just "its step is zero"
    | otherwise = Nothing
  hintFactor = (.value)
  sampleM s origin distribution
    | s.samples <= 0 = Left (Domain "sample needs a positive input sample count")
    | otherwise = do
        let SourceId identity = originId origin
            input i = Sampling.draw s.precision s.seed identity i distribution
        nominal <- input 0
        copies <- traverse (input . globalOf s.copies) [0 .. memberCount s.copies - 1]
        Right (Rat nominal (Just (V.fromList copies)))
  determinantM _ _ rows = do
    result <- matrices (Right . (: []) . (: []) . determinant) rows
    case result of [[x]] -> Right x; _ -> Left (Domain "invalid determinant result")
  invertM _ _ = matrices inverse
  matrixExpM s _ = matrices (matrixExponential s.precision)
  choleskyM s what = matrices (cholesky s.precision what)
  restrictM places x =
    Rat
      x.value
      (fmap (\xs -> V.fromList [xs V.! i | i <- VU.toList places]) x.samples)
  scatterM _ n nominal parts =
    let baseline = maybe 0 (.value) nominal
        entries =
          [ (p, values (VU.length ps) x V.! i)
          | (ps, x) <- parts
          , (i, p) <- zip [0 ..] (VU.toList ps)
          ]
     in Rat baseline (Just (V.replicate n 0 V.// entries))
  own = \case
    "mid" -> Just (Each Keep False (statistic (Just . (.mean))))
    "sd" -> Just (Each Keep False (statistic (.deviation)))
    "covariance" -> Just (Covariance sampleCovariance)
    "crossCovariance" -> Just (Covariance sampleCovariance)
    _ -> Nothing

sampleCovariance :: Settings -> [Rat] -> [Rat] -> [[Either ArithError Rat]]
sampleCovariance _ as bs = [[entry a b | b <- bs] | a <- as]
 where
  entry a b = case countOf [a, b] of
    Nothing -> Left (Domain "covariance needs sampled inputs")
    Just n -> plain <$> Stats.covariance (V.toList (values n a)) (V.toList (values n b))

-- Exact division-free determinant. A 0x0 matrix has determinant one.
determinant :: [[Rational]] -> Rational
determinant rows = (if even (length rows) then id else negate) (last (coefficients rows))
 where
  coefficients [] = [1]
  coefficients (row : rest) =
    let lower = map (drop 1) rest
        column = map first rest
        powers = take (length rest) (iterate (\v -> map (`dot` v) lower) column)
        toeplitz = 1 : negate (first row) : map (negate . dot (drop 1 row)) powers
        previous = coefficients lower
     in [ sum [toeplitz !! (k - j) * c | (j, c) <- zip [0 ..] previous, j <= k]
        | k <- [0 .. length row]
        ]
  first [] = 0
  first (x : _) = x
  dot a b = sum (zipWith (*) a b)

inverse :: [[Rational]] -> Either ArithError [[Rational]]
inverse a =
  go
    0
    [ row ++ [if i == j then 1 else 0 | j <- [0 .. n - 1]] | (i, row) <- zip [0 ..] a
    ]
 where
  n = length a
  go k rows
    | k == n = Right (map (drop n) rows)
    | otherwise = case [i | i <- [k .. n - 1], rows !! i !! k /= 0] of
        [] -> Left (Domain "inverse of a singular matrix")
        i : _ ->
          let pivot = map (/ (rows !! i !! k)) (rows !! i)
              exchanged =
                [ if j == k then pivot else if j == i then rows !! k else row
                | (j, row) <- zip [0 ..] rows
                ]
              cleared =
                [ if j == k then pivot else zipWith (-) row (map (* (row !! k)) pivot)
                | (j, row) <- zip [0 ..] exchanged
                ]
           in go (k + 1) cleared

cholesky :: Int -> Text -> [[Rational]] -> Either ArithError [[Rational]]
cholesky p what a
  | a /= transpose a = Left (Domain what)
  | otherwise = rows [] 0
 where
  n = length a
  rows done i
    | i == n = Right done
    | otherwise = do
        new <- entries done [] i 0
        rows (done ++ [new]) (i + 1)
  entries done prefix i j
    | j == n = Right prefix
    | j > i = entries done (prefix ++ [0]) i (j + 1)
    | otherwise = do
        let other = if i == j then prefix else done !! j
            rest = a !! i !! j - sum (zipWith (*) (take j prefix) (take j other))
        entry <-
          if i == j
            then
              if rest <= 0
                then Left (Domain "cholesky needs a positive-definite matrix")
                else R.squareRoot p rest
            else R.divide rest (done !! j !! j)
        entries done (prefix ++ [entry]) i (j + 1)

-- Scaling and squaring with a precision-controlled Taylor sum.
-- Rational rounding here controls approximation cost, not uncertainty bounds.
matrixExponential :: Int -> [[Rational]] -> Either ArithError [[Rational]]
matrixExponential p input = do
  summed <- series 1 identity identity
  Right (iterate (\x -> multiply x x) summed !! halvings)
 where
  n = length input
  identity = [[if i == j then 1 else 0 | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
  norm = maximum . (0 :) . map (sum . map abs)
  halvings = length (takeWhile (> (1 / 2)) (iterate (/ 2) (norm input)))
  scaled = map (map (/ (2 ^ halvings))) input
  shorten x = Approx.roundAt (Approx.precisionExponent (p + 8) x) x
  multiply a b = [[shorten (sum (zipWith (*) row column)) | column <- transpose b] | row <- a]
  plus = zipWith (zipWith (\x y -> shorten (x + y)))
  tolerance = 1 / 10 ^ (max 1 p + 4)
  series k term total
    | k > max 64 (4 * p + 64) =
        Left (Domain "matrix exponential did not converge at this precision")
    | otherwise =
        let next = map (map (\x -> shorten (x / fromIntegral k))) (multiply term scaled)
            result = plus total next
         in if norm next <= tolerance then Right result else series (k + 1) next result
