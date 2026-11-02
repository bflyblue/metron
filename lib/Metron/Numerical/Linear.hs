-- | Matrix algorithms over affine magnitudes, independent of language values and dimensions.
module Metron.Numerical.Linear (
  determinant,
  invert,
  matrixExp,
  choleskyRows,
) where

import Control.Monad (foldM)
import Data.List (transpose)
import Data.Map.Strict qualified as Map (null)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T (pack)
import Metron.Affine (
  ArithError (Domain, Undecided),
  Decide,
  Magnitude (Exact),
  Precision,
  addM,
  boundRadius,
  compareM,
  coscSqM,
  divM,
  enclose,
  isExact,
  midpoint,
  mulM,
  scaleM,
  sincSqM,
  skewOf,
  sqrtM,
  statCoefficients,
  subM,
 )

{- | A usable pivot: the entry of largest midpoint among those whose
enclosure excludes zero, by row position.
-}
pivotIn :: Int -> [Magnitude] -> Maybe Int
pivotIn from column =
  case [(abs (midpoint x), i) | (i, x) <- zip [0 ..] column, i >= from, excludesZero x] of
    [] -> Nothing
    cands -> Just (snd (maximum cands))
 where
  excludesZero x = midpoint x - boundRadius x > 0 || midpoint x + boundRadius x < 0

singular :: Text -> [Magnitude] -> ArithError
singular what column
  | all (== Exact 0) column =
      Metron.Affine.Domain (what <> " of a singular matrix")
  | otherwise =
      Metron.Affine.Undecided (what <> " of a matrix whose enclosure may be singular")

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
                go (k + 1) (scaleM p sign (mulM p acc pv)) reduced
  eliminate k pivotRow pv r = do
    f <- divM p (r !! k) pv
    pure (zipWith (\a b -> subM p a (mulM p f b)) r pivotRow)

{- | Inverse by Gauss-Jordan elimination on the augmented matrix. Its last
step is linear, a row less a multiple of another, which never rounds
and scales by every exact entry it meets (@1/7@, @1/11@): an entry that
is not exact is shortened at the end, as any operation's result is
(design §3.2.8), its rounding a nudge of its own named by its position.
-}
invert :: Precision -> Int -> [[Magnitude]] -> Either ArithError [[Magnitude]]
invert p n rows0 =
  go
    0
    [ r ++ [if i == j then Exact 1 else Exact 0 | j <- [0 .. n - 1]]
    | (i, r) <- zip [0 ..] rows0
    ]
 where
  settle i j = \case
    x@(Exact _) -> x
    x -> enclose "inverse" p (Exact (fromIntegral (i * n + j)) : concat rows0) 0 x
  go k rows
    | k == n =
        Right
          [ zipWith (settle i) [0 :: Int ..] (drop n row)
          | (i, row) <- zip [0 :: Int ..] rows
          ]
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
                let eliminate r = let f = r !! k in zipWith (\a b -> subM p a (mulM p f b)) r normalised
                go
                  (k + 1)
                  [if j == k then normalised else eliminate r | (j, r) <- zip [0 ..] swapped]

{- | The exponential of a square matrix of enclosures (design §3.3).

/A single plane/. @B@ is split into its antisymmetric part
@A = (B − Bᵀ) / 2@ and its symmetric part @S = (B + Bᵀ) / 2@, as affine
forms. For every matrix in the enclosure the real @A@ is antisymmetric,
whatever its forms look like, and when it is a single plane, @A³ = −t A@
with @t = Σ_{i<j} a_ij²@, then @A^(k+2) = −t Aᵏ@ and the series collapses
to Rodrigues' formula @I + f(t) A + g(t) A²@ with @f = sin θ / θ@ and
@g = (1 − cos θ) / θ²@, @θ² = t@, both entire in @t@ ("Metron.Affine"
'sincSqM', 'coscSqM'), so @θ@ near zero divides by nothing. Every
antisymmetric matrix is a single plane when @n ≤ 3@; beyond, an exact @A@
is checked exactly and an uncertain one takes the series. When @S@ is
exactly zero this is @exp B@. When it is not but its bound @σ@ (the
∞-norm of @|midpoint| + bound radius@, which bounds @‖S‖₂@ for a symmetric
matrix) is below @10^−p@, as it is when @B@ was built antisymmetric
through a product whose two entries got two fresh nudges (@θ * (b ∧ a) /
norm c@), then @‖exp (A + S) − exp A‖₂ ≤ e^σ − 1 ≤ 2σ@ (@exp (τA)@ is
orthogonal, and the logarithmic norm of @A + S@ is at most @σ@), and every
entry gets @2σ@ as a fresh nudge of its own.

/Otherwise/, the series with scaling and squaring. @β@ is the ∞-norm (the
largest row sum) of @|midpoint| + bound radius@, an exact rational that bounds
@‖B‖∞@ for every matrix in the enclosure; it is submultiplicative and
bounds every entry. With @s@ the least power for which @β' = β / 2ˢ ≤ 1/2@
and @A = B / 2ˢ@ (exact scaling), the sum of @Aᵏ / k!@ for @k < K@ is
formed in affine arithmetic, @K@ the first with @β'ᴷ / K! @ below
@10^−(p+4+s)@ (a guard digit per squaring). The remainder
@Σ_{k≥K} Aᵏ / k!@ has ∞-norm at most @β'ᴷ / K! · 1 / (1 − β' / (K+1))
≤ 2 β'ᴷ / K!@, so every entry gets that as a fresh bound nudge of its own
(named with its position, so that no two entries share an unknown), and
the result is squared @s@ times, rigorously. @β = 0@ is the zero matrix,
whose exponential is exactly @I@.
-}
matrixExp ::
  Precision -> Int -> [[Magnitude]] -> Either ArithError [[Magnitude]]
matrixExp p n b
  | any (any (\x -> not (Map.null (statCoefficients x)) || isJust (skewOf x))) b =
      Left
        ( Metron.Affine.Domain
            "expm with statistical uncertainty is not supported; its statistical remainder cannot yet be propagated"
        )
  | singlePlane && sigma == 0 = rodrigues
  | singlePlane && sigma <= 10 ^^ negate (p - 4) =
      positioned "expm: symmetric part" (2 * sigma) <$> rodrigues
  | beta == 0 = Right identity
  | otherwise =
      Right
        (iterate (\m -> matMul m m) (positioned "expm" remainder partial) !! s)
 where
  identity =
    [[if i == j then Exact 1 else Exact 0 | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
  at i j = b !! i !! j
  matMul x y = [[sumM p (zipWith (mulM p) row col) | col <- transpose y] | row <- x]
  -- An independent fresh nudge on every entry, named with its position.
  positioned name size m =
    [ [ enclose name p (Exact (fromIntegral (i * n + j)) : concat b) size x
      | (j, x) <- zip [0 :: Int ..] row
      ]
    | (i, row) <- zip [0 :: Int ..] m
    ]
  normBound m = maximum (0 : [sum [abs (midpoint x) + boundRadius x | x <- row] | row <- m])
  -- Rodrigues
  anti =
    [ [scaleM p (1 / 2) (subM p (at i j) (at j i)) | j <- [0 .. n - 1]]
    | i <- [0 .. n - 1]
    ]
  sigma =
    normBound
      [ [scaleM p (1 / 2) (addM p (at i j) (at j i)) | j <- [0 .. n - 1]]
      | i <- [0 .. n - 1]
      ]
  t =
    sumM
      p
      [ mulM p (anti !! i !! j) (anti !! i !! j)
      | i <- [0 .. n - 1]
      , j <- [i + 1 .. n - 1]
      ]
  singlePlane =
    n <= 3
      || ( all (all isExact) anti
             && all
               (all (== Exact 0))
               ( zipWith
                   (zipWith (addM p))
                   (matMul anti (matMul anti anti))
                   (map (map (mulM p t)) anti)
               )
         )
  rodrigues = do
    f <- sincSqM p t
    g <- coscSqM p t
    Right
      [ [addM p d (addM p (mulM p f x) (mulM p g y)) | (d, x, y) <- zip3 drow xrow yrow]
      | (drow, xrow, yrow) <- zip3 identity anti (matMul anti anti)
      ]
  -- The series
  beta = normBound b
  s = length (takeWhile (> 1 / 2) (iterate (/ 2) beta))
  beta' = beta / 2 ^ s
  scaled = map (map (scaleM p (recip (2 ^ s)))) b
  tol = 10 ^^ negate (p + 4 + s) :: Rational
  factorial k = fromInteger (product [1 .. k]) :: Rational
  top = until (\k -> beta' ^ k / factorial k < tol) (+ 1) (1 :: Integer)
  powers =
    scanl
      (\m k -> map (map (scaleM p (recip (fromInteger k)))) (matMul m scaled))
      identity
      [1 .. top - 1]
  partial = foldr1 (zipWith (zipWith (addM p))) powers
  remainder = 2 * beta' ^ top / factorial top

{- | Cholesky–Banachiewicz on enclosures (design §3.5): @L Lᵀ = P@ with @L@
lower triangular. A pivot whose enclosure reaches zero or below means the
matrix may not be positive definite, which is a domain error.

It reads only the lower triangle, so symmetry must be established first.
An undecidable comparison is refused too: overlapping enclosures do not
prove that the two entries are the same unknown.
-}
choleskyRows ::
  Text -> Decide -> Precision -> [[Magnitude]] -> Either ArithError [[Magnitude]]
choleskyRows what decide p a = mapM_ symmetric pairs >> go 0 []
 where
  n = length a
  pairs = [(i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1]]
  symmetric (i, j) = case compareM decide p ((a !! i) !! j) ((a !! j) !! i) of
    Right EQ -> Right ()
    Right ord
      | ord /= EQ ->
          Left
            ( Metron.Affine.Domain
                ( what
                    <> ": entries ."
                    <> tshow i
                    <> "."
                    <> tshow j
                    <> " and ."
                    <> tshow j
                    <> "."
                    <> tshow i
                    <> " differ"
                )
            )
    _ ->
      Left
        ( Metron.Affine.Domain
            ( what
                <> ": symmetry of entries ."
                <> tshow i
                <> "."
                <> tshow j
                <> " and ."
                <> tshow j
                <> "."
                <> tshow i
                <> " cannot be established"
            )
        )
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
                  s = foldl (addM p) (Exact 0) [mulM p (prev !! k) (rowJ !! k) | k <- [0 .. j - 1]]
                  rest = subM p ((a !! i) !! j) s
              if i == j
                then
                  if midpoint rest <= boundRadius rest
                    then
                      Left
                        ( Metron.Affine.Domain
                            "cholesky needs a positive-definite matrix: a pivot's enclosure reaches zero or below"
                        )
                    else sqrtM p rest
                else divM p rest ((done !! j) !! j)
    foldM (\acc j -> (\x -> acc ++ [x]) <$> entry j acc) [] [0 .. n - 1]

sumM :: Precision -> [Magnitude] -> Magnitude
sumM p = foldl' (addM p) (Exact 0)

tshow :: (Show a) => a -> Text
tshow = T.pack . show
