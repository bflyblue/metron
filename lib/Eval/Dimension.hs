-- | Dimensions (design §4.1, §4.4): the free abelian group over the seven SI
-- base dimensions and dimension variables, kept in normal form, with
-- Kennedy's unification algorithm.
module Eval.Dimension
  ( BaseDim (..)
  , DimAtom (..)
  , Dim
  , dimOne
  , dimBase
  , dimVar
  , dimFromAtoms
  , dimMul
  , dimInv
  , dimDiv
  , dimPow
  , dimRoot
  , dimAtoms
  , dimVars
  , isDimOne
  , substDimVar
  , renderDim
  , renderDimWith
  , renderUnits
  , baseSymbol
  ) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

-- | Length, mass, time, current, temperature, amount, luminous intensity.
data BaseDim = L | M | T | I | Θ | N | J
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data DimAtom
  = Base BaseDim
  | DVar Int
  deriving stock (Eq, Ord, Show)

-- | A normalised dimension: atoms with non-zero integer exponents. The
-- dimensionless dimension is the empty map.
newtype Dim = Dim (Map DimAtom Int)
  deriving stock (Eq, Ord, Show)

dimOne :: Dim
dimOne = Dim Map.empty

dimBase :: BaseDim -> Dim
dimBase b = Dim (Map.singleton (Base b) 1)

dimVar :: Int -> Dim
dimVar v = Dim (Map.singleton (DVar v) 1)

dimFromAtoms :: [(DimAtom, Int)] -> Dim
dimFromAtoms = Dim . Map.filter (/= 0) . Map.fromListWith (+)

dimMul :: Dim -> Dim -> Dim
dimMul (Dim a) (Dim b) = Dim (Map.filter (/= 0) (Map.unionWith (+) a b))

dimInv :: Dim -> Dim
dimInv (Dim a) = Dim (Map.map negate a)

dimDiv :: Dim -> Dim -> Dim
dimDiv a b = dimMul a (dimInv b)

dimPow :: Int -> Dim -> Dim
dimPow 0 _ = dimOne
dimPow k (Dim a) = Dim (Map.map (* k) a)

-- | The @k@-th root, when every exponent is divisible by @k@.
dimRoot :: Int -> Dim -> Maybe Dim
dimRoot k (Dim a)
  | k == 0 = Nothing
  | all ((== 0) . (`mod` k)) (Map.elems a) = Just (Dim (Map.map (`div` k) a))
  | otherwise = Nothing

dimAtoms :: Dim -> [(DimAtom, Int)]
dimAtoms (Dim a) = Map.toList a

dimVars :: Dim -> [Int]
dimVars (Dim a) = [v | DVar v <- Map.keys a]

isDimOne :: Dim -> Bool
isDimOne (Dim a) = Map.null a

-- | Replace a dimension variable by a dimension, renormalising.
substDimVar :: Int -> Dim -> Dim -> Dim
substDimVar v replacement (Dim a) = case Map.lookup (DVar v) a of
  Nothing -> Dim a
  Just k -> dimMul (Dim (Map.delete (DVar v) a)) (dimPow k replacement)

-- Rendering -----------------------------------------------------------------------

baseSymbol :: BaseDim -> Text
baseSymbol = \case
  L -> "m"
  M -> "kg"
  T -> "s"
  I -> "A"
  Θ -> "K"
  N -> "mol"
  J -> "cd"

-- | @[m s^-2]@, @[d1 d2^-1]@; the empty dimension renders as @1@.
renderDim :: Dim -> Text
renderDim = renderDimWith (\v -> "d" <> T.pack (show v))

renderDimWith :: (Int -> Text) -> Dim -> Text
renderDimWith varName d
  | isDimOne d = "1"
  | otherwise = "[" <> renderUnitsWith varName d <> "]"

-- | The base units of a concrete dimension as they follow a printed value:
-- @m s^-2@; empty when dimensionless.
renderUnits :: Dim -> Text
renderUnits d
  | isDimOne d = ""
  | otherwise = renderUnitsWith (\v -> "d" <> T.pack (show v)) d

renderUnitsWith :: (Int -> Text) -> Dim -> Text
renderUnitsWith varName d = T.unwords (map atom (sortOn order (dimAtoms d)))
  where
    -- Positive exponents before negative, and within each the customary
    -- order @kg m s A K mol cd@ (so a joule is @kg m^2 s^-2@), variables last.
    order (a, k) = (k < 0, rank a)
    rank = \case
      Base M -> 0 :: Int
      Base L -> 1
      Base T -> 2
      Base I -> 3
      Base Θ -> 4
      Base N -> 5
      Base J -> 6
      DVar v -> 7 + v
    atom (a, k) = name a <> (if k == 1 then "" else "^" <> T.pack (show k))
    name = \case
      Base b -> baseSymbol b
      DVar v -> varName v
