{- | Dimensions (design §4.1, §4.4): the free abelian group over the seven SI
base dimensions and dimension variables, kept in normal form, with
Kennedy's unification algorithm.
-}
module Metron.Dimension (
  BaseDim (..),
  DimAtom (..),
  Dim,
  dimOne,
  dimBase,
  dimVar,
  dimFromAtoms,
  dimMul,
  dimInv,
  dimDiv,
  dimPow,
  dimRoot,
  dimAtoms,
  dimVars,
  isDimOne,
  substDimVar,
  renderDim,
  renderDimIn,
  renderDimArgIn,
  productText,
  renderUnitsIn,
  Spelling (..),
  exponentText,
  arrowText,
  baseSymbol,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

-- | Length, mass, time, current, temperature, amount, luminous intensity.
data BaseDim = L | M | T | I | Θ | N | J | Ang
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data DimAtom
  = Base BaseDim
  | DVar Int
  deriving stock (Eq, Ord, Show)

{- | A normalised dimension: atoms with non-zero integer exponents. The
dimensionless dimension is the empty map.
-}
newtype Dim = Dim (Map DimAtom Integer)
  deriving stock (Eq, Ord, Show)

dimOne :: Dim
dimOne = Dim Map.empty

dimBase :: BaseDim -> Dim
dimBase b = Dim (Map.singleton (Base b) 1)

dimVar :: Int -> Dim
dimVar v = Dim (Map.singleton (DVar v) 1)

dimFromAtoms :: [(DimAtom, Integer)] -> Dim
dimFromAtoms = Dim . Map.filter (/= 0) . Map.fromListWith (+)

dimMul :: Dim -> Dim -> Dim
dimMul (Dim a) (Dim b) = Dim (Map.filter (/= 0) (Map.unionWith (+) a b))

dimInv :: Dim -> Dim
dimInv (Dim a) = Dim (Map.map negate a)

dimDiv :: Dim -> Dim -> Dim
dimDiv a b = dimMul a (dimInv b)

dimPow :: Integer -> Dim -> Dim
dimPow 0 _ = dimOne
dimPow k (Dim a) = Dim (Map.map (* k) a)

-- | The @k@-th root, when every exponent is divisible by @k@.
dimRoot :: Integer -> Dim -> Maybe Dim
dimRoot k (Dim a)
  | k == 0 = Nothing
  | all ((== 0) . (`mod` k)) (Map.elems a) = Just (Dim (Map.map (`div` k) a))
  | otherwise = Nothing

dimAtoms :: Dim -> [(DimAtom, Integer)]
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
  Ang -> "rad"

{- | How printed output spells the constructs that have both an ASCII and a
unicode spelling (design §2.8, §7.3): @m s^-2@ and @\\x -> x^2@, or
@m s⁻²@ and @λx → x²@. Either reads back as the same expression.
-}
data Spelling = Ascii | Unicode
  deriving stock (Eq, Show)

{- | An exponent glued to what it raises: @^-2@, or the superscript @⁻²@.
The exponent 1 is written too; callers leave it out.
-}
exponentText :: Spelling -> Integer -> Text
exponentText spelling k = case spelling of
  Ascii -> "^" <> T.pack (show k)
  Unicode -> T.map superscript (T.pack (show k))
 where
  superscript = \case
    '-' -> '⁻'
    '0' -> '⁰'
    '1' -> '¹'
    '2' -> '²'
    '3' -> '³'
    '4' -> '⁴'
    '5' -> '⁵'
    '6' -> '⁶'
    '7' -> '⁷'
    '8' -> '⁸'
    '9' -> '⁹'
    c -> c

-- | The arrow of a function type, a lambda or a case alternative, with its spaces.
arrowText :: Spelling -> Text
arrowText = \case
  Ascii -> " -> "
  Unicode -> " → "

{- | A dimension standing alone, as an error message prints it (design
§4.1): @m/s^2@, @kg*m^2/s^2@, @m^2/(s^2*K)@, @1/s@, and @1@ when
dimensionless. Positive powers come first in the customary order, then
@/@ and the negative ones, grouped when there are several.
-}
renderDim :: Dim -> Text
renderDim = renderDimIn Ascii (\v -> "d" <> T.pack (show v))

{- | 'renderDim' in a chosen spelling, its variables named by the
function: @kg·m²/s²@ in unicode.
-}
renderDimIn :: Spelling -> (Int -> Text) -> Dim -> Text
renderDimIn spelling varName d = case (ups, downs) of
  ([], []) -> "1"
  (_, []) -> product' ups
  ([], _) -> "1/" <> grouped downs
  _ -> product' ups <> "/" <> grouped downs
 where
  atoms = sortOn (atomRank . fst) (dimAtoms d)
  ups = [(a, k) | (a, k) <- atoms, k > 0]
  downs = [(a, negate k) | (a, k) <- atoms, k < 0]
  product' = T.intercalate (productText spelling) . map (atomText spelling varName)
  grouped = \case
    [one] -> atomText spelling varName one
    many -> "(" <> product' many <> ")"

{- | A dimension as a type argument (design §4.1): one name to the first
power bare (@m@, @d@), @1@ when dimensionless, anything else in
parentheses (@(m/s^2)@).
-}
renderDimArgIn :: Spelling -> (Int -> Text) -> Dim -> Text
renderDimArgIn spelling varName d = case dimAtoms d of
  [] -> "1"
  [(_, 1)] -> renderDimIn spelling varName d
  _ -> "(" <> renderDimIn spelling varName d <> ")"

-- | The product sign in a dimension: @*@, or @·@ in unicode.
productText :: Spelling -> Text
productText = \case
  Ascii -> "*"
  Unicode -> "·"

{- | The base units of a concrete dimension as they follow a printed value:
@m s^-2@, or @m s⁻²@ in unicode; empty when dimensionless.
-}
renderUnitsIn :: Spelling -> Dim -> Text
renderUnitsIn spelling d
  | isDimOne d = ""
  | otherwise =
      T.unwords
        ( map
            (atomText spelling (\v -> "d" <> T.pack (show v)))
            (sortOn order (dimAtoms d))
        )
 where
  -- Positive exponents before negative, each in the customary order (so a
  -- joule is @kg m^2 s^-2@).
  order (a, k) = (k < 0, atomRank a)

{- | The customary order of a dimension's atoms, @kg m s A K mol cd rad@,
variables last.
-}
atomRank :: DimAtom -> Int
atomRank = \case
  Base M -> 0
  Base L -> 1
  Base T -> 2
  Base I -> 3
  Base Θ -> 4
  Base N -> 5
  Base J -> 6
  Base Ang -> 7
  DVar v -> 8 + v

-- | An atom with its exponent, the exponent 1 left out.
atomText :: Spelling -> (Int -> Text) -> (DimAtom, Integer) -> Text
atomText spelling varName (a, k) =
  name <> (if k == 1 then "" else exponentText spelling k)
 where
  name = case a of
    Base b -> baseSymbol b
    DVar v -> varName v
