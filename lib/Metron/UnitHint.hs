-- | Display-unit factors, their cancellation policy, and evaluated unit preferences.
module Metron.UnitHint (
  UnitAtom (..),
  UnitFactor (..),
  UnitHint (..),
  HintMode (..),
  Preferences,
  mkHint,
  mkHintAs,
  mergeAtoms,
  hintMul,
  hintInv,
  hintPow,
  unitHintMul,
  unitHintDiv,
  unitHintPow,
  unitHint,
  smallerUnit,
  combine,
  hintProduct,
) where

import Control.Monad (foldM)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Text (Text)
import Metron.Affine (
  Magnitude (Exact),
  Precision,
  midpoint,
  mulM,
  powM,
 )
import Metron.Dimension (Dim, dimMul, dimOne, dimPow)

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
  {atom :: UnitAtom, power :: Integer, unitDim :: Dim, unitFactor :: Magnitude}
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

data HintMode = CancelDimensions | PreserveExpression
  deriving stock (Eq, Show)

mkHint :: Precision -> [UnitFactor] -> Maybe UnitHint
mkHint = mkHintAs CancelDimensions

{- | 'mkHint', cancelling units of one dimension or not: a unit's own hint
is its expression as written (design §3.10, U8), so @km/m@ stays @km/m@
until a quantity of it is taken.
-}
mkHintAs :: HintMode -> Precision -> [UnitFactor] -> Maybe UnitHint
mkHintAs cancelling p factors = do
  let kept =
        filter
          ((/= 0) . (.power))
          (if cancelling == CancelDimensions then cancel factors else factors)
  total <-
    foldM
      ( \acc u ->
          either
            (const Nothing)
            (Just . mulM p acc)
            (powM p u.unitFactor u.power)
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
hintMul p a b = mkHint p (mergeAtoms a.atoms b.atoms)

-- | Two hints' atoms, a unit written in both taking the sum of its powers.
mergeAtoms :: [UnitFactor] -> [UnitFactor] -> [UnitFactor]
mergeAtoms = foldl merge
 where
  merge acc u
    | any ((== u.atom) . (.atom)) acc =
        [if x.atom == u.atom then x{power = x.power + u.power} else x | x <- acc]
    | otherwise = acc ++ [u]

hintInv :: Precision -> UnitHint -> Maybe UnitHint
hintInv p a = mkHint p [u{power = negate u.power} | u <- a.atoms]

hintPow :: Precision -> Integer -> UnitHint -> Maybe UnitHint
hintPow p k a = mkHint p [u{power = u.power * k} | u <- a.atoms]

{- | The hint of unit arithmetic (design §3.10, U2): the operands' hints
combined as written, nothing cancelled between units of one dimension,
and a unit written twice taking the sum of its powers.
-}
unitHintMul :: Precision -> UnitHint -> UnitHint -> Maybe UnitHint
unitHintMul p a b = unitHint p (a.atoms ++ b.atoms)

unitHintDiv :: Precision -> UnitHint -> UnitHint -> Maybe UnitHint
unitHintDiv p a b = unitHint p (a.atoms ++ [u{power = negate u.power} | u <- b.atoms])

unitHintPow :: Precision -> Integer -> UnitHint -> Maybe UnitHint
unitHintPow p k a = unitHint p [u{power = u.power * k} | u <- a.atoms]

{- | A unit's hint from its factors as written (design §3.10, U8, U9).
When every unit cancels, as in @km/km@, the factors stay as written, so
that the unit prints as an expression that reads back as a unit and not
as the number one.
-}
unitHint :: Precision -> [UnitFactor] -> Maybe UnitHint
unitHint p written
  | not (null written) && all ((== 0) . (.power)) merged =
      mkHintAs PreserveExpression p written
  | otherwise = mkHintAs PreserveExpression p merged
 where
  merged = mergeAtoms [] written

{- | The unit a sum prints in: the smaller of its operands', so that a + b and
b + a print alike (design §3.2.12); the left one when they are equal.
The choice is made when the result is: a choice left in a thunk would keep
both hints, and a sum in a loop every hint before it.
-}
smallerUnit :: UnitHint -> UnitHint -> Maybe UnitHint
smallerUnit a b = if midpoint b.factor < midpoint a.factor then Just b else Just a

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

-- | The display unit of a product, as @outer@ gives it its operands'.
hintProduct :: Precision -> Maybe UnitHint -> Maybe UnitHint -> Maybe UnitHint
hintProduct p = combine (hintMul p)
