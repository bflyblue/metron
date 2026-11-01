-- | Untyped primitive metadata shared by Core, desugaring, and runtime dispatch.
module Metron.Primitive (
  primArity,
  baseUnit,
  typedPrims,
) where

import Data.Text (Text)
import Metron.Dimension (BaseDim (..))

primArity :: Text -> Maybe Int
primArity = \case
  "add" -> Just 2
  "sub" -> Just 2
  "outer" -> Just 2
  "emul" -> Just 2
  "ediv" -> Just 2
  "div" -> Just 2
  "eq" -> Just 2
  "ne" -> Just 2
  "lt" -> Just 2
  "le" -> Just 2
  "gt" -> Just 2
  "ge" -> Just 2
  "and" -> Just 2
  "or" -> Just 2
  "neg" -> Just 1
  "not" -> Just 1
  "abs" -> Just 1
  "floor" -> Just 1
  "ceil" -> Just 1
  "round" -> Just 1
  -- Known to the desugarer and type checker now; implemented in the
  -- evaluator with affine arithmetic and linear algebra (roadmap 3 and 4).
  "sqrt" -> Just 1
  "sin" -> Just 1
  "cos" -> Just 1
  "tan" -> Just 1
  "asin" -> Just 1
  "acos" -> Just 1
  "atan" -> Just 1
  "sinh" -> Just 1
  "cosh" -> Just 1
  "tanh" -> Just 1
  "exp" -> Just 1
  "log" -> Just 1
  "atan2" -> Just 2
  "to" -> Just 2
  "dot" -> Just 2
  "wedge" -> Just 2
  "star" -> Just 1
  "norm" -> Just 1
  "transpose" -> Just 1
  -- Contraction and index permutation (design §4.2): the leading arguments
  -- are literal index positions, and the type is computed from them.
  "contract" -> Just 3
  "permute" -> Just 2
  -- A slice along axis k at position i (design §2.10): both literal.
  "slice" -> Just 3
  "inverse" -> Just 1
  "det" -> Just 1
  "vmap" -> Just 2
  "indices" -> Just 1
  "vzipWith" -> Just 3
  "timap" -> Just 2
  "pi" -> Just 0
  -- The seven SI base units (design §3.2.11).
  "m" -> Just 0
  "kg" -> Just 0
  "s" -> Just 0
  "A" -> Just 0
  "K" -> Just 0
  "mol" -> Just 0
  "cd" -> Just 0
  "rad" -> Just 0
  -- A chart (design §3.10, F3, F10): on a space or on a parent chart, with
  -- the frame and the axes it mints, if any, and its clauses, each a list
  -- of none or one (the generators a list of any number).
  "mkRoot" -> Just 7
  "mkChart" -> Just 7
  "pointOn" -> Just 2
  "pointAdd" -> Just 2
  "pointSub" -> Just 2
  -- An amount placed on a chart from its origin along its axes (design §7.7).
  "pointAt" -> Just 2
  -- Conversions (design §3.10, F5, F7, F10): a point to a chart, a point
  -- from a configuration of its frame to a chart, and an amount along a
  -- chart's axes, from the space's base axes or from a configuration.
  "toChart" -> Just 2
  "fromTo" -> Just 3
  "toAxes" -> Just 2
  "axesFromTo" -> Just 3
  -- Units (design §3.10): the quantity rule after a unit, and a unit's
  -- declaration. `unit` is a keyword, so no source names it; `scale 3 km`
  -- is the quantity `3 km`.
  "scale" -> Just 2
  "unit" -> Just 1
  "cholesky" -> Just 1
  "covariance" -> Just 1
  "crossCovariance" -> Just 2
  -- The parts of an enclosure (design §3.2.9), to write a comparison policy.
  "mid" -> Just 1
  "bound" -> Just 1
  "sd" -> Just 1
  -- The double backend's own (design §8.2).
  "errorOf" -> Just 1
  "digitsOf" -> Just 1
  "nextUp" -> Just 1
  "ulps" -> Just 2
  "eps" -> Just 0
  "fma" -> Just 3
  "isNaN" -> Just 1
  "isInfinite" -> Just 1
  -- Rotations (design §3.3, §3.8): the matrix exponential, a matrix
  -- applied along every axis of a tensor, and the rotation of a chart.
  "expm" -> Just 1
  "transformBy" -> Just 2
  "rotationOf" -> Just 1
  "withAxes" -> Just 2
  -- A chart's kinematics (design §3.8): its absolute angular velocity and
  -- the velocity of its origin, both along the base axes, and its origin
  -- from the space's base origin (design §3.10, part F, as built).
  "spinOf" -> Just 1
  "originVelocityOf" -> Just 1
  "originOf" -> Just 1
  "seq" -> Just 2
  _ -> Nothing

-- | The base unit a primitive stands for, if it is one (design §3.2.11).
baseUnit :: Text -> Maybe BaseDim
baseUnit = \case
  "m" -> Just L
  "kg" -> Just M
  "s" -> Just T
  "A" -> Just I
  "K" -> Just Θ
  "mol" -> Just N
  "cd" -> Just J
  "rad" -> Just Ang
  _ -> Nothing

-- | The primitives whose result's dimension comes from their type.
typedPrims :: [Text]
typedPrims = ["vmap", "vzipWith", "timap"]

-- | A type under the type-level arguments in force.
