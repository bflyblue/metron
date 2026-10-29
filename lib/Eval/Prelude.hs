-- | The prelude (design §3.2.11): derived SI units, prefixes, accepted units,
-- exact constants, the Levi-Civita tensor and the cross product, as source
-- text in the language itself. It is entered into every session as one
-- binding group, so every unit is an ordinary hashed, viewable definition.
-- The prefix table is generated here rather than typed by hand.
module Eval.Prelude
  ( preludeSource
  , preludeNames
  ) where

import Data.Text (Text)
import Data.Text qualified as T

-- | Derived and accepted units, in dependency order is not required: the
-- prelude is one binding group.
derived :: [(Text, Text)]
derived =
  [ ("N", "kg * m / s^2")
  , ("J", "N * m")
  , ("W", "J / s")
  , ("Pa", "N / m^2")
  , ("Hz", "1 / s")
  , ("C", "A * s")
  , ("V", "W / A")
  , ("Ω", "V / A")
  , ("ohm", "V / A")
  , ("F", "C / V")
  , ("S", "A / V")
  , ("T", "V * s / m^2")
  , ("H", "V * s / A")
  , ("Wb", "V * s")
  , ("rad", "1")
  , ("sr", "1")
  , ("lm", "cd")
  , ("lx", "lm / m^2")
  , ("Bq", "1 / s")
  , ("Gy", "J / kg")
  , ("Sv", "J / kg")
  , ("kat", "mol / s")
  , ("g", "kg / 1000")
  , ("L", "(m / 10)^3")
  , ("t", "1000 * kg")
  , ("min", "60 * s")
  , ("h", "3600 * s")
  , ("day", "86400 * s")
  , ("year", "365.25 * day")
  , ("AU", "149597870700 * m")
  ]

-- | The 24 SI prefixes as powers of ten, with @u@ as the ASCII micro.
prefixes :: [(Text, Int)]
prefixes =
  [ ("Q", 30), ("R", 27), ("Y", 24), ("Z", 21), ("E", 18), ("P", 15), ("T", 12), ("G", 9), ("M", 6), ("k", 3), ("h", 2), ("da", 1)
  , ("d", -1), ("c", -2), ("m", -3), ("µ", -6), ("u", -6), ("n", -9), ("p", -12), ("f", -15), ("a", -18), ("z", -21), ("y", -24), ("r", -27), ("q", -30)
  ]

-- | Units that take prefixes: the base units except kg (whose prefixes attach
-- to g), the coherent derived units, g and L.
prefixable :: [Text]
prefixable =
  ["m", "s", "A", "K", "mol", "cd", "g", "N", "J", "W", "Pa", "Hz", "C", "V", "Ω", "ohm", "F", "S", "T", "H", "Wb", "lm", "lx", "Bq", "Gy", "Sv", "kat", "L"]

-- | Exact constants: SI-2019 defining constants and IAU nominal values.
-- Measured constants with a standard uncertainty (G, M_earth) arrive with
-- affine arithmetic.
constants :: [(Text, Text)]
constants =
  [ ("c", "299792458 * m / s")
  , ("planck", "6.62607015e-34 * J * s")
  , ("k_B", "1.380649e-23 * J / K")
  , ("N_A", "6.02214076e23 / mol")
  , ("e_charge", "1.602176634e-19 * C")
  , ("g0", "9.80665 * m / s^2")
  , ("GM_earth", "3.986004e14 * m^3 / s^2")
  , ("GM_sun", "1.3271244e20 * m^3 / s^2")
  , ("R_earth", "6378100 * m")
  ]

-- | Tensor algebra: the 3D Levi-Civita tensor and the cross product as the
-- Hodge dual of the wedge product (design §3.3).
algebra :: [(Text, Text)]
algebra =
  [ ("ε", "[[[0, 0, 0], [0, 0, 1], [0, -1, 0]], [[0, 0, -1], [0, 0, 0], [1, 0, 0]], [[0, 1, 0], [-1, 0, 0], [0, 0, 0]]]")
  , ("levi", "ε")
  , ("cross", "\\a b -> star (a /\\ b)")
  ]

preludeSource :: Text
preludeSource =
  T.unlines $
    [def n e | (n, e) <- derived]
      ++ [def (p <> u) ("10^" <> T.pack (show k) <> " * " <> u) | (p, k) <- prefixes, u <- prefixable, p <> u /= "kg"]
      ++ [def n e | (n, e) <- constants]
      ++ [def n e | (n, e) <- algebra]
  where
    def n e = "let " <> n <> " = " <> e

-- | Every name the prelude defines.
preludeNames :: [Text]
preludeNames =
  map fst derived
    ++ [p <> u | (p, _) <- prefixes, u <- prefixable, p <> u /= "kg"]
    ++ map fst constants
    ++ map fst algebra
