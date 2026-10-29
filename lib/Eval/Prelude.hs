{- | The prelude (design §3.2.11): derived SI units, prefixes, accepted units,
exact constants, the Levi-Civita tensor and the cross product, as source
text in the language itself. It is entered into every session as one
binding group, so every unit is an ordinary hashed, viewable definition.
The prefix table is generated here rather than typed by hand.
-}
module Eval.Prelude (
  preludeSource,
  preludeNames,
) where

import Data.Text (Text)
import Data.Text qualified as T

{- | Derived and accepted units, in dependency order is not required: the
prelude is one binding group.
-}
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
  , -- Units with the same definition would be one definition with two names
    -- (content addressing), and would print under one of them. Where two units
    -- are the same quantity under different names, one is defined through the
    -- other so that each keeps its own identity and prints as itself.
    ("sr", "rad^2")
  , ("lm", "cd * sr")
  , ("lx", "lm / m^2")
  , ("Bq", "1 * Hz")
  , ("Gy", "J / kg")
  , ("Sv", "1 * Gy")
  , ("kat", "mol / s")
  , ("g", "kg / 1000")
  , ("L", "(m / 10)^3")
  , ("t", "1000 * kg")
  , ("min", "60 * s")
  , ("h", "3600 * s")
  , ("day", "86400 * s")
  , ("year", "365.25 * day")
  , ("AU", "149597870700 * m")
  , ("deg", "pi / 180 * rad")
  , ("arcmin", "deg / 60")
  , ("arcsec", "arcmin / 60")
  , ("deltaC", "K")
  , ("deltaF", "5/9 * K")
  ]

-- | The 24 SI prefixes as powers of ten, with @u@ as the ASCII micro.
prefixes :: [(Text, Int)]
prefixes =
  [ ("Q", 30)
  , ("R", 27)
  , ("Y", 24)
  , ("Z", 21)
  , ("E", 18)
  , ("P", 15)
  , ("T", 12)
  , ("G", 9)
  , ("M", 6)
  , ("k", 3)
  , ("h", 2)
  , ("da", 1)
  , ("d", -1)
  , ("c", -2)
  , ("m", -3)
  , ("µ", -6)
  , ("u", -6)
  , ("n", -9)
  , ("p", -12)
  , ("f", -15)
  , ("a", -18)
  , ("z", -21)
  , ("y", -24)
  , ("r", -27)
  , ("q", -30)
  ]

{- | Units that take prefixes: the base units except kg (whose prefixes attach
to g), the coherent derived units, g and L.
-}
prefixable :: [Text]
prefixable =
  [ "m"
  , "s"
  , "A"
  , "K"
  , "mol"
  , "cd"
  , "rad"
  , "g"
  , "N"
  , "J"
  , "W"
  , "Pa"
  , "Hz"
  , "C"
  , "V"
  , "Ω"
  , "ohm"
  , "F"
  , "S"
  , "T"
  , "H"
  , "Wb"
  , "lm"
  , "lx"
  , "Bq"
  , "Gy"
  , "Sv"
  , "kat"
  , "L"
  ]

{- | Constants. SI-2019 defining constants and IAU 2015 nominal values are
exact. G carries its CODATA 2018 standard uncertainty with the
statistical kind (design §3.2.11), and the masses are derived from the
exact nominal GM values and G, so their uncertainty is G's and the error
budget says so.
-}
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
  , ("G", "(6.67430e-11 ±σ 1.5e-15) * m^3 / (kg * s^2)")
  , ("M_earth", "GM_earth / G")
  , ("M_sun", "GM_sun / G")
  ]

{- | Scales for points (design §3.6): temperature scales, epochs on the time
line, gauge pressure. Each is a step unit and an origin.
-}
scales :: [(Text, Text)]
scales =
  [ ("degC", "K at 273.15 K")
  , ("degF", "deltaF at 459.67 deltaF")
  , ("degR", "deltaF at 0 deltaF")
  , ("kelvin", "K at 0 K")
  , ("JD", "day at 0 day")
  , ("MJD", "day at 2400000.5 day")
  , ("J2000", "day at 2451545 day")
  , ("unix", "s at 2440587.5 day")
  , ("gauge", "Pa at 101325 Pa")
  ]

{- | Tensor algebra: the 3D Levi-Civita tensor and the cross product as the
Hodge dual of the wedge product (design §3.3).
-}
algebra :: [(Text, Text)]
algebra =
  [
    ( "ε"
    , "[[[0, 0, 0], [0, 0, 1], [0, -1, 0]], [[0, 0, -1], [0, 0, 0], [1, 0, 0]], [[0, 1, 0], [-1, 0, 0], [0, 0, 0]]]"
    )
  , ("levi", "ε")
  , ("cross", "\\a b -> star (a /\\ b)")
  ]

preludeSource :: Text
preludeSource =
  T.unlines
    $ [unitDef n e | (n, e) <- derived]
      ++ [ unitDef (p <> u) ("10^" <> T.pack (show k) <> " * " <> u)
         | (p, k) <- prefixes
         , u <- prefixable
         , p <> u /= "kg"
         ]
      ++ [def n e | (n, e) <- constants]
      ++ [scaleDef n e | (n, e) <- scales]
      ++ [def n e | (n, e) <- algebra]
 where
  def n e = "let " <> n <> " = " <> e
  unitDef n e = "unit " <> n <> " = " <> e
  scaleDef n e = "scale " <> n <> " = " <> e

-- | Every name the prelude defines.
preludeNames :: [Text]
preludeNames =
  map fst derived
    ++ [p <> u | (p, _) <- prefixes, u <- prefixable, p <> u /= "kg"]
    ++ map fst constants
    ++ map fst scales
    ++ map fst algebra
