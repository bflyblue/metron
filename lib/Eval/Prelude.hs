{- | The standard library (design §7.7) as source text in the language
itself, split by domain into sibling namespaces: the structural functions
in @std@, tensor algebra and the joint covariance in blocks in @linalg@,
the SI in @si@, and @time@, @angle@, @temperature@, @astro@, @physics@ and
@imperial@ ('stdlibLayout'). A new codebase is seeded with it as one
binding group, so every unit is an ordinary hashed, viewable definition
that lives in the codebase like any other, with the stored default @use@s
of 'stdlibDefaultUses'. Labels that name a definition twice (@newton@ and
@N@) are 'stdlibAliases', bound after the group is entered, as @:alias@
binds them. The prefix table is generated here rather than typed by hand.

The library as it was in format 4, everything under @std@, is kept
('stdlib4Source'): the format 4 to 5 migration needs its hashes to know
which of a store's labels are the old library's (design §7.4).
-}
module Eval.Prelude (
  -- * The library
  stdlibSource,
  stdlibAliases,
  stdlibNames,
  stdlibNamespaces,
  stdlibDefaultUses,
  stdlibMovedOut,
  isLibraryPath,
  stdlibCodebase,
  stdlibHomes,
  stdlibMoved,

  -- * The format-4 library
  preludeSource,
  stdlib4Source,
  stdlib4Codebase,
  stdlib4Moved,
) where

import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, maybeToList)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase (
  Codebase (..),
  Reference,
  addStoredUse,
  bindName,
  emptyCodebase,
  isScaleName,
  isUnitName,
  lookupName,
  markScale,
  markUnit,
 )
import Eval.Lexer (prepare)
import Eval.Parser (parseProgram)
import Eval.Resolve (processGroup, renderResolveError)
import Eval.Syntax qualified as S

-- The format-4 library's tables ------------------------------------------------

{- These tables are frozen: 'preludeSource' and 'stdlib4Source' are made
from them, and the migrations and tests rely on their hashes. The current
library ('stdlibLayout') shares 'prefixes', 'algebra', 'structural' and
the covariance blocks with them and has its own tables for the rest. -}

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
  , -- Two units may share a definition (Bq and Hz are both 1/s): a unit is
    -- a name, and a value prints under the name it was written with.
    ("sr", "rad^2")
  , ("lm", "cd * sr")
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

{- | Tensor algebra: the 3D Levi-Civita tensor, the cross product as the
Hodge dual of the wedge product, the trace as a contraction, and @vimap@,
a map that also sees each component's position as a value (design §3.3).
@vimap@ is for vectors, with the position as one number; the primitive
@timap@ is the general form, at any rank, with the multi-index as a vector.
-}
algebra :: [(Text, Text)]
algebra =
  [
    ( "ε"
    , "[[[0, 0, 0], [0, 0, 1], [0, -1, 0]], [[0, 0, -1], [0, 0, 0], [1, 0, 0]], [[0, 1, 0], [-1, 0, 0], [0, 0, 0]]]"
    )
  , ("levi", "ε")
  , ("cross", "\\a b -> star (a /\\ b)")
  , ("trace", "\\a -> contract 0 1 a")
  , ("vimap", "\\f v -> vzipWith f (indices v) v")
  ]

{- | Tuples and lists (design §2.3): the structural functions, recursive
through cycles like any other definition.
-}
structural :: [(Text, Text)]
structural =
  [ ("fst", "\\p -> case p of (a, _) -> a")
  , ("snd", "\\p -> case p of (_, b) -> b")
  , ("map", "\\f xs -> case xs of {} -> {}; x : rest -> f x : map f rest")
  ,
    ( "filter"
    , "\\p xs -> case xs of {} -> {}; x : rest -> if p x then x : filter p rest else filter p rest"
    )
  , ("foldr", "\\f z xs -> case xs of {} -> z; x : rest -> f x (foldr f z rest)")
  , ("foldl", "\\f z xs -> case xs of {} -> z; x : rest -> foldl f (f z x) rest")
  , ("length", "\\xs -> foldl (\\n _ -> n + 1) 0 xs")
  , ("reverse", "\\xs -> foldl (\\acc x -> x : acc) {} xs")
  ,
    ( "zip"
    , "\\xs ys -> case xs of {} -> {}; x : xr -> case ys of {} -> {}; y : yr -> (x, y) : zip xr yr"
    )
  , ("range", "\\a b -> if a > b then {} else a : range (a + 1) b")
  ]

{- | A joint covariance in blocks (design §3.7): the covariance of a state
@(r, v)@ of two homogeneous vectors, @r : Vec n d1@ and @v : Vec n d2@, as
the record of its three distinct blocks, @rr = Cov(r, r)@, @rv = Cov(r, v)@
and @vv = Cov(v, v)@ (the fourth is @transpose rv@). Every block is
homogeneous, so no matrix of mixed dimensions is needed, and the Kalman
filter's steps are written on the blocks: propagation @Φ P Φᵀ@ with
@Φ = [Φ_rr, Φ_rv; Φ_vr, Φ_vv]@, the innovation covariance @H P Hᵀ + R@ and
the gain @P Hᵀ S⁻¹@ with @H = [H_r | H_v]@, and the update @(I − K H) P@.
-}
covarianceData :: Text
covarianceData =
  "data Cov2 n d1 d2 = Cov2 {rr :: Mat n n [d1^2], rv :: Mat n n [d1 d2], vv :: Mat n n [d2^2]}"

{- | The block filter over 'covarianceData'. @propagateCov2@ forms the block
rows of @Φ P@ first and multiplies them by the block columns of @Φᵀ@;
expanded, @rr' = Φ_rr rr Φ_rrᵀ + Φ_rv rvᵀ Φ_rrᵀ + Φ_rr rv Φ_rvᵀ + Φ_rv vv
Φ_rvᵀ@. @gain2@ returns the pair @(K_r, K_v)@ of the gain's block rows.
@updateCov2@ is @P − K (H P)@ with @H P = (P Hᵀ)ᵀ@, since @P@ is
symmetric: written with @transpose h_r@ the measurement matrices have a
known rank, where @h_r \@ p.rr@ alone would default @h_r@ to a vector
(design §4.2).
-}
covarianceBlocks :: [(Text, Text)]
covarianceBlocks =
  [
    ( "jointCovariance"
    , "\\state -> case state of (r, v) -> Cov2 {rr = crossCovariance r r, rv = crossCovariance r v, vv = crossCovariance v v}"
    )
  ,
    ( "propagateCov2"
    , T.unwords
        [ "\\phi p -> case phi of (phi_rr, phi_rv, phi_vr, phi_vv) ->"
        , "let rr_ = phi_rr @ p.rr + phi_rv @ transpose p.rv in"
        , "let rv_ = phi_rr @ p.rv + phi_rv @ p.vv in"
        , "let vr_ = phi_vr @ p.rr + phi_vv @ transpose p.rv in"
        , "let vv_ = phi_vr @ p.rv + phi_vv @ p.vv in"
        , "Cov2 {rr = rr_ @ transpose phi_rr + rv_ @ transpose phi_rv,"
        , "rv = rr_ @ transpose phi_vr + rv_ @ transpose phi_vv,"
        , "vv = vr_ @ transpose phi_vr + vv_ @ transpose phi_vv}"
        ]
    )
  ,
    ( "innovationCov2"
    , T.unwords
        [ "\\h_r h_v p r_meas ->"
        , "h_r @ p.rr @ transpose h_r + h_r @ p.rv @ transpose h_v"
        , "+ h_v @ transpose p.rv @ transpose h_r + h_v @ p.vv @ transpose h_v + r_meas"
        ]
    )
  ,
    ( "gain2"
    , T.unwords
        [ "\\h_r h_v p s_inv ->"
        , "((p.rr @ transpose h_r + p.rv @ transpose h_v) @ s_inv,"
        , "(transpose p.rv @ transpose h_r + p.vv @ transpose h_v) @ s_inv)"
        ]
    )
  ,
    ( "updateCov2"
    , T.unwords
        [ "\\k h_r h_v p -> case k of (k_r, k_v) ->"
        , "let ph_r = p.rr @ transpose h_r + p.rv @ transpose h_v in"
        , "let ph_v = transpose p.rv @ transpose h_r + p.vv @ transpose h_v in"
        , "Cov2 {rr = p.rr - k_r @ transpose ph_r,"
        , "rv = p.rv - k_r @ transpose ph_v,"
        , "vv = p.vv - k_v @ transpose ph_v}"
        ]
    )
  ]

{- | The library's statements at the root, one per line, as the prelude was
entered before it moved under @std@ (design §7.7). 'stdlib4Source' is this
inside a @namespace std@ block; the tests enter both to check that the
move kept every hash, and build a format-3 store from this one.
-}
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
      ++ [def n e | (n, e) <- structural]
 where
  def n e = "let " <> n <> " = " <> e
  unitDef n e = "unit " <> n <> " = " <> e
  scaleDef n e = "scale " <> n <> " = " <> e

{- | Statements the format-4 library gained after it moved under @std@:
they were never at the root, so they are not in 'preludeSource'.
-}
stdlib4Additions :: Text
stdlib4Additions =
  T.unlines
    (covarianceData : ["let " <> n <> " = " <> e | (n, e) <- covarianceBlocks])

{- | The library as format 4 seeded it (design §7.7): every statement
inside @namespace std@.
-}
stdlib4Source :: Text
stdlib4Source =
  T.unlines
    ( "namespace std"
        : map ("  " <>) (T.lines preludeSource ++ T.lines stdlib4Additions)
    )

-- | The format-4 library entered, with its stored @use std@.
stdlib4Codebase :: Either Text Codebase
stdlib4Codebase = addStoredUse (S.Use "std" Nothing) <$> entered stdlib4Source

{- | The format-4 library's names whose reference the move under @std@
changed, each with the reference the old root prelude gave the bare name:
a @±@ is stamped with its definition's full path (design §3.2.4), so
@std.G@ is not the root @G@, and the masses derived from it differ too.
The format 3 to 4 migration records these as history (design §7.4).
-}
stdlib4Moved :: Either Text [(Text, Reference)]
stdlib4Moved = do
  new <- stdlib4Codebase
  old <- entered preludeSource
  pure
    [ (full, r)
    | (n, r) <- Map.toList old.names
    , let full = "std." <> n
    , lookupName full new /= Just r
    ]

-- The library by domain ------------------------------------------------------------

-- | One statement of the library's source.
data Statement
  = Let Text Text
  | Unit Text Text
  | Scale Text Text
  | -- | a @use@ inside the block, for names of a sibling namespace
    UseNs Text
  | {- | a @data@ declaration, and its labels: the type, its constructors
    where they are not the type's name, then its fields
    -}
    Data Text [Text]

{- | @Bool@, tuples and lists (design §2.3, §7.7): the declarations the
compiler holds ("Eval.Builtin"), written exactly so, so that entering
them gives the same hashes. Naming them changes only how they print:
@true@, @(1, 2)@ and @{1, 2}@ print so whatever names them.
-}
builtinData :: [Statement]
builtinData =
  [ Data "structural data Bool = False | True" ["Bool", "False", "True"]
  , Data "structural data Pair a b = Pair a b" ["Pair"]
  , Data "structural data List a = Nil | Cons a (List a)" ["List", "Nil", "Cons"]
  ]

{- | The library as namespace blocks, in the order the source has them
(design §7.7). Inside a block a name resolves in that block first, then
through the block's own @use@s; a sibling's name is otherwise written by
its path (@angle.sr@, @time.hr@), since the seed is entered before any
stored @use@ exists.
-}
stdlibLayout :: [(Text, [Statement])]
stdlibLayout =
  [ ("std", builtinData ++ [Let n e | (n, e) <- structural])
  ,
    ( "linalg"
    , [Let n e | (n, e) <- algebra]
        ++ [Data covarianceData ["Cov2", "rr", "rv", "vv"]]
        ++ [Let n e | (n, e) <- covarianceBlocks]
    )
  , ("si", siStatements)
  ,
    ( "time"
    ,
      [ Unit "min" "60 * s"
      , Unit "hr" "60 * min"
      , Unit "day" "86400 * s"
      , Unit "week" "7 * day"
      , Unit "year" "365.25 * day"
      , Scale "JD" "day at 0 day"
      , Scale "MJD" "day at 2400000.5 day"
      , Scale "J2000" "day at 2451545 day"
      , Scale "unix" "s at 2440587.5 day"
      ]
    )
  ,
    ( "angle"
    ,
      [ Unit "deg" "pi / 180 * rad"
      , Unit "arcmin" "deg / 60"
      , Unit "arcsec" "arcmin / 60"
      , Unit "turn" "2 * pi * rad"
      , Unit "sr" "rad^2"
      ]
    )
  ,
    ( "temperature"
    ,
      [ Unit "deltaC" "K"
      , Unit "deltaF" "5/9 * K"
      , Scale "degC" "K at 273.15 K"
      , Scale "degF" "deltaF at 459.67 deltaF"
      , Scale "degR" "deltaF at 0 deltaF"
      , -- The absolute scale: K's spelled-out name is this scale, not a unit.
        Scale "kelvin" "K at 0 K"
      ]
    )
  ,
    ( "astro"
    ,
      [ Unit "AU" "149597870700 * m"
      , -- IAU 2015: the parsec is exactly 648000/π au; the light-year is
        -- the distance light travels in a Julian year.
        Unit "pc" "648000 / pi * AU"
      , Unit "ly" "physics.c * time.year"
      , Let "GM_earth" "3.986004e14 * m^3 / s^2"
      , Let "GM_sun" "1.3271244e20 * m^3 / s^2"
      , Let "R_earth" "6378100 * m"
      , Let "G" "(6.67430e-11 ±σ 1.5e-15) * m^3 / (kg * s^2)"
      , Let "M_earth" "GM_earth / G"
      , Let "M_sun" "GM_sun / G"
      ]
    )
  ,
    ( "physics"
    ,
      [ UseNs "si"
      , Let "c" "299792458 * m / s"
      , Let "planck" "6.62607015e-34 * J * s"
      , Let "hbar" "planck / (2 * pi)"
      , Let "k_B" "1.380649e-23 * J / K"
      , Let "N_A" "6.02214076e23 / mol"
      , Let "e_charge" "1.602176634e-19 * C"
      , Unit "eV" "e_charge * V"
      , Let "g0" "9.80665 * m / s^2"
      ]
    )
  ,
    ( "imperial"
    , -- Exact by the 1959 international yard and pound; `in` is a keyword.

      [ Unit "inch" "0.0254 * m"
      , Unit "ft" "12 * inch"
      , Unit "yd" "3 * ft"
      , Unit "mile" "1760 * yd"
      , Unit "lb" "0.45359237 * kg"
      , Unit "oz" "lb / 16"
      , Unit "lbf" "lb * physics.g0"
      , Unit "psi" "lbf / inch^2"
      , Unit "mph" "mile / time.hr"
      ]
    )
  ]

-- | The 24 SI prefixes by name, with the symbols of 'prefixes'.
prefixNames :: [(Text, Text)]
prefixNames =
  [ ("Q", "quetta")
  , ("R", "ronna")
  , ("Y", "yotta")
  , ("Z", "zetta")
  , ("E", "exa")
  , ("P", "peta")
  , ("T", "tera")
  , ("G", "giga")
  , ("M", "mega")
  , ("k", "kilo")
  , ("h", "hecto")
  , ("da", "deca")
  , ("d", "deci")
  , ("c", "centi")
  , ("m", "milli")
  , ("µ", "micro")
  , ("u", "micro")
  , ("n", "nano")
  , ("p", "pico")
  , ("f", "femto")
  , ("a", "atto")
  , ("z", "zepto")
  , ("y", "yocto")
  , ("r", "ronto")
  , ("q", "quecto")
  ]

{- | The base units' spelled-out names. @K@ has none: @kelvin@ is the
absolute temperature scale (design §3.6), and a name is one label.
-}
baseNames :: [(Text, Text)]
baseNames =
  [ ("m", "metre")
  , ("s", "second")
  , ("kg", "kilogram")
  , ("A", "ampere")
  , ("mol", "mole")
  , ("cd", "candela")
  , ("rad", "radian")
  ]

{- | The coherent derived units with special names, and the accepted units
the SI keeps beside them: the symbol, the name, the definition.
-}
coherent :: [(Text, Text, Text)]
coherent =
  [ ("N", "newton", "kg * m / s^2")
  , ("J", "joule", "N * m")
  , ("W", "watt", "J / s")
  , ("Pa", "pascal", "N / m^2")
  , ("Hz", "hertz", "1 / s")
  , ("C", "coulomb", "A * s")
  , ("V", "volt", "W / A")
  , ("Ω", "ohm", "V / A")
  , ("F", "farad", "C / V")
  , ("S", "siemens", "A / V")
  , ("T", "tesla", "V * s / m^2")
  , ("H", "henry", "V * s / A")
  , ("Wb", "weber", "V * s")
  , ("lm", "lumen", "cd * angle.sr")
  , ("lx", "lux", "lm / m^2")
  , -- Two units may share a definition (Bq and Hz are both 1/s): a unit is
    -- a name, and a value prints under the name it was written with.
    ("Bq", "becquerel", "1 / s")
  , ("Gy", "gray", "J / kg")
  , ("Sv", "sievert", "J / kg")
  , ("kat", "katal", "mol / s")
  , ("g", "gram", "kg / 1000")
  , ("L", "litre", "(m / 10)^3")
  , ("t", "tonne", "1000 * kg")
  ]

{- | Units that take prefixes, by symbol: the base units except kg (whose
prefixes attach to g), the coherent derived units, g and L. A prefixed
base unit is written with the base unit's name (@kilo * metre@).
-}
siPrefixable :: [Text]
siPrefixable =
  ["m", "s", "A", "K", "mol", "cd", "rad"]
    ++ [u | (u, _, _) <- coherent, u /= "t"]

{- | The SI: base unit names, prefixes, derived units, prefixed units. A
prefix is a plain number written as a power of ten (@kilo = 10^3@), not
as a literal: a term is its content, so @let kilo = 1000@ would be the
same hash as a user's @let n = 1000@, and an @:update@ of that would
upgrade every @k@ unit with it (design §7.5).
-}
siStatements :: [Statement]
siStatements =
  [Unit n b | (b, n) <- baseNames]
    ++ [Let n ("10^" <> T.pack (show k)) | (n, k) <- prefixValues]
    ++ [Unit u e | (u, _, e) <- coherent]
    ++ [Scale "gauge" "Pa at 101325 Pa"]
    ++ [ Unit (p <> u) (n <> " * " <> fromMaybe u (lookup u baseNames))
       | (p, n) <- prefixNames
       , u <- siPrefixable
       , p <> u /= "kg"
       ]
 where
  prefixValues =
    [(n, k) | ((p, n), (p', k)) <- zip prefixNames prefixes, p == p', p /= "u"]

{- | Second labels on a definition (design §7.7): each alias's full path,
then the full path it names. The SI's names for its symbols (@si.newton@
is @si.N@), the prefixed ohms (@si.kohm@ is @si.kΩ@), the hour's symbol
(@time.h@ is @time.hr@), the steradian, and
the short spellings of the physical constants (@physics.h@ is
@physics.planck@, so after @use physics@ a bare @h@ is ambiguous and @hr@
is the hour). An alias of a unit is a unit.
-}
stdlibAliases :: [(Text, Text)]
stdlibAliases =
  [("si." <> n, "si." <> u) | (u, n, _) <- coherent]
    ++ [("si." <> p <> "ohm", "si." <> p <> "Ω") | (p, _) <- prefixNames]
    ++ [ ("time.h", "time.hr")
       , ("angle.steradian", "angle.sr")
       , ("physics.h", "physics.planck")
       , ("physics.kB", "physics.k_B")
       , ("physics.NA", "physics.N_A")
       , ("physics.e", "physics.e_charge")
       ]

-- | The library's namespaces, in the order the source has them.
stdlibNamespaces :: [Text]
stdlibNamespaces = map fst stdlibLayout

{- | The stored @use@s a new codebase is seeded with (design §7.7), in
order. @astro@, @physics@ and @imperial@ are left to @:use@.
-}
stdlibDefaultUses :: [Text]
stdlibDefaultUses = ["std", "linalg", "si", "time", "angle", "temperature"]

{- | The names that were bare before the library was split by domain and
are not now, because they moved to a namespace no stored @use@ reaches:
the constants and @AU@ (design §7.7).
-}
stdlibMovedOut :: [Text]
stdlibMovedOut =
  [ "AU"
  , "G"
  , "GM_earth"
  , "GM_sun"
  , "M_earth"
  , "M_sun"
  , "R_earth"
  , "c"
  , "planck"
  , "k_B"
  , "N_A"
  , "e_charge"
  , "g0"
  ]

-- | Whether a full path is under one of the library's namespaces.
isLibraryPath :: Text -> Bool
isLibraryPath n = any (\ns -> (ns <> ".") `T.isPrefixOf` n) stdlibNamespaces

-- | The standard library as source: one @namespace@ block per domain.
stdlibSource :: Text
stdlibSource =
  T.unlines
    [ line
    | (ns, stmts) <- stdlibLayout
    , line <- ("namespace " <> ns) : map (("  " <>) . render) stmts
    ]
 where
  render = \case
    Let n e -> "let " <> n <> " = " <> e
    Unit n e -> "unit " <> n <> " = " <> e
    Scale n e -> "scale " <> n <> " = " <> e
    UseNs p -> "use " <> p
    Data src _ -> src

{- | Every label the library defines, by its full path (@si.km@), spelled
as the lexer reads it, aliases included: what @:ls@ counts for each
namespace. A type and its constructor of one name are one path, and a
record's fields are labels, which @:ls@ counts but does not list.
-}
stdlibNames :: [Text]
stdlibNames =
  [ prepare (ns <> "." <> l)
  | (ns, stmts) <- stdlibLayout
  , stmt <- stmts
  , l <- case stmt of
      Let n _ -> [n]
      Unit n _ -> [n]
      Scale n _ -> [n]
      UseNs _ -> []
      Data _ ls -> ls
  ]
    ++ map (prepare . fst) stdlibAliases

{- | A codebase seeded with the library (design §7.7): 'stdlibSource'
entered into the empty codebase as one binding group, as @:add@ enters
it, then 'stdlibAliases' bound as @:alias@ binds them, with the stored
default @use@s 'stdlibDefaultUses'. Fails only if the library itself does
not check, which is a build error the tests catch.
-}
stdlibCodebase :: Either Text Codebase
stdlibCodebase = do
  cb <- entered stdlibSource
  aliased <- foldM alias cb stdlibAliases
  pure
    (foldl (flip addStoredUse) aliased [S.Use u Nothing | u <- stdlibDefaultUses])
 where
  alias cb (new, old) =
    let new' = prepare new
        old' = prepare old
        flagged =
          (if isUnitName old' cb then markUnit new' else id)
            . (if isScaleName old' cb then markScale new' else id)
     in case lookupName old' cb of
          Just r -> Right (flagged (bindName new' r cb))
          Nothing -> Left ("the library's alias " <> new <> " names nothing: " <> old)

{- | Where each name of the format-4 library lives now: @std.km@ is
@si.km@, @std.G@ is @astro.G@. A name's home is the label of the current
library with the same last segment, and where two namespaces have one (the
hour @time.h@ and Planck's @physics.h@), the one a stored @use@ reaches,
which is what the bare name meant. The format 4 to 5 migration records the
old reference in the history of the new home (design §7.4).
-}
stdlibHomes :: Either Text [(Text, Text)]
stdlibHomes = do
  old <- stdlib4Codebase
  new <- stdlibCodebase
  let candidates x = [n | n <- Map.keys new.names, S.lastSegment n == x]
      byDefault = filter (\n -> any (\u -> (u <> ".") `T.isPrefixOf` n) stdlibDefaultUses)
      home o = case candidates (S.lastSegment o) of
        [one] -> Just one
        many -> case byDefault many of
          [one] -> Just one
          _ -> Nothing
  pure [(o, h) | o <- Map.keys old.names, Just h <- [home o]]

{- | The references a current library name had in the libraries before it,
oldest first, where they differ from its current one: before the split by
domain, the format-4 library's @std.x@ for its new home, and before that,
for a name whose move under @std@ changed it, the old root prelude's. The
migrations record them as history (design §7.4), and @:stdlib upgrade@
reads a name whose history holds only these below its seeded binding as
untouched.
-}
stdlibMoved :: Either Text [(Text, Reference)]
stdlibMoved = do
  old <- stdlib4Codebase
  root <- stdlib4Moved
  new <- stdlibCodebase
  homes <- stdlibHomes
  pure
    [ (h, r)
    | (o, h) <- homes
    , Just current <- [lookupName h new]
    , r <- [r' | (o', r') <- root, o' == o] ++ maybeToList (lookupName o old)
    , r /= current
    ]

-- | Source entered into the empty codebase as one binding group.
entered :: Text -> Either Text Codebase
entered src = do
  stmts <- parseProgram src
  let (decls, _, _) = S.flatten S.rootScope stmts
  first renderResolveError (processGroup emptyCodebase decls)
