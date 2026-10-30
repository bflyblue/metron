{- | The standard library (design §3.2.11, §7.7): derived SI units, prefixes,
accepted units, exact constants, the Levi-Civita tensor and the cross
product, the structural functions, and a joint covariance in blocks with
its Kalman filter steps (design §3.7), as source text in the language
itself, under the namespace @std@.
A new codebase is seeded with it as one binding group, so every unit is an
ordinary hashed, viewable definition that lives in the codebase like any
other. The prefix table is generated here rather than typed by hand.
-}
module Eval.Prelude (
  stdlibSource,
  stdlibNames,
  stdlibNamespace,
  stdlibCodebase,
  stdlibMoved,
  preludeSource,
) where

import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase (
  Codebase (..),
  Reference,
  addStoredUse,
  emptyCodebase,
  lookupName,
 )
import Eval.Lexer (prepare)
import Eval.Parser (parseProgram)
import Eval.Resolve (processGroup, renderResolveError)
import Eval.Syntax qualified as S

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
entered before it moved under @std@ (design §7.7). 'stdlibSource' is this
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

-- | The namespace the library lives under (design §7.7).
stdlibNamespace :: Text
stdlibNamespace = "std"

{- | Statements the library gained after it moved under @std@: they were
never at the root, so they are not in 'preludeSource' and the migration
records no root history for them (design §7.7).
-}
stdlibAdditions :: Text
stdlibAdditions =
  T.unlines
    (covarianceData : ["let " <> n <> " = " <> e | (n, e) <- covarianceBlocks])

-- | The standard library as source: every statement inside @namespace std@.
stdlibSource :: Text
stdlibSource =
  T.unlines
    ( ("namespace " <> stdlibNamespace)
        : map ("  " <>) (T.lines preludeSource ++ T.lines stdlibAdditions)
    )

{- | Every label the library defines, by its full path (@std.km@), spelled as
the lexer reads it: what @:ls@ counts for @namespace std@. A type and its
constructor of one name are one path, and a record's fields are labels,
which @:ls std@ does not list.
-}
stdlibNames :: [Text]
stdlibNames =
  map
    (\n -> stdlibNamespace <> "." <> prepare n)
    ( map fst derived
        ++ [p <> u | (p, _) <- prefixes, u <- prefixable, p <> u /= "kg"]
        ++ map fst constants
        ++ map fst scales
        ++ map fst algebra
        ++ map fst structural
        -- Cov2 names the type and its constructor; the fields are labels.
        ++ ["Cov2", "rr", "rv", "vv"]
        ++ map fst covarianceBlocks
    )

{- | A codebase seeded with the library (design §7.7): 'stdlibSource'
entered into the empty codebase as one binding group, as @:add@ enters
it, with the stored default @use std@. Fails only if the library itself
does not check, which is a build error the tests catch.
-}
stdlibCodebase :: Either Text Codebase
stdlibCodebase =
  addStoredUse (S.Use stdlibNamespace Nothing) <$> entered stdlibSource

{- | The library names whose reference the move under @std@ changed, each
with the reference the old root prelude gave the bare name: a @±@ is
stamped with its definition's full path (design §3.2.4), so @std.G@ is not
the root @G@, and the masses derived from it differ too. The format 3 to 4
migration records these as history (design §7.4).
-}
stdlibMoved :: Either Text [(Text, Reference)]
stdlibMoved = do
  new <- stdlibCodebase
  old <- entered preludeSource
  pure
    [ (full, r)
    | (n, r) <- Map.toList old.names
    , let full = stdlibNamespace <> "." <> n
    , lookupName full new /= Just r
    ]

-- | Source entered into the empty codebase as one binding group.
entered :: Text -> Either Text Codebase
entered src = do
  stmts <- parseProgram src
  let (decls, _, _) = S.flatten S.rootScope stmts
  first renderResolveError (processGroup emptyCodebase decls)
