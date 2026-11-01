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
-}
module Metron.Prelude (
  stdlibSource,
  stdlibAliases,
  stdlibNames,
  stdlibNamespaces,
  stdlibDefaultUses,
  isLibraryPath,
  stdlibCodebase,
) where

import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T (
  isPrefixOf,
  pack,
  replicate,
  unlines,
  unwords,
 )
import Metron.Codebase (
  Codebase (..),
  addStoredUse,
  bindName,
  emptyCodebase,
  isChartName,
  isUnitName,
  lookupName,
  markChart,
  markUnit,
 )
import Metron.Lexer (prepare)
import Metron.Parser (parseProgram)
import Metron.Resolve (processGroup)
import Metron.Resolve.Error (renderResolveError)
import Metron.Syntax qualified as S (Use (Use), flatten, rootScope)

-- The library's tables -------------------------------------------------------------

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

{- | Tensor algebra: the 3D Levi-Civita tensor, the cross product as the
Hodge dual of the wedge product, the trace as a contraction, and @vimap@,
a map that also sees each component's position as a value (design §3.3).
@vimap@ is for vectors, with the position as one number; the primitive
@timap@ is the general form, at any rank, with the multi-index as a vector.

Then rotations (design §3.3, §3.8): the unit vectors, and the bivectors
that @expm@ turns into rotation matrices. @a ∧ b@ is @a bᵀ − b aᵀ@, which
turns @b@ toward @a@, so @rotz θ@ is @θ (e2 ∧ e1)@ and the right-hand rule
holds. @dual v = ε \@ v@ is the inverse of @⋆@ and @b ∧ a = dual (b × a)@,
so a bivector built from a computed vector is formed as the dual of one
vector, angle and all: every entry is then exactly the negation of its
partner, even when the vector is an enclosure, and @B + Bᵀ@ is exactly
zero. @euler313@ is the composed matrix, for @\@@ and @transformBy@; a
chart is turned by the sequence itself, @by rotz Ω then rotx i then rotz
ω@ (design §3.8). A vector along a chart's axes is read along another's
with @v from c to c1@, and one along its space's base axes along a
chart's with @v to c@ (design §3.10, F10). @rotateVec r v@
and @rotateCov r p@ are a rotation applied to a vector, @r v@, and to a
covariance, @r p rᵀ@, typed by the axes of @r@'s rows and columns;
@transformBy@, along every axis at once, is for anonymous axes only.
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
  , ("e1", "[1, 0, 0]")
  , ("e2", "[0, 1, 0]")
  , ("e3", "[0, 0, 1]")
  , ("rotx", "\\θ -> (θ to rad) / 1 rad * (e3 /\\ e2)")
  , ("roty", "\\θ -> (θ to rad) / 1 rad * (e1 /\\ e3)")
  , ("rotz", "\\θ -> (θ to rad) / 1 rad * (e2 /\\ e1)")
  , ("dual", "\\v -> ε @ v")
  , ("axisAngle", "\\n θ -> dual ((θ to rad) / 1 rad * (-n) / norm n)")
  ,
    ( "rotation"
    , T.unwords
        [ "\\a b -> let c = cross a b in"
        , "if c == 0 * c then"
        , "(if a · b > 0 * (a · b) then [[0, 0, 0], [0, 0, 0], [0, 0, 0]]"
        , "else let k = if cross a e3 == 0 * cross a e3 then e1 else e3 in"
        , "dual (cross k a * pi / norm (cross k a)))"
        , "else dual (-c * (atan2 (norm c) (a · b) / 1 rad) / norm c)"
        ]
    )
  ,
    ( "euler313"
    , "\\raan inc argp -> expm (rotz raan) @ expm (rotx inc) @ expm (rotz argp)"
    )
  , -- r v, written so that r is known to be a matrix
    ("rotateVec", "\\r v -> transpose (transpose r) @ v")
  , -- r p rᵀ, written so that both operands are known to be matrices
    ("rotateCov", "\\r p -> r @ transpose (r @ transpose p)")
  ]

{- | A body's state (design §3.8, §3.10): its epoch, a point on a time
frame, and its position and velocity as amounts along a space's base
axes, the position from the base origin: the velocity relative to the
space's base, the inertial frame. @velocityIn c s@ is that velocity
relative to chart @c@, along @c@'s axes, with the transport terms of a
moving chart:

@
v_c = R_abs⁻¹ (v − v_o − ω_abs × (p − o_abs))
@

with @R_abs@ the chart's rotation, @o_abs@ its origin, @v_o@ the velocity
of its origin and @ω_abs@ its angular velocity, all from the base
(@rotationOf@, @originOf@, @originVelocityOf@, @spinOf@), @R_abs⁻¹@ being
@to c@. @stateFrom c t pc vc@ is the inverse: a position @pc@ and a
velocity @vc@ along @c@'s axes, relative to @c@, to a state, @p = o_abs +
R_abs pc@ and @v = R_abs vc + v_o + ω_abs × (p − o_abs)@. A chart with
parameters is passed at the state's instant, @velocityIn (ecef s.epoch)
s@. Their inferred types retain the space constraint
@(s : Space (Vec 3 m))@ when printed.
-}
stateStatements :: [Statement]
stateStatements =
  [ Data
      "data State t r = State {epoch :: Point t, pos :: Vec r m, vel :: Vec r (m/s)}"
      ["State", "epoch", "pos", "vel"]
  , Let
      "velocityIn"
      ( T.unwords
          [ "\\c st ->"
          , "(st.vel - originVelocityOf c - linalg.cross (spinOf c) (st.pos - originOf c)) to c"
          ]
      )
  , Let
      "stateFrom"
      ( T.unwords
          [ "\\c t pc vc -> let r = rotationOf c @ pc in"
          , "State {epoch = t, pos = originOf c + r,"
          , "vel = rotationOf c @ vc + originVelocityOf c + linalg.cross (spinOf c) r}"
          ]
      )
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
  , -- Strict in the accumulator (design §7.7): each step's is evaluated first.
    ("foldl'", "\\f z xs -> case xs of {} -> z; x : rest -> let z_ = f z x in seq z_ (foldl' f z_ rest)")
  , ("length", "\\xs -> foldl' (\\n _ -> n + 1) 0 xs")
  , ("reverse", "\\xs -> foldl' (\\acc x -> x : acc) {} xs")
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
  "data Cov2 n d1 d2 = Cov2 {rr :: Mat n n (d1^2), rv :: Mat n n (d1*d2), vv :: Mat n n (d2^2)}"

{- | The block filter over 'covarianceData'. @propagateCov2@ forms the block
rows of @Φ P@ first and multiplies them by the block columns of @Φᵀ@;
expanded, @rr' = Φ_rr rr Φ_rrᵀ + Φ_rv rvᵀ Φ_rrᵀ + Φ_rr rv Φ_rvᵀ + Φ_rv vv
Φ_rvᵀ@. @gain2@ returns the pair @(K_r, K_v)@ of the gain's block rows.
@updateCov2@ is @P − K (H P)@ with @H P = (P Hᵀ)ᵀ@, since @P@ is
symmetric: written with @transpose h_r@ the measurement matrices have a
known rank, where @h_r \@ p.rr@ alone would default @h_r@ to a vector
(design §4.2). @inChartCov2 c p@ reads a block covariance as given along
the axes of chart @c@ and gives it along its root's axes: each block is
@R P Rᵀ@ ('rotateCov'), since the state's rotation is @R@ on positions and on
velocities alike (design §3.8).
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
  ,
    ( "inChartCov2"
    , T.unwords
        [ "\\c p -> let r = rotationOf c in"
        , "Cov2 {rr = rotateCov r p.rr, rv = rotateCov r p.rv, vv = rotateCov r p.vv}"
        ]
    )
  ]

-- Astrodynamics ---------------------------------------------------------------------

{- | A body of a constant set (design §7.7): its gravitational parameter,
equatorial radius, flattening, second zonal harmonic and rotation rate.
A field its source does not define is an exact zero, and the set's
comments say which.

@
field       type           unit
mu          Num (m^3/s^2)  GM, with any atmosphere the source includes
radius      Num m          equatorial radius
flattening  Num            (a - b) / a
j2          Num            -C20 unnormalised; -√5 C̄20 from a normalised one
rate        Num (rad/s)    rotation rate
@
-}
bodyData :: Text
bodyData =
  "data Body = Body {mu :: Num (m^3/s^2), radius :: Num m, flattening :: Num, j2 :: Num, rate :: Num (rad/s)}"

{- | WGS 84, the Earth that GPS and Vallado use: NIMA TR8350.2, 3rd
edition with Amendments 1 and 2 (2000, 2004), and the EGM96 C̄20 for J2.

* @mu@: GM = 3986004.418 × 10⁸ m³/s², atmosphere included, eq. (3-3)
  and Table 3.1. A defining parameter, so exact; eq. (3-3) quotes its
  measured 1σ of 0.008 × 10⁸ m³/s².
* @radius@: a = 6378137.0 m, eq. (3-1) and Table 3.1, defining.
* @flattening@: 1/f = 298.257223563, eq. (3-2) and Table 3.1, defining.
* @j2@: J2 = −√5 C̄20 (TR8350.2 eq. 7-1), with the EGM96 dynamic C̄20 =
  −0.484165371736 × 10⁻³, σ = 0.35610635 × 10⁻¹⁰, tide-free, epoch 1986.0
  (Lemoine et al., NASA/TP-1998-206861, Appendix C, p. C-1; TR8350.2
  Table 5.1 and §3.3.1 say to use it for orbits, not the ellipsoid's
  geometric −0.484166774985 × 10⁻³ of Table 3.3). The σ is taken as a
  standard uncertainty.
* @rate@: ω = 7292115 × 10⁻¹¹ rad/s, eq. (3-6) and Table 3.1, defining.
-}
wgs84 :: [Statement]
wgs84 =
  [ Let
      "earth"
      ( T.unwords
          [ "astro.Body {mu = 3986004.418e8 m^3/s^2, radius = 6378137 m,"
          , "flattening = 1 / 298.257223563,"
          , "j2 = sqrt 5 * (0.484165371736e-3 ±σ 0.35610635e-10),"
          , "rate = 7292115e-11 rad/s}"
          ]
      )
  ]

{- | The IERS Conventions (2010), IERS Technical Note 36 (Petit and
Luzum), chapter 1. Its Table 1.1 gives geocentric values compatible with
TCG and heliocentric ones with TCB, as printed here; its uncertainties
are taken as standard uncertainties.

* Earth: GM⊕ = 3.986004418 × 10¹⁴ ± 8 × 10⁵ m³/s² (TCG; Table 1.1);
  a_E = 6378136.6 ± 0.1 m and 1/f = 298.25642 ± 0.00001 (zero tide;
  Table 1.1); J2 = 1.0826359 × 10⁻³ ± 1 × 10⁻¹⁰ (zero tide; Table 1.1).
  Table 1.1 has no rotation rate, so the rate is Table 1.2's nominal mean
  angular velocity, 7.292115 × 10⁻⁵ rad/s, exact.
* Moon: GM = μ GM⊕ with the Moon-Earth mass ratio μ = 0.0123000371 ±
  4 × 10⁻¹⁰ (Table 1.1), so it shares the Earth's uncertainty. The table
  gives no radius, flattening, J2 or rate: exact zeros.
* Sun: GM☉ = 1.32712442099 × 10²⁰ ± 1 × 10¹⁰ m³/s² (TCB; Table 1.1);
  J2☉ = 2.0 × 10⁻⁷, adopted for DE421 (Table 1.1), exact. No radius,
  flattening or rate: exact zeros.
-}
iers2010 :: [Statement]
iers2010 =
  UseNs "astro"
    : [ Let
          "earth"
          ( T.unwords
              [ "astro.Body {mu = (3.986004418e14 ±σ 8e5) * 1 m^3/s^2,"
              , "radius = (6378136.6 ±σ 0.1) * 1 m,"
              , "flattening = 1 / (298.25642 ±σ 0.00001),"
              , "j2 = 1.0826359e-3 ±σ 1e-10,"
              , "rate = 7.292115e-5 rad/s}"
              ]
          )
      , Let
          "moon"
          ( T.unwords
              [ "astro.Body {mu = (0.0123000371 ±σ 4e-10) * earth.mu,"
              , "radius = 0 m, flattening = 0, j2 = 0, rate = 0 rad/s}"
              ]
          )
      , Let
          "sun"
          ( T.unwords
              [ "astro.Body {mu = (1.32712442099e20 ±σ 1e10) * 1 m^3/s^2,"
              , "radius = 0 m, flattening = 0, j2 = 2.0e-7, rate = 0 rad/s}"
              ]
          )
      ]

{- | IAU 2015 Resolution B3, the nominal solar and planetary conversion
constants (also Prša et al. 2016, AJ 152:41, Table 1): exact by
definition (Recommends 1 and 2). The flattening is derived from the
nominal equatorial and polar radii, (R_e − R_p) / R_e; the resolution
defines no J2 or rotation rate, so those are exact zeros, and the Sun's
flattening is zero too. Jupiter's GM is Jupiter alone, without the
Galilean satellites (Explanation 8).

* Earth: (GM)_E = 3.986004 × 10¹⁴ m³/s², R_eE = 6.3781 × 10⁶ m,
  R_pE = 6.3568 × 10⁶ m.
* Sun: (GM)☉ = 1.3271244 × 10²⁰ m³/s², R☉ = 6.957 × 10⁸ m.
* Jupiter: (GM)_J = 1.2668653 × 10¹⁷ m³/s², R_eJ = 7.1492 × 10⁷ m,
  R_pJ = 6.6854 × 10⁷ m.
-}
iau2015 :: [Statement]
iau2015 =
  [ Let
      "earth"
      ( T.unwords
          [ "astro.Body {mu = 3.986004e14 m^3/s^2, radius = 6.3781e6 m,"
          , "flattening = (6.3781e6 - 6.3568e6) / 6.3781e6, j2 = 0, rate = 0 rad/s}"
          ]
      )
  , Let
      "sun"
      ( T.unwords
          [ "astro.Body {mu = 1.3271244e20 m^3/s^2, radius = 6.957e8 m,"
          , "flattening = 0, j2 = 0, rate = 0 rad/s}"
          ]
      )
  , Let
      "jupiter"
      ( T.unwords
          [ "astro.Body {mu = 1.2668653e17 m^3/s^2, radius = 7.1492e7 m,"
          , "flattening = (7.1492e7 - 6.6854e7) / 7.1492e7, j2 = 0, rate = 0 rad/s}"
          ]
      )
  ]

{- | JPL DE440: the GMs of Park, Folkner, Williams and Boggs (2021), "The
JPL Planetary and Lunar Ephemerides DE440 and DE441", AJ 161:105, Table
2, in km³/s², compatible with TDB. The paper publishes no uncertainties
for them, so they are exact. From Mars outwards a GM is the planet's
system, satellites included, and Pluto's is the Pluto system's.

The radii and J2s of the Earth, the Moon and the Sun are the ephemeris
header's (header.440, groups 1040 and 1041): RE = 6378.1366 km,
J2E = 1.08262539 × 10⁻³, AM = 1738 km, J2M = 2.03214360135 × 10⁻⁴,
ASUN = 696000 km (also the paper, p. 7) and J2SUN as printed,
0.219613915165298248 × 10⁻⁶. The header prints IEEE doubles to 18 digits
(RE as 0.637813659999999982D+04); a value is written as the shortest
decimal that prints so, where one is evident. DE440 defines no
flattening or rotation rate for any body, and no radius or J2 for the
planets: exact zeros.
-}
de440 :: [Statement]
de440 =
  UseNs "si"
    : [ Let n (gm v r j)
      | (n, v, r, j) <-
          [ ("sun", "132712440041.279419", "696000", "0.219613915165298248e-6")
          , ("mercury", "22031.868551", "0", "0")
          , ("venus", "324858.592000", "0", "0")
          , ("earth", "398600.435507", "6378.1366", "1.08262539e-3")
          , ("moon", "4902.800118", "1738", "2.03214360135e-4")
          , ("mars", "42828.375816", "0", "0")
          , ("jupiter", "126712764.100000", "0", "0")
          , ("saturn", "37940584.841800", "0", "0")
          , ("uranus", "5794556.400000", "0", "0")
          , ("neptune", "6836527.100580", "0", "0")
          , ("pluto", "975.500000", "0", "0")
          ]
      ]
 where
  gm v r j =
    T.unwords
      [ "astro.Body {mu =" <> " " <> v <> " km^3/s^2, radius = " <> r <> " km,"
      , "flattening = 0, j2 = " <> j <> ", rate = 0 rad/s}"
      ]

{- | Two-body motion (design §7.7): the relations of the conic, the
classical elements and their conversions to and from a position and a
velocity, the anomalies, a Kepler solver for each conic, analytic
propagation and the J2 secular rates. Every function that needs a body
takes one, so a computation names its constants once.

Elements are elliptic or hyperbolic (@a < 0@, as Vallado writes it). The
special cases keep the record's shape: a circular orbit has @argp = 0@
and @nu@ the argument of latitude; an equatorial one has @raan = 0@ and
@argp@ the longitude of periapsis; a circular equatorial one has both
zero and @nu@ the true longitude. A case is decided by comparison with
zero, so a value too uncertain to decide is an error, and every angle
comes from @atan2@. @fromState@ gives angles in [0, 2π), as Vallado
does; an angle at the cut, near zero and uncertain, is an error.

The solvers (design §7.7) iterate Newton's method on midpoints, from a
starter, for a fixed number of steps, then take one step on the values
themselves, so that the result carries the inputs' uncertainty to first
order, and declare the truncation error as a bound: for Kepler's
equation @f(E) = E − e sin E − M@, @f' ≥ 1 − e@, so @|E − E*| ≤ |f(E)| /
(1 − e)@, and for the hyperbola @f' ≥ e − 1@. The parabola is solved in
closed form (Barker).
-}
kepler :: [Statement]
kepler =
  [ UseNs "astro"
  , Data
      "data Elements = Elements {a :: Num m, e :: Num, i :: Num rad, raan :: Num rad, argp :: Num rad, nu :: Num rad}"
      ["Elements", "a", "e", "i", "raan", "argp", "nu"]
  , -- Relations (Vallado §1.3, §2.2): a is negative for a hyperbola.
    Sig "period" "Body -> Num m -> Num s"
  , Let "period" "\\body a -> 2 * pi * sqrt (a^3 / body.mu)"
  , Sig "meanMotion" "Body -> Num m -> Num (rad/s)"
  , Let "meanMotion" "\\body a -> sqrt (body.mu / (abs a)^3) * 1 rad"
  , Sig "visViva" "Body -> Num m -> Num m -> Num (m/s)"
  , Let "visViva" "\\body r a -> sqrt (body.mu * (2 / r - 1 / a))"
  , Sig "energy" "Body -> Num m -> Num (m^2/s^2)"
  , Let "energy" "\\body a -> -(body.mu / (2 * a))"
  , Sig "momentum" "Body -> Num m -> Num (m^2/s)"
  , Let "momentum" "\\body p -> sqrt (body.mu * p)"
  , Sig "circular" "Body -> Num m -> Num (m/s)"
  , Let "circular" "\\body r -> sqrt (body.mu / r)"
  , Sig "escape" "Body -> Num m -> Num (m/s)"
  , Let "escape" "\\body r -> sqrt (2 * body.mu / r)"
  , Let "semilatus" "\\el -> el.a * (1 - el.e^2)"
  , -- The angle of (x, y) in [0, 2π): exactly zero on the positive x axis.
    Let
      "fullAngle"
      ( T.unwords
          [ "\\y x -> if mid y == 0 * mid y && bound y == 0 * bound y"
          , "&& sd y == 0 * sd y && x > 0 * x"
          , "then 0 rad else pi * 1 rad + atan2 (-y) (-x)"
          ]
      )
  , -- The angle from d to w in the plane normal to h, positive about h.
    Let "angleIn" "\\h d w -> fullAngle (h · linalg.cross d w) (norm h * (d · w))"
  , -- Vallado algorithm 10 (COE2RV): the perifocal axes P and Q, the
    -- first two columns of the 3-1-3 rotation Rz(raan) Rx(i) Rz(argp),
    -- written out in sines and cosines, which carry statistical
    -- uncertainty where expm does not yet.
    Let
      "toState"
      ( T.unwords
          [ "\\body el -> let p = semilatus el in"
          , "let co = cos el.raan in let so = sin el.raan in"
          , "let cw = cos el.argp in let sw = sin el.argp in"
          , "let ci = cos el.i in let si = sin el.i in"
          , "let pv = [co * cw - so * sw * ci, so * cw + co * sw * ci, sw * si] in"
          , "let qv = [-(co * sw) - so * cw * ci, co * cw * ci - so * sw, cw * si] in"
          , "let r = p / (1 + el.e * cos el.nu) in"
          , "(r * cos el.nu * pv + r * sin el.nu * qv,"
          , "sqrt (body.mu / p) * (-(sin el.nu) * pv + (el.e + cos el.nu) * qv))"
          ]
      )
  , -- Vallado algorithm 9 (RV2COE), with atan2 for every angle.
    Let
      "fromState"
      ( T.unwords
          [ "\\body r v -> let mu = body.mu in"
          , "let h = linalg.cross r v in"
          , "let n = [-h.1, h.0, 0 * h.0] in"
          , "let rn = norm r in"
          , "let ev = ((v · v - mu / rn) * r - (r · v) * v) / mu in"
          , "let circ = ev == 0 * ev in"
          , "let equat = n == 0 * n in"
          , "let x = [1, 0, 0] in"
          , "Elements {a = -(mu / (v · v - 2 * mu / rn)),"
          , "e = if circ then 0 else norm ev,"
          , "i = atan2 (norm n) h.2,"
          , "raan = if equat then 0 rad else fullAngle n.1 n.0,"
          , "argp = if circ then 0 rad else if equat then angleIn h x ev else angleIn h n ev,"
          , "nu = if circ then (if equat then angleIn h x r else angleIn h n r) else angleIn h ev r}"
          ]
      )
  , -- Anomalies (Vallado §2.2, algorithms 5 and 6).
    Let
      "trueToEccentric"
      "\\e nu -> fullAngle (sqrt (1 - e^2) * sin nu) (e + cos nu)"
  , Let
      "eccentricToTrue"
      "\\e ea -> fullAngle (sqrt (1 - e^2) * sin ea) (cos ea - e)"
  , Let "eccentricToMean" "\\e ea -> ea - e * sin ea * 1 rad"
  , Let "asinh" "\\x -> log (x + sqrt (x^2 + 1))"
  , Let
      "trueToHyperbolic"
      "\\e nu -> asinh (sqrt (e^2 - 1) * sin nu / (1 + e * cos nu)) * 1 rad"
  , Let
      "hyperbolicToTrue"
      "\\e h -> atan2 (sqrt (e^2 - 1) * sinh (h / 1 rad)) (e - cosh (h / 1 rad))"
  , Let "hyperbolicToMean" "\\e h -> e * sinh (h / 1 rad) * 1 rad - h"
  , Let "trueToParabolic" "\\nu -> tan (nu / 2)"
  , Let "parabolicToTrue" "\\b -> 2 * atan b"
  , Let "parabolicToMean" "\\b -> b + b^3 / 3"
  , -- Kepler's equation, elliptic: Newton from M + e sin M.
    Let "newtonE" "\\e m x -> x - (x - e * sin x * 1 rad - m) / (1 - e * cos x)"
  , Let
      "newtonStepsE"
      "\\k e m x -> if k == 0 then x else newtonStepsE (k - 1) e m (mid (newtonE e m x))"
  , Let
      "meanToEccentric"
      ( T.unwords
          [ "\\e m -> let em = mid e in let mm = mid m in"
          , "let x = newtonE e m (newtonStepsE 10 em mm (mm + em * sin mm * 1 rad)) in"
          , "let r = x - e * sin x * 1 rad - m in"
          , "x ± (abs (mid r) + bound r) / (1 - (mid e + bound e))"
          ]
      )
  , -- Hyperbolic: Newton from asinh (M / (e - 1)), which is not below the
    -- root for M > 0, where f is convex.
    Let
      "newtonH"
      "\\e m x -> x - (e * sinh (x / 1 rad) * 1 rad - x - m) / (e * cosh (x / 1 rad) - 1)"
  , Let
      "newtonStepsH"
      "\\k e m x -> if k == 0 then x else newtonStepsH (k - 1) e m (mid (newtonH e m x))"
  , Let
      "meanToHyperbolic"
      ( T.unwords
          [ "\\e m -> let em = mid e in let mm = mid m in"
          , "let x = newtonH e m (newtonStepsH 10 em mm (asinh (mm / (em - 1) / 1 rad) * 1 rad)) in"
          , "let r = e * sinh (x / 1 rad) * 1 rad - x - m in"
          , "x ± (abs (mid r) + bound r) / (mid e - bound e - 1)"
          ]
      )
  , -- Parabolic: B + B³/3 = M in closed form, B = c − 1/c with
    -- c³ = 3M/2 + √(1 + 9M²/4) (Vallado algorithm 3, Barker's equation).
    Let
      "meanToParabolic"
      "\\mp -> let c = exp (log (3 * mp / 2 + sqrt (1 + 9 * mp^2 / 4)) / 3) in c - 1 / c"
  , Sig "barker" "Body -> Num m -> Num s -> Num"
  , Let "barker" "\\body p dt -> meanToParabolic (2 * sqrt (body.mu / p^3) * dt)"
  , Let
      "trueToMean"
      ( T.unwords
          [ "\\e nu -> if e < 1 then eccentricToMean e (trueToEccentric e nu)"
          , "else hyperbolicToMean e (trueToHyperbolic e nu)"
          ]
      )
  , Let
      "meanToTrue"
      ( T.unwords
          [ "\\e m -> if e < 1 then eccentricToTrue e (meanToEccentric e m)"
          , "else hyperbolicToTrue e (meanToHyperbolic e m)"
          ]
      )
  , -- Two-body propagation by the mean anomaly (Vallado algorithm 7).
    Let
      "propagate"
      "\\body el dt -> el {nu = meanToTrue el.e (trueToMean el.e el.nu + meanMotion body el.a * dt)}"
  , -- J2 secular rates (Vallado eqs. 9-41, 9-42; Curtis eqs. 4.52, 4.53).
    Let
      "nodeRate"
      "\\body el -> -(3 / 2 * meanMotion body el.a * body.j2 * (body.radius / semilatus el)^2 * cos el.i)"
  , Let
      "perigeeRate"
      "\\body el -> 3 / 4 * meanMotion body el.a * body.j2 * (body.radius / semilatus el)^2 * (4 - 5 * (sin el.i)^2)"
  , -- The node rate of a sun-synchronous orbit, 360° in a mean tropical
    -- year of 365.2421897 days (Vallado §11.4.1 and Example 11-2,
    -- 1.991 063 853 × 10⁻⁷ rad/s).
    Let "sunSyncRate" "360 angle.deg / (365.2421897 time.day)"
  , Let
      "sunSynchronous"
      "\\body a e -> acos (-(2 / 3 * sunSyncRate * (a * (1 - e^2))^2 / (meanMotion body a * body.j2 * body.radius^2)))"
  , Let
      "propagateJ2"
      ( T.unwords
          [ "\\body el dt -> (propagate body el dt)"
          , "{raan = el.raan + nodeRate body el * dt, argp = el.argp + perigeeRate body el * dt}"
          ]
      )
  ]

{- | Impulsive manoeuvres (design §7.7; Vallado chapter 6): each burn is
signed, the velocity after it less the velocity before it, so a burn
that lowers an orbit is negative, and 'total' adds their sizes. A
transfer with two burns has @dv3 = 0@.
-}
maneuver :: [Statement]
maneuver =
  [ UseNs "astro"
  , Data
      "data Transfer = Transfer {dv1 :: Num (m/s), dv2 :: Num (m/s), dv3 :: Num (m/s), tof :: Num s}"
      ["Transfer", "dv1", "dv2", "dv3", "tof"]
  , Let "total" "\\t -> abs t.dv1 + abs t.dv2 + abs t.dv3"
  , -- Between circular orbits (Vallado algorithm 36).
    Let
      "hohmann"
      ( T.unwords
          [ "\\body r1 r2 -> let mu = body.mu in let ta = (r1 + r2) / 2 in"
          , "Transfer {dv1 = sqrt (mu * (2 / r1 - 1 / ta)) - sqrt (mu / r1),"
          , "dv2 = sqrt (mu / r2) - sqrt (mu * (2 / r2 - 1 / ta)),"
          , "dv3 = 0 m/s, tof = pi * sqrt (ta^3 / mu)}"
          ]
      )
  , -- Through an intermediate apoapsis rb (Vallado algorithm 37).
    Let
      "biElliptic"
      ( T.unwords
          [ "\\body r1 rb r2 -> let mu = body.mu in"
          , "let a1 = (r1 + rb) / 2 in let a2 = (rb + r2) / 2 in"
          , "Transfer {dv1 = sqrt (mu * (2 / r1 - 1 / a1)) - sqrt (mu / r1),"
          , "dv2 = sqrt (mu * (2 / rb - 1 / a2)) - sqrt (mu * (2 / rb - 1 / a1)),"
          , "dv3 = sqrt (mu / r2) - sqrt (mu * (2 / r2 - 1 / a2)),"
          , "tof = pi * (sqrt (a1^3 / mu) + sqrt (a2^3 / mu))}"
          ]
      )
  , -- An inclination change at speed v and flight-path angle fpa
    -- (Vallado eq. 6-27).
    Sig "planeChange" "forall d. Num d -> Num rad -> Num rad -> Num d"
  , Let "planeChange" "\\v fpa di -> 2 * v * cos fpa * sin (di / 2)"
  , -- A burn that changes the speed from v1 to v2 and turns the plane by
    -- di (Vallado eq. 6-30, the law of cosines).
    Let "combinedChange" "\\v1 v2 di -> sqrt (v1^2 + v2^2 - 2 * v1 * v2 * cos di)"
  , -- The angle between two orbit planes (Vallado eq. 6-28): for a change
    -- of node, or of node and inclination, at a circular orbit's speed.
    Let
      "rotationAngle"
      "\\i1 i2 draan -> acos (cos i1 * cos i2 + sin i1 * sin i2 * cos draan)"
  , -- Phasing within one circular orbit of radius a: catch up phase in
    -- k revolutions of a phasing orbit, both burns at the burn point
    -- (Vallado algorithm 44).
    Let
      "phasing"
      ( T.unwords
          [ "\\body a phase k -> let mu = body.mu in"
          , "let w = sqrt (mu / a^3) * 1 rad in"
          , "let tau = (2 * pi * k * 1 rad + phase) / w in"
          , "let aph = a * exp (2 / 3 * log (tau * w / (2 * pi * k * 1 rad))) in"
          , "let dv = sqrt (2 * mu / a - mu / aph) - sqrt (mu / a) in"
          , "Transfer {dv1 = dv, dv2 = -dv, dv3 = 0 m/s, tof = tau}"
          ]
      )
  ]

-- The library by domain ------------------------------------------------------------

-- | One statement of the library's source.
data Statement
  = Let Text Text
  | -- | a signature (design §4.8): the name and its type
    Sig Text Text
  | Unit Text Text
  | Chart Text Text
  | -- | a space (design §3.10, F2): its name and its amounts' type
    SpaceDecl Text Text
  | -- | a @use@ inside the block, for names of a sibling namespace
    UseNs Text
  | {- | a @data@ declaration, and its labels: the type, its constructors
    where they are not the type's name, then its fields
    -}
    Data Text [Text]
  | -- | a nested @namespace@ block (design §7.6): its last segment and body
    Namespace Text [Statement]

{- | @Bool@, tuples and lists (design §2.3, §7.7): the declarations the
compiler holds ("Metron.Builtin"), written exactly so, so that entering
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
    , [Let n e | (n, e) <- algebra, n /= "vimap"]
        -- vimap over timap, signed so it stays vector-only (design §3.3)
        ++ [ Sig "vimap" "forall d d1 n. (Num -> Num d -> Num d1) -> Vec n d -> Vec n d1"
           , Let "vimap" "\\f v -> timap (\\i x -> f i.0 x) v"
           ]
        ++ [Data covarianceData ["Cov2", "rr", "rv", "vv"]]
        ++ [Let n e | (n, e) <- covarianceBlocks]
    )
  , ("si", siStatements)
  ,
    ( "time"
    ,
      [ Unit "min" "60 s"
      , Unit "hr" "60 min"
      , Unit "day" "86400 s"
      , Unit "week" "7 day"
      , Unit "year" "365.25 day"
      , SpaceDecl "TT" "Num s"
      , Chart "JD" "on TT step day"
      , Chart "MJD" "on TT at 2400000.5 day step day"
      , Chart "J2000" "on TT at 2451545 day step day"
      , -- UTC is not an affine map of TT (leap seconds): no chart joins them.
        SpaceDecl "UTC" "Num s"
      , Chart "unix" "on UTC"
      ]
    )
  ,
    ( "angle"
    ,
      [ Unit "deg" "pi / 180 * 1 rad"
      , Unit "arcmin" "1 deg / 60"
      , Unit "arcsec" "1 arcmin / 60"
      , Unit "turn" "2 * pi * 1 rad"
      , Unit "sr" "rad^2"
      ]
    )
  ,
    ( "temperature"
    ,
      [ Unit "deltaC" "K"
      , Unit "deltaF" "5/9 * 1 K"
      , SpaceDecl "ITS90" "Num K"
      , Chart "degC" "on ITS90 at 273.15 K"
      , Chart "degF" "on ITS90 at 459.67 deltaF step deltaF"
      , -- Rankine is a rescaling of kelvin: one frame (design §3.10, F3).
        Chart "degR" "on kelvin step deltaF"
      , -- The absolute scale: K's spelled-out name is this scale, not a unit.
        Chart "kelvin" "on ITS90"
      ]
    )
  ,
    ( "astro"
    , [ Unit "AU" "149597870700 m"
      , -- IAU 2015: the parsec is exactly 648000/π au; the light-year is
        -- the distance light travels in a Julian year.
        Unit "pc" "648000 / pi * 1 AU"
      , Unit "ly" "physics.c * 1 time.year"
      , -- CODATA 2018, unchanged in CODATA 2022: 6.674 30(15) × 10⁻¹¹
        -- m³ kg⁻¹ s⁻², a standard uncertainty (NIST, physics.nist.gov,
        -- "Newtonian constant of gravitation").
        Let "G" "(6.67430e-11 ±σ 1.5e-15) * 1 m^3 kg^-1 s^-2"
      ]
        ++ stateStatements
        ++ [Data bodyData ["Body", "mu", "radius", "flattening", "j2", "rate"]]
        ++ [ Namespace "wgs84" wgs84
           , Namespace "iers2010" iers2010
           , Namespace "iau2015" iau2015
           , Namespace "de440" de440
           , Namespace "kepler" kepler
           , Namespace "maneuver" maneuver
           ]
    )
  ,
    ( "physics"
    ,
      [ UseNs "si"
      , Let "c" "299792458 m/s"
      , Let "planck" "6.62607015e-34 J s"
      , Let "hbar" "planck / (2 * pi)"
      , Let "k_B" "1.380649e-23 J/K"
      , Let "N_A" "6.02214076e23 mol^-1"
      , Let "e_charge" "1.602176634e-19 C"
      , Unit "eV" "e_charge * 1 V"
      , Let "g0" "9.80665 m/s^2"
      ]
    )
  ,
    ( "imperial"
    , -- Exact by the 1959 international yard and pound; `in` is a keyword.

      [ Unit "inch" "0.0254 m"
      , Unit "ft" "12 inch"
      , Unit "yd" "3 ft"
      , Unit "mile" "1760 yd"
      , Unit "lb" "0.45359237 kg"
      , Unit "oz" "1 lb / 16"
      , Unit "lbf" "1 lb * physics.g0"
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
  , ("Hz", "hertz", "s^-1")
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
    ("Bq", "becquerel", "s^-1")
  , ("Gy", "gray", "J / kg")
  , ("Sv", "sievert", "J / kg")
  , ("kat", "katal", "mol / s")
  , ("g", "gram", "1 kg / 1000")
  , ("L", "litre", "(1 m / 10)^3")
  , ("t", "tonne", "1000 kg")
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
    ++ [ Unit (p <> u) (n <> " * 1 " <> fromMaybe u (lookup u baseNames))
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

-- | Whether a full path is under one of the library's namespaces.
isLibraryPath :: Text -> Bool
isLibraryPath n = any (\ns -> (ns <> ".") `T.isPrefixOf` n) stdlibNamespaces

-- | The standard library as source: one @namespace@ block per domain.
stdlibSource :: Text
stdlibSource =
  T.unlines (concat [block 0 ns stmts | (ns, stmts) <- stdlibLayout])
 where
  -- A block's statements are indented one step further than its header,
  -- and a nested block's further still (design §7.6).
  block depth ns stmts =
    (indent depth <> "namespace " <> ns) : concatMap (render (depth + 1)) stmts
  indent depth = T.replicate depth "  "
  render depth = \case
    Namespace ns stmts -> block depth ns stmts
    Let n e -> [indent depth <> "let " <> n <> " = " <> e]
    Sig n t -> [indent depth <> n <> " :: " <> t]
    Unit n e -> [indent depth <> "unit " <> n <> " = " <> e]
    Chart n e -> [indent depth <> "chart " <> n <> " " <> e]
    SpaceDecl n t -> [indent depth <> "space " <> n <> " = " <> t]
    UseNs p -> [indent depth <> "use " <> p]
    Data src _ -> [indent depth <> src]

{- | Every label the library defines, by its full path (@si.km@,
@astro.wgs84.earth@), spelled as the lexer reads it, aliases included:
what @:ls@ counts for each namespace. A type and its constructor of one
name are one path, and a record's fields are labels, which @:ls@ counts
but does not list.
-}
stdlibNames :: [Text]
stdlibNames =
  map prepare (concat [labels ns stmts | (ns, stmts) <- stdlibLayout])
    ++ map (prepare . fst) stdlibAliases
 where
  labels ns = concatMap $ \case
    Namespace inner stmts -> labels (ns <> "." <> inner) stmts
    Let n _ -> [ns <> "." <> n]
    Sig _ _ -> []
    Unit n _ -> [ns <> "." <> n]
    Chart n _ -> [ns <> "." <> n]
    SpaceDecl n _ -> [ns <> "." <> n]
    UseNs _ -> []
    Data _ ls -> map ((ns <> ".") <>) ls

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
            . (if isChartName old' cb then markChart new' else id)
     in case lookupName old' cb of
          Just r -> Right (flagged (bindName new' r cb))
          Nothing -> Left ("the library's alias " <> new <> " names nothing: " <> old)

-- | Source entered into the empty codebase as one binding group.
entered :: Text -> Either Text Codebase
entered src = do
  stmts <- parseProgram src
  let (decls, _, _) = S.flatten S.rootScope stmts
  first renderResolveError (processGroup emptyCodebase decls)
