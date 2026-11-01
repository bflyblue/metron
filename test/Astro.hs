{- | The @astro@ library (design §7.7): the constant sets, @astro.kepler@
and @astro.maneuver@, each function checked against a published worked
example, cited, within a stated tolerance, and the conversions by round
trips.

The references:

* Vallado, /Fundamentals of Astrodynamics and Applications/, 4th ed.
  (Microcosm, 2013), with its June 2019 errata: examples 2-1 to 2-6 and
  6-1 to 6-8, and 11-2. Chapter 6 works in canonical units with
  μ = 398600.4418 km³/s² and R = 6378.137 km, which is @astro.wgs84.earth@'s
  μ.
* Curtis, /Orbital Mechanics for Engineering Students/, 4th ed. (Elsevier,
  2020), with μ = 398600 km³/s², R = 6378 km: examples 3.1, 3.2, 3.4, 3.5,
  4.3, 4.7, 4.8, 4.9, 4.11 and 6.3.

A tolerance is the published value's last printed digit, or a little
more where the book rounds intermediate values (said where it applies).
-}
module Astro (astroTests) where

import Data.Text (Text)
import Data.Text qualified as T
import Metron.Driver (Session, feed, seededSession)
import Test.Tasty
import Test.Tasty.HUnit

{- | The solvers iterate a fixed number of Newton steps, linear in time
since the iteration fix; each test gets 10 s as a backstop, though the
slowest takes under a second.
-}
astroTests :: TestTree
astroTests =
  localOption (mkTimeout 10_000_000)
    $ testGroup
      "astro (design §7.7)"
      [ constantTests
      , relationTests
      , elementTests
      , anomalyTests
      , propagationTests
      , maneuverTests
      ]

-- Running sessions -------------------------------------------------------------------

seeded :: Session
seeded = either (error . T.unpack) id seededSession

{- | Lines fed in turn to a seeded session with @astro@, @astro.kepler@ and
@astro.maneuver@ used, and Curtis's Earth as @curtis@.
-}
session :: [Text] -> Either Text [Text]
session = go seeded [] . (preamble ++)
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls
  preamble =
    [ "use astro"
    , "use astro.kepler"
    , "use astro.maneuver"
    , -- Curtis's constants (4th ed., Table A.1 and §4.7).
      "let curtis = Body {mu = 398600 km^3/s^2, radius = 6378 km, flattening = 0, j2 = 0.00108263, rate = 0 rad/s}"
    ]

-- | Every check, after the setup lines, prints @true@.
holds :: [Text] -> [Text] -> Assertion
holds setup checks =
  case session (setup ++ checks) of
    Left err -> assertFailure (T.unpack err)
    Right outs ->
      let got = drop (length outs - length checks) outs
       in mapM_
            (\(c, o) -> assertEqual (T.unpack c) "true" o)
            (zip checks got)

-- | @|x − y| ≤ tol@, decided on the enclosure, so rigorously.
near :: Text -> Text -> Text -> Text
near tol x y = "abs ((" <> x <> ") - (" <> y <> ")) <= " <> tol

-- | A vector within @tol@ of another, by the square of its distance.
nearVec :: Text -> Text -> Text -> Text
nearVec tol x y =
  "let d = (" <> x <> ") - (" <> y <> ") in d · d <= (" <> tol <> ")^2"

-- | The lines fail with an error that contains the text.
fails :: [Text] -> Text -> Assertion
fails ls needle = case session ls of
  Left err ->
    (needle `T.isInfixOf` err)
      @? T.unpack ("expected " <> needle <> " in:\n" <> err)
  Right outs -> assertFailure ("expected an error, got " <> show outs)

-- Constant sets ----------------------------------------------------------------------

constantTests :: TestTree
constantTests =
  testGroup
    "constant sets"
    [ testCase "wgs84: TR8350.2 Table 3.1, and J2 from the EGM96 C20" $ do
        holds
          []
          [ "wgs84.earth.mu == 3986004.418e8 m^3/s^2"
          , "wgs84.earth.radius == 6378137 m"
          , "wgs84.earth.flattening == 1 / 298.257223563"
          , "wgs84.earth.rate == 7292115e-11 rad/s"
          , -- J2 = -√5 C̄20 = 1.0826266836e-3 (EGM96, tide-free); Vallado
            -- uses 0.0010826267.
            near "1e-13" "mid wgs84.earth.j2" "1.0826266836e-3"
          , near "1e-13" "sd wgs84.earth.j2" "sqrt 5 * 0.35610635e-10"
          ]
        -- The defining values are exact; only J2 is measured.
        session ["bound wgs84.earth.mu", "sd wgs84.earth.mu"]
          @?= Right ["0 m^3 s^-2", "0 m^3 s^-2"]
    , testCase "iers2010: TN36 Tables 1.1 and 1.2, with their uncertainties" $ do
        holds
          []
          [ "mid iers2010.earth.mu == 3.986004418e14 m^3/s^2"
          , "sd iers2010.earth.mu == 8e5 m^3/s^2"
          , "mid iers2010.earth.radius == 6378136.6 m"
          , "sd iers2010.earth.radius == 0.1 m"
          , "mid iers2010.earth.j2 == 1.0826359e-3"
          , "sd iers2010.earth.j2 == 1e-10"
          , near "1e-18" "mid (1 / iers2010.earth.flattening)" "298.25642"
          , "iers2010.earth.rate == 7.292115e-5 rad/s"
          , -- the Moon's GM is the mass ratio times the Earth's
            near "1e-20" "mid (iers2010.moon.mu / iers2010.earth.mu)" "0.0123000371"
          , near "1e-15" "sd (iers2010.moon.mu / iers2010.earth.mu)" "4e-10"
          , "iers2010.moon.radius == 0 m"
          , "mid iers2010.sun.mu == 1.32712442099e20 m^3/s^2"
          , "sd iers2010.sun.mu == 1e10 m^3/s^2"
          , "iers2010.sun.j2 == 2.0e-7"
          ]
    , testCase "iau2015: Resolution B3's nominal values, exact"
        $ holds
          []
          [ "iau2015.earth.mu == 3.986004e14 m^3/s^2"
          , "iau2015.earth.radius == 6.3781e6 m"
          , "iau2015.earth.flattening == 213 / 63781"
          , "iau2015.sun.mu == 1.3271244e20 m^3/s^2"
          , "iau2015.sun.radius == 6.957e8 m"
          , "iau2015.jupiter.mu == 1.2668653e17 m^3/s^2"
          , "iau2015.jupiter.radius == 7.1492e7 m"
          , "iau2015.jupiter.flattening == (7.1492 - 6.6854) / 7.1492"
          ]
    , testCase "de440: Park et al. (2021) Table 2 and the header's radii and J2"
        $ holds
          []
          [ "de440.sun.mu == 132712440041.279419 km^3/s^2"
          , "de440.mercury.mu == 22031.868551 km^3/s^2"
          , "de440.venus.mu == 324858.592 km^3/s^2"
          , "de440.earth.mu == 398600.435507 km^3/s^2"
          , "de440.moon.mu == 4902.800118 km^3/s^2"
          , "de440.mars.mu == 42828.375816 km^3/s^2"
          , "de440.jupiter.mu == 126712764.1 km^3/s^2"
          , "de440.saturn.mu == 37940584.8418 km^3/s^2"
          , "de440.uranus.mu == 5794556.4 km^3/s^2"
          , "de440.neptune.mu == 6836527.10058 km^3/s^2"
          , "de440.pluto.mu == 975.5 km^3/s^2"
          , "de440.earth.radius == 6378.1366 km"
          , "de440.earth.j2 == 1.08262539e-3"
          , "de440.moon.radius == 1738 km"
          , "de440.sun.radius == 696000 km"
          , -- Earth over Moon is the header's EMRAT, 81.3005682214972154, to
            -- the 1e-6 km³/s² to which Table 2 rounds the Moon's GM
            near "2e-8" "de440.earth.mu / de440.moon.mu" "81.3005682214972154"
          ]
    , testCase "a set is chosen with a use, and two sets offering earth are ambiguous" $ do
        session ["use astro.wgs84", "period earth (7000 km) to min"]
          @?= Right ["97.141943961433593065… min"]
        fails
          ["use astro.wgs84", "use astro.iau2015", "earth"]
          "`earth` is both"
    ]

-- Relations --------------------------------------------------------------------------

relationTests :: TestTree
relationTests =
  testGroup
    "relations"
    [ testCase "period, mean motion, energy, momentum, circular and escape speed"
        $ holds
          ["use astro.wgs84"]
          [ -- Curtis Ex 3.1: rp = 9600 km, ra = 21000 km, T = 18834 s.
            near "1 s" "period curtis (15300 km)" "18834 s"
          , -- Vallado Ex 6-1: v = 7.789390 km/s at 6569.4781 km.
            near "1e-6 km/s" "circular earth (6569.4781 km)" "7.789390 km/s"
          , -- and the transfer's 10.246429 km/s at perigee, to 42159.4856 km
            -- (the book's a = 24364.4183 km is a misprint of 24364.4819)
            near
              "1e-6 km/s"
              "visViva earth (6569.4781 km) ((6569.4781 km + 42159.4856 km) / 2)"
              "10.246429 km/s"
          , -- Vallado Ex 2-5: ξ = -5.516604 km²/s², a = 36127.343 km, and
            -- h = 66420.10 km²/s from p.
            near "1e-6 km^2/s^2" "energy earth (36127.343 km)" "-5.516604 km^2/s^2"
          , near "0.01 km^2/s" "momentum earth (11067.798 km)" "66420.10 km^2/s"
          , near "1e-9 m^2/s^2" "escape earth (7000 km)^2" "2 * circular earth (7000 km)^2"
          , -- n = 2π / T, and a hyperbola's mean motion uses |a|
            near
              "1e-12 rad"
              "meanMotion earth (7000 km) * period earth (7000 km)"
              "2 * pi * 1 rad"
          , "meanMotion earth (-7000 km) == meanMotion earth (7000 km)"
          ]
    ]

-- Elements and states ----------------------------------------------------------------

elementTests :: TestTree
elementTests =
  testGroup
    "elements and states"
    [ testCase "Vallado Ex 2-5: RV2COE"
        $ holds
          [ "use astro.wgs84"
          , "let el = fromState earth ([6524.834, 6862.875, 6448.296] km) ([4.901327, 5.533756, -1.976341] km/s)"
          ]
          [ -- the book prints p = 11067.790 km; exactly it is 11067.79834
            near "1e-5 km" "semilatus el" "11067.79834 km"
          , -- the book prints a = 36127.343 km from rounded intermediates;
            -- exactly it is 36127.3376 km
            near "0.01 km" "el.a" "36127.343 km"
          , near "1e-6" "el.e" "0.832853"
          , near "1e-3 deg" "el.i" "87.870 deg"
          , near "1e-3 deg" "el.raan" "227.898 deg"
          , near "1e-2 deg" "el.argp" "53.38 deg"
          , near "1e-3 deg" "el.nu" "92.335 deg"
          , -- the task's reference values, to their last digit
            near "1e-6 deg" "el.i" "87.869126 deg"
          , near "1e-6 deg" "el.raan" "227.898260 deg"
          , near "1e-6 deg" "el.argp" "53.384931 deg"
          , near "1e-6 deg" "el.nu" "92.335157 deg"
          ]
    , testCase "Vallado Ex 2-6: COE2RV, with the 2019 errata"
        $ holds
          [ "use astro.wgs84"
          , "let st = toState earth (Elements {a = 11067.790 km / (1 - 0.83285^2), e = 0.83285, i = 87.87 deg, raan = 227.89 deg, argp = 53.38 deg, nu = 92.335 deg})"
          ]
          [ nearVec "1e-3 km" "fst st" "[6525.368, 6861.532, 6449.119] km"
          , nearVec "1e-6 km/s" "snd st" "[4.902279, 5.533140, -1.975710] km/s"
          , -- the task's reference values
            nearVec "1e-6 km" "fst st" "[6525.368121, 6861.531835, 6449.118614] km"
          , nearVec "1e-6 km/s" "snd st" "[4.902279, 5.533140, -1.975710] km/s"
          ]
    , testCase "Curtis Ex 4.3: rv to elements, retrograde"
        $ holds
          [ "let el = fromState curtis ([-6045, -3490, 2500] km) ([-3.457, 6.618, 2.533] km/s)"
          ]
          [ near "1 km" "el.a" "8788 km"
          , near "1e-4" "el.e" "0.1712"
          , near "0.1 deg" "el.i" "153.2 deg"
          , near "0.1 deg" "el.raan" "255.3 deg"
          , near "0.01 deg" "el.argp" "20.07 deg"
          , near "0.01 deg" "el.nu" "28.45 deg"
          ]
    , testCase "Curtis Ex 4.7: elements to rv, hyperbolic"
        $ holds
          [ "let el = Elements {a = (80000 km^2/s)^2 / (398600 km^3/s^2) / (1 - 1.4^2), e = 1.4, i = 30 deg, raan = 40 deg, argp = 60 deg, nu = 30 deg}"
          , "let st = toState curtis el"
          ]
          [ nearVec "1 km" "fst st" "[-4040, 4815, 3629] km"
          , nearVec "0.01 km/s" "snd st" "[-10.39, -4.772, 1.744] km/s"
          ]
    , testCase "round trips: elements to a state and back, for each case"
        $ holds
          [ "use astro.wgs84"
          , "let back el = fromState earth (fst (toState earth el)) (snd (toState earth el))"
          , "let same x y = abs (x.a - y.a) < 1e-12 km && abs (x.e - y.e) < 1e-15 && abs (x.i - y.i) < 1e-15 rad && abs (x.raan - y.raan) < 1e-15 rad && abs (x.argp - y.argp) < 1e-15 rad && abs (x.nu - y.nu) < 1e-15 rad"
          , "let ell = Elements {a = 36127.343 km, e = 0.83285, i = 87.87 deg, raan = 227.89 deg, argp = 53.38 deg, nu = 92.335 deg}"
          , "let hyp = Elements {a = -16725 km, e = 1.4, i = 30 deg, raan = 40 deg, argp = 60 deg, nu = 330 deg}"
          , "let low = Elements {a = 7000 km, e = 0.001, i = 98 deg, raan = 300 deg, argp = 200 deg, nu = 10 deg}"
          , -- equatorial: sin 0 is exact, so the node vector is exactly zero
            "let flat = Elements {a = 7000 km, e = 0.1, i = 0 deg, raan = 0 deg, argp = 30 deg, nu = 40 deg}"
          ]
          [ "same (back ell) ell"
          , "same (back hyp) hyp"
          , "same (back low) low"
          , "same (back flat) flat"
          ]
    , testCase
        "a circular orbit's state from toState is too uncertain to call circular"
        $
        -- toState's state is an enclosure, so its eccentricity vector is
        -- zero only to within it: fromState cannot decide the case.
        fails
          [ "use astro.wgs84"
          , "let st = toState earth (Elements {a = 7000 km, e = 0, i = 30 deg, raan = 20 deg, argp = 0 deg, nu = 40 deg})"
          , "fromState earth (fst st) (snd st)"
          ]
          "cannot decide"
    , testCase "the circular and equatorial cases keep the record's shape" $ do
        -- Exact states: r along x, v exactly circular for μ = 398600 km³/s²
        -- at 7.5 km/s, r = 398600 / 56.25 km.
        let r0 = "[398600 / 56.25, 0, 0] km"
        session
          [ "fromState curtis (" <> r0 <> ") ([0, 7.5, 0] km/s)"
          , "fromState curtis (" <> r0 <> ") ([0, 6, 4.5] km/s)"
          , "fromState curtis ([7000, 0, 0] km) ([0, 8, 0] km/s)"
          , "fromState curtis ([0, 7000, 0] km) ([8, 0, 0] km/s)"
          ]
          @?= Right
            [ -- circular equatorial: nu is the true longitude
              "Elements {a = 7086.2222222222222222… km, e = 0, i = 0 rad, raan = 0 rad, argp = 0 rad, nu = 0 rad}"
            , -- circular inclined: argp = 0, nu the argument of latitude
              "Elements {a = 7086.2222222222222222… km, e = 0, i = 0.64350110879328438680… rad, raan = 0 rad, argp = 0 rad, nu = 0 rad}"
            , -- elliptic equatorial: raan = 0, argp the longitude of periapsis
              "Elements {a = 7990.2634593356242840… km, e = 0.12393376818866031108…, i = 0 rad, raan = 0 rad, argp = 0 rad, nu = 0 rad}"
            , -- retrograde equatorial: i = 180°, periapsis on +y
              "Elements {a = 7990.2634593356242840… km, e = 0.12393376818866031108…, i = 3.1415926535897932384… rad, raan = 0 rad, argp = 4.7123889803846898576… rad, nu = 0 rad}"
            ]
        -- and back
        holds
          [ "let st = toState curtis (fromState curtis ([0, 7000, 0] km) ([8, 0, 0] km/s))"
          , "let sc = toState curtis (fromState curtis (" <> r0 <> ") ([0, 6, 4.5] km/s))"
          ]
          [ nearVec "1e-15 km" "fst st" "[0, 7000, 0] km"
          , nearVec "1e-15 km/s" "snd st" "[8, 0, 0] km/s"
          , nearVec "1e-15 km" "fst sc" r0
          , nearVec "1e-15 km/s" "snd sc" "[0, 6, 4.5] km/s"
          ]
    , testCase "a case too uncertain to decide is an error"
        $
        -- Circular to within its 1 mm/s: is it circular?
        fails
          ["fromState curtis ([398600 / 56.25, 0, 0] km) ([0, 7.5 ± 1e-6, 0] km/s)"]
          "cannot decide"
    , testCase "a measured state carries its bounds into the elements"
        $ holds
          [ "use astro.wgs84"
          , "let el = fromState earth (([6524.834, 6862.875, 6448.296] ± 0.1) * 1 km) (([4.901327, 5.533756, -1.976341] ± 0.0001) * 1 km/s)"
          ]
          [ near "0.01 km" "mid el.a" "36127.343 km"
          , "bound el.a < 20 km"
          , "bound el.nu < 0.1 deg"
          ]
    ]

-- Anomalies and the solvers ----------------------------------------------------------

anomalyTests :: TestTree
anomalyTests =
  testGroup
    "anomalies and Kepler solvers"
    [ testCase "Vallado Ex 2-1: elliptic Kepler, E = 220.512074767522°"
        $ holds
          ["let ea = meanToEccentric 0.4 (235.4 deg)"]
          [ near "1e-12 deg" "ea" "220.512074767522 deg"
          , -- the declared truncation bound is far below that
            "bound ea < 1e-20 rad"
          , near "1e-20 rad" "eccentricToMean 0.4 ea" "235.4 deg"
          ]
    , testCase "Vallado Ex 2-3: hyperbolic Kepler, H = 1.601376144 rad"
        $ holds
          ["let hh = meanToHyperbolic 2.4 (235.4 deg)"]
          [ near "1e-9 rad" "hh" "1.601376144 rad"
          , "bound hh < 1e-20 rad"
          , near "1e-20 rad" "hyperbolicToMean 2.4 hh" "235.4 deg"
          ]
    , testCase "Vallado Ex 2-2: Barker's equation, B = 0.817751"
        $ holds
          ["use astro.wgs84"]
          [near "1e-6" "barker earth (25512 km) (53.7874 min)" "0.817751"]
    , testCase "Curtis Ex 3.4: parabolic, θ = 144.75° from Mp = 6.7737"
        $
        -- Curtis's Mp is half of Vallado's B + B³/3.
        holds
          []
          [ near "0.01 deg" "parabolicToTrue (meanToParabolic (2 * 6.7737))" "144.75 deg"
          , near "1e-20" "parabolicToMean (meanToParabolic 3)" "3"
          , near "1e-20 rad" "parabolicToTrue (trueToParabolic (1 rad))" "1 rad"
          ]
    , testCase "Curtis Ex 3.1 and 3.2: true, eccentric and mean anomalies"
        $ holds
          ["let e = 0.37255"]
          [ near "1e-4 rad" "trueToEccentric e (120 deg)" "1.7281 rad"
          , near "1e-4 rad" "trueToMean e (120 deg)" "1.3601 rad"
          , -- Ex 3.2: Me = 3.6029 rad gives E = 3.4794 rad, θ = 193.2°
            near "1e-4 rad" "meanToEccentric e (3.6029 rad)" "3.4794 rad"
          , near "0.05 deg" "meanToTrue e (3.6029 rad)" "193.2 deg"
          ]
    , testCase "Curtis Ex 3.5: hyperbolic anomalies at θ = 100°"
        $ holds
          ["let e = 2.7696"]
          [ near "1e-3 rad" "trueToHyperbolic e (100 deg)" "2.2927 rad"
          , near "1e-2 rad" "trueToMean e (100 deg)" "11.279 rad"
          ]
    , testCase "round trips through the mean anomaly, each conic"
        $ holds
          []
          [ near "1e-20 rad" "meanToTrue 0.3 (trueToMean 0.3 (250 deg))" "250 deg"
          , near "1e-20 rad" "meanToTrue 0.99 (trueToMean 0.99 (170 deg))" "170 deg"
          , near "1e-20 rad" "meanToTrue 1.5 (trueToMean 1.5 (-100 deg))" "-100 deg"
          , near "1e-20 rad" "eccentricToTrue 0.6 (trueToEccentric 0.6 (300 deg))" "300 deg"
          , near "1e-20 rad" "hyperbolicToTrue 3 (trueToHyperbolic 3 (80 deg))" "80 deg"
          ]
    , testCase
        "a solver's result is rigorous, and carries its inputs' σ to first order"
        $ holds
          [ "let ea = meanToEccentric 0.4 ((235.4 ±σ 0.01) * 1 deg)"
          , "let e0 = meanToEccentric 0.4 (235.4 deg)"
          , -- near e = 1 and M = 0, Newton's hardest case
            "let hard = meanToEccentric 0.999 (0.01 rad)"
          ]
          [ -- dE/dM = 1 / (1 - e cos E)
            near "1e-12 deg" "sd ea" "0.01 deg / (1 - 0.4 * cos e0)"
          , near "1e-12 deg" "mid ea" "e0"
          , "bound hard < 1e-18 rad"
          , near "1e-18 rad" "hard - 0.999 * sin hard * 1 rad" "0.01 rad"
          ]
    ]

-- Propagation ------------------------------------------------------------------------

propagationTests :: TestTree
propagationTests =
  testGroup
    "propagation and J2"
    [ testCase "Vallado Ex 2-4: Kepler's problem over 40 min"
        $ holds
          [ "use astro.wgs84"
          , "let el = fromState earth ([1131.340, -2282.343, 6672.423] km) ([-5.64305, 4.30333, 2.42879] km/s)"
          , "let st = toState earth (propagate earth el (40 min))"
          ]
          [ nearVec "1e-4 km" "fst st" "[-4219.7527, 4363.0292, -3958.7666] km"
          , nearVec "1e-6 km/s" "snd st" "[3.689866, -1.916735, -6.112511] km/s"
          ]
    , testCase "Curtis Ex 3.5: a hyperbola 3 h on, θ = 107.78°, r = 163180 km"
        $ holds
          [ "let e = (6678 km) * (15 km/s)^2 / (398600 km^3/s^2) - 1"
          , "let el = Elements {a = 6678 km / (1 - e), e = e, i = 0 deg, raan = 0 deg, argp = 0 deg, nu = 100 deg}"
          , "let later = propagate curtis el (3 hr)"
          ]
          [ near "1e-4" "e" "2.7696"
          , near "0.01 deg" "later.nu" "107.78 deg"
          , near "1 km" "norm (fst (toState curtis later))" "163180 km"
          ]
    , testCase "Curtis Ex 4.8: J2 node regression and perigee advance"
        $ holds
          [ "let c8 = Body {mu = 398600 km^3/s^2, radius = 6378 km, flattening = 0, j2 = 0.0010826, rate = 0 rad/s}"
          , "let el = Elements {a = 6718 km, e = 0.008931, i = 51.43 deg, raan = 0 deg, argp = 0 deg, nu = 0 deg}"
          ]
          [ near "1e-3 deg/day" "nodeRate c8 el" "-5.181 deg/day"
          , near "1e-3 deg/day" "perigeeRate c8 el" "3.920 deg/day"
          ]
    , testCase "Curtis Ex 4.9 and Vallado Ex 11-2: sun-synchronous inclinations"
        $ holds
          [ "let v11 = Body {mu = 398600.4418 km^3/s^2, radius = 6378.137 km, flattening = 0, j2 = 0.00108263, rate = 0 rad/s}"
          ]
          [ -- Curtis: z = 758.63 km, i = 98.43° (his rate is 2π per 365.26 d)
            near "0.005 deg" "sunSynchronous curtis (6378 km + 758.63 km) 0" "98.43 deg"
          , -- Vallado: 800 km, a = 7178.1363 km, i = 98.6°
            near "0.05 deg" "sunSynchronous v11 (7178.1363 km) 0" "98.6 deg"
          , -- Vallado Ex 11-2's node rate
            near "1e-16 rad/s" "sunSyncRate" "1.991063853e-7 rad/s"
          ]
    , testCase "Curtis Ex 4.11: secular J2 propagation over 4 days"
        $ holds
          [ "let el = fromState curtis ([-3670, -3870, 4400] km) ([4.7, -7.4, 1] km/s)"
          , "let st = toState curtis (propagateJ2 curtis el (4 day))"
          ]
          [ nearVec "1 km" "fst st" "[9672, 4320, -8691] km"
          , nearVec "1e-3 km/s" "snd st" "[-3.040, 3.330, 0.6299] km/s"
          ]
    ]

-- Manoeuvres -------------------------------------------------------------------------

maneuverTests :: TestTree
maneuverTests =
  testGroup
    "manoeuvres"
    [ testCase "Vallado Ex 6-1: Hohmann, 191.34411 km to 35781.34857 km"
        $ holds
          [ "use astro.wgs84"
          , "let re = 6378.137 km"
          , "let t = hohmann earth (re + 191.34411 km) (re + 35781.34857 km)"
          ]
          [ near "1e-6 km/s" "total t" "3.935224 km/s"
          , near "1e-6 hr" "t.tof" "5.256713 hr"
          , -- the burns, from the printed speeds: 10.246429 - 7.789390 and
            -- 3.074831 - 1.596644 km/s, each rounded to 1e-6
            near "2e-6 km/s" "t.dv1" "2.457039 km/s"
          , near "2e-6 km/s" "t.dv2" "1.478187 km/s"
          , "t.dv3 == 0 m/s"
          ]
    , testCase "Vallado Ex 6-2: bi-elliptic through 80 ER to 60 ER"
        $ holds
          [ "use astro.wgs84"
          , "let re = 6378.137 km"
          , "let t = biElliptic earth (re + 191.34411 km) (80 * re) (60 * re)"
          ]
          [ near "1e-6 km/s" "total t" "3.904057 km/s"
          , -- worked in canonical units with a rounded TU: 0.36 s
            near "1e-4 hr" "t.tof" "593.919803 hr"
          ]
    , testCase "Curtis Ex 6.3: bi-elliptic against Hohmann"
        $ holds
          [ "let b = biElliptic curtis (7000 km) (210000 km) (105000 km)"
          , "let h = hohmann curtis (7000 km) (105000 km)"
          ]
          [ near "1e-4 km/s" "total b" "4.0285 km/s"
          , near "10 s" "b.tof" "488870 s"
          , near "1e-4 km/s" "total h" "4.0463 km/s"
          , near "1 s" "h.tof" "65942 s"
          ]
    , testCase "Vallado Ex 6-4: inclination only, circular and elliptic"
        $ holds
          []
          [ -- 0.1945770 ER/TU, printed as 1.5382021 km/s from a rounded v
            near "1e-6 km/s" "planeChange (5.892311 km/s) (0 deg) (15 deg)" "1.5382021 km/s"
          , near
              "1e-5 km/s"
              "planeChange (5.993824 km/s) (-6.7900 deg) (15 deg)"
              "1.553727 km/s"
          , near
              "1e-5 km/s"
              "planeChange (3.568017 km/s) (11.4558 deg) (15 deg)"
              "0.912883 km/s"
          ]
    , testCase "Vallado Ex 6-5 and 6-6: node, and node with inclination"
        $ holds
          []
          [ near "1e-5 deg" "rotationAngle (55 deg) (55 deg) (45 deg)" "36.53766 deg"
          , near
              "1e-6 km/s"
              "planeChange (5.892311 km/s) (0 deg) (rotationAngle (55 deg) (55 deg) (45 deg))"
              "3.694195 km/s"
          , near "1e-5 deg" "rotationAngle (55 deg) (40 deg) (45 deg)" "35.73709 deg"
          , near
              "1e-6 km/s"
              "planeChange (5.892311 km/s) (0 deg) (rotationAngle (55 deg) (40 deg) (45 deg))"
              "3.615925 km/s"
          ]
    , testCase "Vallado Ex 6-7: combined plane change with a Hohmann transfer"
        $
        -- Δi₁ is printed to six decimals, so the second burn is 1e-6 off.
        holds
          [ "use astro.wgs84"
          , "let r1 = 6569.137 km"
          , "let r2 = 42158.137 km"
          , "let ta = (r1 + r2) / 2"
          ]
          [ near
              "1e-6 km/s"
              "combinedChange (circular earth r1) (visViva earth r1 ta) (1.594920 deg)"
              "2.469669 km/s"
          , near
              "2e-6 km/s"
              "combinedChange (visViva earth r2 ta) (circular earth r2) (26.905080 deg)"
              "1.802216 km/s"
          ]
    , testCase "Vallado Ex 6-8: phasing within one orbit, 1 and 2 revolutions"
        $ holds
          [ "use astro.wgs84"
          , "let a = 2 * 6378.137 km"
          , "let p1 = phasing earth a (-20 deg) 1"
          , "let p2 = phasing earth a (-20 deg) 2"
          ]
          [ near "1e-4 min" "p1.tof" "225.6950 min"
          , near "1e-6 km/s" "p1.dv1" "-0.109634 km/s"
          , near "1e-6 km/s" "total p1" "0.219269 km/s"
          , "p1.dv2 == -p1.dv1"
          , near "1e-4 min" "p2.tof" "464.6661 min"
          , near "1e-6 km/s" "total p2" "0.106481 km/s"
          ]
    ]
