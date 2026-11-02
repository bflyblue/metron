-- | Rotations and charts, turned and moving.
module Lang.Charts (
  rotationTests,
  turnedChartTests,
  movingChartTests,
) where

import Data.Text (Text)
import Data.Text qualified as T (
  isPrefixOf,
  strip,
  unpack,
  unwords,
 )
import Lang.Common (
  eciChart,
  encloses,
  evalP,
  expectError,
  expecting,
  linesIn,
  lvlhCharts,
  persistLines,
  reload,
  runLinesP,
  typeOfTextP,
  withTempStore,
 )
import Metron.Codebase (Codebase (charts, names))
import Metron.Driver (Session (codebase))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

{- | Design §3.8: charts turned from their parent. Rotations are enclosures,
so a conversion is checked with 'encloses' on the amount from a fixed
point, divided by its unit, and never with @==@.
-}
turnedChartTests :: TestTree
turnedChartTests =
  testGroup
    "turnedCharts"
    [ testCase "one level: lvlh's x axis is eci's y, and back" $ do
        runLinesP
          ( lvlhCharts
              ++ [ encloses "1e-20" (fromEci "[1, 0, 0] lvlh") "[7000000, 1, 0]"
                 , -- reading back, by the generator negated
                   encloses
                     "1e-20"
                     "transformBy (expm (-(rotz (90 deg)))) (([7000000, 1, 0] eci .- ([0, 0, 0] lvlh to eci)) / 1 m)"
                     "[1, 0, 0]"
                 , "[1, 0, 0] lvlh to eci"
                 , "[7000000, 1, 0] eci to lvlh"
                 , "[0, 0, 0] lvlh"
                 ]
          )
          @?= Right
            [ "true"
            , "true"
            , "[7000000.0000000000000…, 1.0000000000000000000…, 0] eci"
            , "[1.0000000000000000000…, 3.0e-24 ± 3.8e-24, 0] lvlh"
            , "[0, 0, 0] lvlh"
            ]
    , testCase
        "two levels: the rotations compose in order, the origin turns with the parent"
        $ do
          -- arm is turned from lvlh by rotx (90 deg), its origin [0, 2, 5] m
          -- along lvlh's axes. By hand: R = Rz(90) Rx(90) = [0, 0, 1; 1, 0, 0;
          -- 0, 1, 0], the origin [7000000, 0, 0] + Rz(90) [0, 2, 5] =
          -- [6999998, 0, 5], so [1, 2, 3] arm is [6999998, 0, 5] + [3, 1, 2].
          -- The product reversed would give [-2, -3, 1] for R [1, 2, 3], and
          -- the origin not turned [7000000, 2, 5].
          let arm = lvlhCharts ++ ["chart arm on lvlh at [0, 2, 5] m by rotx (90 deg)"]
          runLinesP
            ( arm
                ++ [ encloses "1e-20" (fromEci "[1, 2, 3] arm") "[7000001, 1, 7]"
                   , encloses "1e-20" (fromEci "[0, 0, 0] arm") "[6999998, 0, 5]"
                   , encloses "1e-20" "rotationOf arm" "[0, 0, 1; 1, 0, 0; 0, 1, 0]"
                   , encloses
                       "1e-20"
                       "transformBy (expm (-(rotx (90 deg))) @ expm (-(rotz (90 deg)))) (([7000001, 1, 7] eci .- ([0, 0, 0] arm to eci)) / 1 m)"
                       "[1, 2, 3]"
                   , "[7000001, 1, 7] eci to arm"
                   ]
            )
            @?= Right
              [ "true"
              , "true"
              , "true"
              , "true"
              , "[1.0000000000000000000…, 1.9999999999999999999…, 3.0000000000000000000…] arm"
              ]
    , testCase
        "an origin is an amount along the parent's axes, not steps of the parent"
        $ do
          runLinesP
            [ eciChart
            , "chart kmc on eci step km"
            , "chart sub on kmc at [1, 0, 0] km step m"
            , "[0, 0, 0] sub to eci"
            , "chart kmt on eci step km by rotz (90 deg)"
            , "chart subt on kmt at [1, 0, 0] km step m"
            , encloses "1e-20" (fromEci "[0, 0, 0] subt") "[0, 1000, 0]"
            , -- a chart under a turned one, not turned itself, has its parent's axes
              encloses "1e-20" (fromEci "[1, 0, 0] subt") "[0, 1001, 0]"
            ]
            @?= Right ["[1000, 0, 0] eci", "true", "true"]
    , testCase "a sequence with then is the Euler product, applied in order" $ do
        let pf =
              [ eciChart
              , "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
              ]
        runLinesP
          ( pf
              ++ [ -- rows along eci and columns along pf, against a rotation
                   -- along one axis set: Rᵀ E is the identity
                   encloses
                     "1e-20"
                     "transpose (rotationOf pf) @ euler313 (30 deg) (45 deg) (60 deg)"
                     "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
                 , encloses
                     "1e-20"
                     (fromEci "[1, 2, 3] pf")
                     "euler313 (30 deg) (45 deg) (60 deg) @ [1, 2, 3]"
                 ]
          )
          @?= Right ["true", "true"]
    , testCase "displacements within a frame are along its axes, exactly" $ do
        runLinesP
          ( lvlhCharts
              ++ [ -- chart coordinates (design §3.10, F6): no rotation applies
                   "[1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , ":type [1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , -- re-expressed along eci's axes, the rotated difference
                   encloses
                     "1e-20"
                     "(([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci) / 1 m"
                     "expm (rotz (90 deg)) @ [1, -3, 3]"
                 , encloses
                     "1e-20"
                     "(([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci) / 1 m"
                     "[3, 1, 3]"
                 , -- q .+ (p .- q) is p, in one frame
                   "([4, 5, 6] lvlh .+ ([1, 2, 3] lvlh .- [4, 5, 6] lvlh)) == [1, 2, 3] lvlh"
                 , "let p = [1, 2, 3] eci"
                 , "let q = [7, 8, 9] eci"
                 , -- the difference re-expressed equals the difference of the
                   -- points re-expressed (design §3.10, F7)
                   encloses
                     "1e-20"
                     "(((p to lvlh) .- (q to lvlh)) - ((p .- q) to lvlh)) / 1 m"
                     "[0, 0, 0]"
                 , encloses
                     "1e-20"
                     "((p .- q on lvlh) - ((p .- q) to lvlh)) / 1 m"
                     "[0, 0, 0]"
                 , -- an amount along a chart's axes reaches the base's with from
                   encloses
                     "1e-20"
                     "(([1, 0, 0] m from lvlh to eci) - (([1, 0, 0] lvlh to eci) .- ([0, 0, 0] lvlh to eci))) / 1 m"
                     "[0, 0, 0]"
                 ]
          )
          @?= Right
            [ "[1, -3, 3] m"
            , "Vec lvlh m"
            , "true"
            , "true"
            , "true"
            , "true"
            , "true"
            , "true"
            ]
        -- Two frames' amounts do not mix unconverted.
        expectError
          ( runLinesP
              ( lvlhCharts
                  ++ ["([1, 2, 3] lvlh .- [0, 0, 0] lvlh) + ([1, 2, 3] eci .- [0, 0, 0] eci)"]
              )
          )
          "the axes of lvlh against the axes of GCRS"
    , testCase "a covariance and a Cov2 block through rotateCov are R P Rᵀ" $ do
        let pm = "[[4, 1, 0], [1, 9, 0], [0, 0, 1]]"
        typeOfTextP "rotateCov"
          @?= Right "forall n m d d1. Mat n m d -> Mat m m d1 -> Mat n n (d^2*d1)"
        typeOfTextP "rotateVec"
          @?= Right
            "forall n m d s d1. Mat n m d -> Tensor (m : s) d1 -> Tensor (n : s) (d*d1)"
        runLinesP
          ( lvlhCharts
              ++ [ encloses
                     "1e-20"
                     ("rotateCov (rotationOf lvlh) " <> pm)
                     ("rotationOf lvlh @ " <> pm <> " @ transpose (rotationOf lvlh)")
                 , encloses
                     "1e-20"
                     ("rotateCov (rotationOf lvlh) " <> pm)
                     "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , -- an unturned chart's is exactly the identity
                   "rotateCov (rotationOf eci) " <> pm <> " == " <> pm
                 , "blk :: Cov2 lvlh m (m/s)\nlet blk = Cov2 {rr = "
                     <> pm
                     <> " * 1 m^2, rv = "
                     <> pm
                     <> " * 1 m^2/s, vv = 2 * "
                     <> pm
                     <> " * (1 m/s)^2}"
                 , "let turned = inChartCov2 lvlh blk"
                 , encloses "1e-20" "turned.rr / 1 m^2" "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , encloses "1e-20" "turned.rv / (1 m^2/s)" "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , encloses
                     "1e-20"
                     "turned.vv / (1 m/s)^2"
                     "2 * [[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 ]
          )
          @?= Right ["true", "true", "true", "true", "true", "true"]
    , testCase "an uncertain angle: the coordinates carry it, correlated" $ do
        runLinesP
          [ eciChart
          , "chart tilt on eci by rotz (30 deg ± 0.001 rad)"
          , "let v = (([1000, 0, 0] tilt to eci) .- [0, 0, 0] eci) / 1 m"
          , -- x = 1000 cos θ, y = 1000 sin θ: bounds near 0.5 and 0.87
            "bound v.0 > 0.4 && bound v.0 < 0.6"
          , "bound v.1 > 0.8 && bound v.1 < 0.95"
          , -- the norm is 1000 whatever the angle: the first-order terms cancel
            "bound (norm v) < bound v.0 / 100"
          , "abs (mid (norm v) - 1000) < 1e-3"
          , -- on its own frame the point is exact
            "[1000, 0, 0] tilt .- [0, 0, 0] tilt"
          ]
          @?= Right ["true", "true", "true", "true", "[1000, 0, 0] m"]
    , testCase "a chart used in 100 conversions computes its rotation once" $ do
        -- Each mention of lvlh shares one value, and so one rotation.
        runLinesP
          ( lvlhCharts
              ++ [ encloses
                     "1e-15"
                     "foldl (\\acc k -> acc + (([k, 0, 0] lvlh to eci) .- ([0, 0, 0] lvlh to eci)).1 / 1 m) 0 (range 1 100)"
                     "5050"
                 ]
          )
          @?= Right ["true"]
    , testCase ":view and :edit of a sequence read back to the same hash" $ do
        let pf = "chart pf on eci at [0, 2, 0] km by rotz (30 deg) then rotx (45 deg)"
        runLinesP [eciChart, pf, ":view pf"] @?= Right [pf]
        let hashAfter def = runLinesP [eciChart, def, ":hash pf"]
        expecting (runLinesP [eciChart, pf, ":edit pf"]) $ \outs ->
          hashAfter (T.strip (last outs)) @?= hashAfter pf
    , testCase "design §12: a perifocal chart" $ do
        runLinesP perifocalSession
          @?= Right
            [ "chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
            , "[887785.38831025442775…, 5462310.6012293745031…, 4286607.0498705616718…] eci"
            , "[6999.9999999999999999…, -1.3e-20 ± 8.9e-20, 6e-21 ± 2.3e-20] pf"
            , "[-6.9508252147247766082…, -0.95119863033241545830…, 2.6516504294495532165…] km s^-1"
            , "[4.5767451288348659649…, -1.3794313182928119555…, 1.0170048711651340350…; -1.3794313182928119555…, 4.0482548711651340350…, -3.5986214154904359879…; 1.0170048711651340350…, -3.5986214154904359879…, 5.3749999999999999999…] km^2"
            , "7000 km"
            ]
    , testCase "a sequence-turned chart survives a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ eciChart
            , "chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"
            , "chart pf on lvlh by rotz (30 deg) then rotx (45 deg)"
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.names @?= s.codebase.names
        loaded.codebase.charts @?= s.codebase.charts
        linesIn loaded [":view pf", ":hash pf"]
          @?= linesIn s [":view pf", ":hash pf"]
        linesIn loaded ["[1, 2, 3] pf to eci"] @?= linesIn s ["[1, 2, 3] pf to eci"]
    ]
 where
  fromEci p = "(((" <> p <> ") to eci) .- [0, 0, 0] eci) / 1 m"

{- | The session of design §12, "A perifocal chart": a chart turned by the
3-1-3 sequence of an orbit's elements, a point on it, and a velocity and a
covariance given along its axes.
-}
perifocalSession :: [Text]
perifocalSession =
  [ "space GCRS = Vec 3 m"
  , "chart eci on GCRS"
  , "chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
  , ":view pf"
  , "let rp = [7000, 0, 0] pf"
  , "rp to eci"
  , "(rp to eci) to pf"
  , "let vp = [0, 7.5, 0] km/s from pf to eci"
  , "vp to km/s"
  , "rotateCov (rotationOf pf) ([[1, 0, 0], [0, 4, 0], [0, 0, 9]] km^2) to km^2"
  , "rp.0"
  ]

{- | Design §3.8: moving charts. A chart declared with parameters is a
function to a chart, applied at a time; a spinning chart carries its
angular velocity, and the kinematics compose through the tree. The physics
is checked against hand formulas (sines and cosines, not @expm@), against
a finite difference of positions, and by the transport law that a body
fixed on a chart is at rest relative to it.
-}
movingChartTests :: TestTree
movingChartTests =
  testGroup
    "movingCharts"
    [ testCase
        "a moving chart declares, prints with its parameter and spin, and applies"
        $ do
          runLinesP
            ( spinning
                ++ [ ":view spinner"
                   , ":type spinner"
                   , "[7000000, 0, 0] eci to spinner t1"
                   , "[7000000, 0, 0] eci to (spinner t1)"
                   , "spinner t1"
                   ]
            )
            @?= Right
              [ "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
              , "Point unix -> Chart spinner"
              , "[6981397.0116296611947…, -509995.84901098588542…, 0] (spinner (1000 unix))"
              , "[6981397.0116296611947…, -509995.84901098588542…, 0] (spinner (1000 unix))"
              , "chart (spinner (1000 unix))"
              ]
          -- what an instant prints reads back: one frame, one point
          runLinesP
            (spinning ++ ["[1, 2, 3] (spinner (1000 unix)) == [1, 2, 3] (spinner t1)"])
            @?= Right ["true"]
          -- a spin with no `by`: the generators are an empty list, and no `by` prints
          runLinesP
            ( spinning
                ++ [ "chart carousel t on (spinner t) at [10, 0, 0] m spinning [0, 0, 2] * w"
                   , ":view carousel"
                   ]
            )
            @?= Right
              ["chart carousel t on (spinner t) at [10, 0, 0] m spinning [0, 0, 2] * w"]
    , testCase ":edit reads a moving chart back to the same hash" $ do
        let hashAfter def = runLinesP (take 4 spinning ++ [def, ":hash spinner"])
        expecting (runLinesP (spinning ++ [":edit spinner"])) $ \outs ->
          hashAfter (T.strip (last outs)) @?= hashAfter (spinning !! 4)
    , testCase
        "a moving chart without its arguments is refused, as a point's chart, a target or a parent"
        $ do
          expectError
            (runLinesP (spinning ++ ["[1, 2, 3] eci to spinner"]))
            "`spinner` takes arguments: apply it, as in p to (spinner t0)"
          expectError
            (runLinesP (spinning ++ ["[1, 2, 3] spinner"]))
            "`spinner` takes arguments: a point is written on an applied chart, as in [1, 2, 3] (spinner t0)"
          expectError
            (runLinesP (spinning ++ ["chart arm t on spinner at [1, 0, 0] m"]))
            "`spinner` takes arguments: apply it, as in chart arm t on (spinner t) at [1, 0, 0] m"
          -- A point on it converts from a configuration named with `from`
          -- (design §3.10, F7), never the one it was written on.
          expectError
            (runLinesP (spinning ++ ["let p = [1, 2, 3] (spinner t1)", "p to eci"]))
            "spinner takes arguments: write p from (spinner …) to eci"
          -- the spin is an angular velocity: rad s^-1, not s^-1
          expectError
            ( runLinesP
                (spinning ++ ["chart bad on eci spinning [0, 0, 1] / 1 s"])
            )
            "rad"
    , testCase "a body fixed on a spinning chart: at rest on it, ω × r in the parent" $ do
        runLinesP
          ( spinning
              ++ [ ":use astro"
                 , "let c = spinner t1"
                 , "let p = [7000000, 0, 0] (spinner t1)"
                 , "let pe = (p from c to eci) .- [0, 0, 0] eci"
                 , "let wv = withAxes eci ([0, 0, 1] * (w / 1 rad))"
                 , -- the inertial velocity of a point turning with the chart
                   "let body = State {epoch = t1, pos = pe, vel = wv × pe}"
                 , encloses "1e-15" "velocityIn c body / (1 m/s)" "[0, 0, 0]"
                 , -- written back: ω × r along the parent's axes, by hand,
                   -- r = 7000 km at θ = w (t1 − t0)
                   encloses
                     "1e-15"
                     "(stateFrom c t1 ([7000000, 0, 0] m) ([0, 0, 0] m/s)).vel / (1 m/s)"
                     "7000000 * (w * 1 s / rad) * [-sin (w * 1000 s), cos (w * 1000 s), 0]"
                 , -- a body at rest in the parent turns backwards on the chart
                   encloses
                     "1e-15"
                     "velocityIn c (State {epoch = t1, pos = pe, vel = [0, 0, 0] m/s}) / (1 m/s)"
                     "[0, -7000000 * (w * 1 s / rad), 0]"
                 ]
          )
          @?= Right ["stored use astro", "true", "true", "true"]
    , testCase
        "stateFrom then velocityIn and the position back on the chart are the round trip"
        $ do
          runLinesP
            ( spinning
                ++ [ ":use astro"
                   , "chart tilted t on (spinner t) at [100, -20, 30] km by rotx (30 deg) spinning [0.1, 0, 0] * w"
                   , "let c = tilted t1"
                   , "let pc = withAxes c ([7000, 100, -50] km)"
                   , "let vc = withAxes c ([1, 7.5, 0.2] km/s)"
                   , "let st = stateFrom c t1 pc vc"
                   , encloses "1e-15" "velocityIn c st / (1 m/s)" "vc / 1 (m/s)"
                   , encloses "1e-15" "((st.pos - originOf c) to c) / 1 m" "pc / 1 m"
                   , encloses
                       "1e-12"
                       "((([0, 0, 0] eci .+ st.pos) to tilted t1) .- [0, 0, 0] (tilted t1)) / 1 m"
                       "pc / 1 m"
                   ]
            )
            @?= Right ["stored use astro", "true", "true", "true"]
    , testCase
        "a declared spin agrees with the rotation it goes with: a finite difference"
        $ do
          -- A body fixed on the chart at t1 and t1 + 1 ms, compared with the
          -- velocity stateFrom gives it: the forward difference is off by
          -- about ω δt / 2 ≈ 3.6e-8 of the speed (the centripetal term). Its
          -- positions at two configurations are compared in the parent
          -- (design §3.10, F7), on one frame they would be one point.
          runLinesP
            ( spinning
                ++ [ ":use astro"
                   , "let pc = withAxes (spinner t1) [7000000, 2000, 300]"
                   , "let seen t = pointOn (spinner t) pc from (spinner t) to eci"
                   , "let fd = (seen (t1 .+ 1 ms) .- seen t1) / (1 ms)"
                   , "let v = (stateFrom (spinner t1) t1 (pc * 1 m) ([0, 0, 0] m/s)).vel"
                   , "let rel = norm (fd - v) / norm v"
                   , "mid rel < 1e-6 && mid rel > 1e-8"
                   , "rel"
                   , "pointOn (spinner (t1 .+ 1 ms)) pc .- pointOn (spinner t1) pc"
                   ]
            )
            @?= Right
              ["stored use astro", "true", "3.6460579499999992e-8 ± 3.5e-23", "[0, 0, 0] m"]
    , testCase
        "two levels: a station under a spinning Earth, a dish spinning on the station"
        $ do
          let station =
                spinning
                  ++ [ ":use astro"
                     , "chart station t on (spinner t) at [6378, 0, 0] km by roty (30 deg)"
                     , "let wv = withAxes eci ([0, 0, 1] * (w / 1 rad))"
                     , "let c = station t1"
                     ]
          runLinesP
            ( station
                ++ [ -- the station's own spin is none; it turns with the Earth
                     encloses "1e-25" "spinOf c * 1 s" "wv * 1 s"
                   , -- its origin moves with the Earth's frame: ω × (R_p a), by hand
                     encloses
                       "1e-12"
                       "originVelocityOf c / (1 m/s)"
                       "6378000 * (w * 1 s / rad) * [-sin (w * 1000 s), cos (w * 1000 s), 0]"
                   , -- a body fixed at the station is at rest relative to it
                     "let pe = ([1, 2, 3] (station t1) from c to eci) .- [0, 0, 0] eci"
                   , "let body = State {epoch = t1, pos = pe, vel = wv × pe}"
                   , encloses "1e-12" "velocityIn c body / (1 m/s)" "[0, 0, 0]"
                   ]
            )
            @?= Right ["stored use astro", "true", "true", "true"]
          -- A dish turning on the station, two spinning levels: the composed
          -- ω_abs = ω_p + R ω and the origin's transport agree with a
          -- central difference of positions. The dish's own turning adds
          -- 0.037 m/s to the Earth's 464 m/s; the difference is off by about
          -- (|ω| δt)² / 6 of each, under 1e-12 m/s, where a spin left out,
          -- turned the wrong way or not turned by R would be off by 0.01 m/s.
          -- (Checked by component: `norm` of so small an enclosure is slow.)
          runLinesP
            ( station
                ++ [ "chart dish t on (station t) at [0, 0, 10] m by rotz (0.01 rad/s * (t .- t0)) spinning [0, 0, 0.01] rad/s"
                   , "let pc = withAxes (dish t1) [3, 1, 2]"
                   , "let seen t = pointOn (dish t) pc from (dish t) to eci"
                   , "let fd = (seen (t1 .+ 1 ms) .- seen (t1 .+ -1 ms)) / (2 ms)"
                   , "let v = (stateFrom (dish t1) t1 (pc * 1 m) ([0, 0, 0] m/s)).vel"
                   , "vmap (\\x -> if abs (mid x) < 1e-11 then 0 else 1) ((fd - v) / (1 m/s)) == [0, 0, 0]"
                   , encloses
                       "1e-25"
                       "spinOf (dish t1) * 1 s"
                       "(wv + ([0, 0, 0.01] / 1 s from (dish t1) to eci)) * 1 s"
                   ]
            )
            @?= Right ["stored use astro", "true", "true"]
    , testCase "an uncertain spin rate gives a velocity whose bound grows with |r|" $ do
        runLinesP
          [ ":use astro"
          , "space GCRS = Vec 3 m"
          , "chart eci on GCRS"
          , "let wu = 7.2921159e-5 rad/s ± 1e-10 rad/s"
          , "let t0 = 0 unix"
          , "chart wobbly t on eci by rotz (wu * (t .- t0)) spinning [0, 0, 1] * wu"
          , "let v1 = (stateFrom (wobbly t0) t0 ([7000, 0, 0] km) ([0, 0, 0] m/s)).vel / (1 m/s)"
          , "let v2 = (stateFrom (wobbly t0) t0 ([14000, 0, 0] km) ([0, 0, 0] m/s)).vel / (1 m/s)"
          , -- 7000 km × 1e-10 s^-1 = 7e-4 m/s
            "bound v1.1 > 6.9e-4 && bound v1.1 < 7.1e-4"
          , "bound v2.1 / bound v1.1 > 1.99 && bound v2.1 / bound v1.1 < 2.01"
          ]
          @?= Right ["stored use astro", "true", "true"]
    , testCase "a moving chart survives a reload" $ withTempStore $ \dir -> do
        s <- persistLines dir (spinning ++ [":add"])
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.charts @?= s.codebase.charts
        let probe =
              [ ":view spinner"
              , ":hash spinner"
              , "[1, 2, 3] (spinner t1) from (spinner t1) to eci"
              , "[1, 2, 3] eci to spinner t1"
              ]
        linesIn loaded probe @?= linesIn s probe
        expectError
          (linesIn loaded ["[1, 2, 3] spinner"])
          "`spinner` takes arguments: a point is written on an applied chart"
        expectError
          (linesIn loaded ["[1, 2, 3] (spinner t1) to eci"])
          "spinner takes arguments: write [1, 2, 3] (spinner t1) from (spinner …) to eci"
    , testCase "design §12: a spinning Earth, for illustration" $ do
        -- The GMST model is linear, θ = 280.46061837° + 360.98564736629°/day ×
        -- (t − J2000.0) (Meeus, Astronomical Algorithms, without the T² and
        -- T³ terms). Checked against the IAU 1982 GMST (Aoki et al. 1982,
        -- A&A 105, 359) at 2026 Jan 1 0h UT1, JD 2461041.5: 24110.54841 s +
        -- 8640184.812866 s T + 0.093104 s T² − 6.2e-6 s T³ with T = 0.26
        -- Julian centuries is 100.6608585° modulo 360°; the linear model is
        -- 0.094″ less.
        runLinesP
          ( take 3 spinningEarthSession
              ++ [ "let g = gmst (9496.5 J2000) / 1 deg"
                 , "abs (g - 360 * floor (g / 360) - 100.6608585) < 1e-4"
                 ]
          )
          @?= Right ["true"]
        runLinesP spinningEarthSession
          @?= Right
            [ "chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg / day"
            , "[-734892.0553385001942 ± 3e-13, 3903932.6219852148939…, 4990000] eci"
            , "stored use astro"
            , "[-284.67928970827302009…, -53.589180086727794658 ± 2.2e-17, 0] m s^-1"
            , "[0, 0, 0] m s^-1"
            , "[0.00000000000000000 ± 4e-17, -289.67930235205722039…, 0] m s^-1"
            ]
    ]
 where
  spinning =
    [ eciChart
    , "let w = 7.2921159e-5 rad/s"
    , "let t0 = 0 unix"
    , "let t1 = 1000 unix"
    , "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
    ]

{- | The session of design §12, "A spinning Earth": a chart turned by a
linear GMST and spinning at its rate, a station fixed on it, and the
station's velocity, which is the Earth's rotation alone.
-}
spinningEarthSession :: [Text]
spinningEarthSession =
  [ eciChart
  , "let gmst t = 280.46061837 deg + 360.98564736629 deg / day * (t .- 0 J2000)"
  , "chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg/day"
  , ":view earth"
  , "chart greenwich t on (earth t) at [3972.5, 0, 4990] km"
  , "let t26 = 9496.5 J2000"
  , "[0, 0, 0] (greenwich t26) from (greenwich t26) to eci"
  , ":use astro"
  , "let st = stateFrom (greenwich t26) t26 ([0, 0, 0] m) ([0, 0, 0] m/s)"
  , "st.vel to m/s"
  , "velocityIn (greenwich st.epoch) st"
  , "velocityIn (greenwich t26) (State {epoch = t26, pos = st.pos, vel = [0, 0, 0] m/s})"
  ]

-- | Design §3.3, §3.8: @expm@, @transformBy@ and the bivector constructors.
rotationTests :: TestTree
rotationTests =
  testGroup
    "rotations"
    [ testCase "expm of a bivector is a right-handed rotation about each axis" $ do
        evalP "expm (rotz (90 deg)) @ [1, 0, 0]"
          @?= Right ["[3.0e-24 ± 3.8e-24, 1.0000000000000000000…, 0]"]
        evalP (encloses "1e-20" "expm (rotz (90 deg)) @ e1" "e2") @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotx (90 deg)) @ e2" "e3") @?= Right ["true"]
        evalP (encloses "1e-20" "expm (roty (90 deg)) @ e3" "e1") @?= Right ["true"]
        evalP
          (encloses "1e-20" "expm (rotz (30 deg)) @ e1" "[cos (30 deg), sin (30 deg), 0]")
          @?= Right ["true"]
    , testCase "expm of zero is the identity, exactly" $ do
        evalP "expm [[0, 0, 0], [0, 0, 0], [0, 0, 0]]"
          @?= Right ["[1, 0, 0; 0, 1, 0; 0, 0, 1]"]
        evalP "expm [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]"
          @?= Right ["[1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]"]
        evalP "expm (rotz (0 deg)) == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
          @?= Right ["true"]
        case evalP "expm [[5]]" of
          Right [v] -> T.isPrefixOf "[[148.41315910257660342" v @? T.unpack v
          other -> assertFailure (show other)
    , testCase "expm (-B) undoes expm B" $ do
        let b = "axisAngle [1, 2, 2] (40 deg)"
        evalP
          ( encloses
              "1e-20"
              ("expm (-(" <> b <> ")) @ (expm (" <> b <> ") @ [3, -1, 2])")
              "[3, -1, 2]"
          )
          @?= Right ["true"]
        -- not antisymmetric: the series, with its remainder
        let m = "[[0.1, 0.2], [0.3, -0.1]]"
        evalP (encloses "1e-20" ("expm (-" <> m <> ") @ expm " <> m) "[[1, 0], [0, 1]]")
          @?= Right ["true"]
    , testCase "a rotation is orthogonal: Rᵀ R encloses I" $ do
        let i3 = "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
        evalP
          ( encloses
              "1e-20"
              "let r = expm (axisAngle [1, 2, 2] (40 deg)) in transpose r @ r"
              i3
          )
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "let r = euler313 (30 deg) (45 deg) (60 deg) in transpose r @ r"
              i3
          )
          @?= Right ["true"]
    , testCase "an uncertain angle carries its nudge into the entries" $ do
        -- R00 = cos θ moves at the full rate, R01 = sin θ only to second order
        evalP
          "let b = bound (expm (rotz (90 deg ± 0.001 rad))) in b.0.0 >= 0.001 && b.0.0 <= 0.0011 && b.1.1 >= 0.001 && b.0.1 <= 1e-5 && b.2.2 == 0"
          @?= Right ["true"]
        -- an angle whose enclosure contains zero: nothing divides by it
        evalP
          ( encloses
              "0.0011"
              "expm (rotz (0 rad ± 0.001 rad))"
              "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
        evalP
          "let b = bound (expm (rotz (0 rad ± 0.001 rad))) in b.0.1 >= 0.001 && b.0.0 <= 1e-5"
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm (rotz (1e-30 rad)) @ e1"
              "[cos (1e-30 rad), sin (1e-30 rad), 0]"
          )
          @?= Right ["true"]
    , testCase "four dimensions: two planes by the series, one plane by Rodrigues" $ do
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 1/2, 0, 0], [-1/2, 0, 0, 0], [0, 0, 0, 1/3], [0, 0, -1/3, 0]]"
              ( T.unwords
                  [ "let a = 0.5 rad in let b = (1/3) * 1 rad in"
                  , "[[cos a, sin a, 0, 0], [-sin a, cos a, 0, 0],"
                  , "[0, 0, cos b, sin b], [0, 0, -sin b, cos b]]"
                  ]
              )
          )
          @?= Right ["true"]
        -- one plane, found exactly: the other two axes are untouched
        evalP
          "let r = expm [[0, 3, 0, 0], [-3, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]] in r.2 == [0, 0, 1, 0] && r.3 == [0, 0, 0, 1]"
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 3, 0, 0], [-3, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]"
              "[[cos (3 rad), sin (3 rad), 0, 0], [-sin (3 rad), cos (3 rad), 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]"
          )
          @?= Right ["true"]
    , testCase "expm of a general matrix: the scaled and squared series" $ do
        evalP (encloses "1e-20" "expm [[1, 0], [0, 2]]" "[[exp 1, 0], [0, exp 2]]")
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 1, 0], [0, 0, 1], [0, 0, 0]]"
              "[[1, 1, 1/2], [0, 1, 1], [0, 0, 1]]"
          )
          @?= Right ["true"]
        -- uncertain entries: the enclosure holds the midpoint matrix's exponential
        evalP
          ( encloses
              "0.1"
              "expm ([[0.1, 0.2], [0.3, -0.1]] ± 0.01)"
              "expm [[0.1, 0.2], [0.3, -0.1]]"
          )
          @?= Right ["true"]
        -- nearly antisymmetric (two fresh nudges where one would cancel):
        -- Rodrigues with the symmetric part's bound, not the slow series
        let near =
              "let x = sqrt 2 in let y = sqrt 3 in [[0, x * y, 0], [(0 - x) * y, 0, 0], [0, 0, 0]]"
        expectError
          (evalP ("let b = " <> near <> " in b + transpose b == 0 * b"))
          "decide"
        evalP
          ( encloses
              "1e-20"
              ("expm (" <> near <> ")")
              "let a = sqrt 6 * 1 rad in [[cos a, sin a, 0], [-sin a, cos a, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
        evalP "expm [[1, 2], [3, 4]]"
          @?= Right
            [ "[51.968956198705003658…, 74.736564567003212549…; 112.10484685050481882…, 164.07380304920982248…]"
            ]
    , testCase "expm is dimensionless" $ do
        typeOfTextP "expm" @?= Right "forall n. Mat n n -> Mat n n"
        expectError (evalP "expm [[1 m]]") "dimensions differ"
        expectError (evalP "expm (rotz (1 m))") "expected Num rad, got Num m"
        expectError (evalP "rotz 1") "expected Num rad, got Num"
    , testCase "transformBy applies R along every axis" $ do
        let r = "[[1, 2, 0], [3, 4, 1], [0, 1, 5]]"
            s = "[[2, 0, 1], [1, 1, 0], [0, 3, 1]]"
            p = "[[2, 1, 0], [1, 3, 1], [0, 7, 4]]"
        evalP ("transformBy " <> r <> " [1, -2, 3] == " <> r <> " @ [1, -2, 3]")
          @?= Right ["true"]
        evalP
          ( "transformBy "
              <> r
              <> " "
              <> p
              <> " == "
              <> r
              <> " @ "
              <> p
              <> " @ transpose "
              <> r
          )
          @?= Right ["true"]
        evalP
          ( "let a = [1, 2, 3] in let b = [0, -1, 2] in let c = [4, 0, 1] in transformBy "
              <> r
              <> " (a ⊗ b ⊗ c) == ("
              <> r
              <> " @ a) ⊗ ("
              <> r
              <> " @ b) ⊗ ("
              <> r
              <> " @ c)"
          )
          @?= Right ["true"]
        evalP
          ( "transformBy "
              <> r
              <> " (transformBy "
              <> s
              <> " "
              <> p
              <> ") == transformBy ("
              <> r
              <> " @ "
              <> s
              <> ") "
              <> p
          )
          @?= Right ["true"]
        -- the identity keeps every component as it was, nudges and all
        evalP "let t = [[1, 2], [3, 4]] ± 0.1 in transformBy [[1, 0], [0, 1]] t == t"
          @?= Right ["true"]
        -- a rotation of a covariance
        evalP
          ( encloses
              "1e-20"
              "transformBy (expm (rotz (90 deg))) [[4, 1, 0], [1, 9, 0], [0, 0, 1]]"
              "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
    , testCase "transformBy keeps the dimension and the display unit" $ do
        evalP "transformBy [[0, 1], [1, 0]] ([1, 2] km)" @?= Right ["[2, 1] km"]
        evalP "transformBy [[0, 1], [1, 0]] ([[1, 2], [3, 4]] km)"
          @?= Right ["[4, 3; 2, 1] km"]
        evalP "transformBy [[0, 1], [1, 0]] (5 km)" @?= Right ["5 km"]
        typeOfTextP "transformBy"
          @?= Right "forall n s d. Mat n n -> Tensor s d -> Tensor s d"
        typeOfTextP "transformBy (expm (rotz (10 deg))) ([1, 2, 3] m)"
          @?= Right "Vec 3 m"
    , testCase "transformBy refuses an axis of another length, at run time" $ do
        expectError
          (evalP "transformBy [[1, 2], [3, 4]] [1, 2, 3]")
          "transformBy: every axis must have length n: the matrix is 2 × 2 and the tensor's lengths are [3]"
        expectError
          (evalP "transformBy [[1, 2], [3, 4]] [[1, 2, 3], [4, 5, 6]]")
          "every axis must have length n: the matrix is 2 × 2 and the tensor's lengths are [2, 3]"
    , testCase "the constructors' types" $ do
        typeOfTextP "e1" @?= Right "Vec 3"
        typeOfTextP "rotx" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "roty" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "rotz" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "dual"
          @?= Right
            "forall (a : 3) s d (b : 3) (c : 3). Tensor (a : s) d -> Tensor (b : c : s) d"
        typeOfTextP "axisAngle"
          @?= Right "forall (a : 3) d (b : 3) (c : 3). Vec a d -> Num rad -> Mat b c"
        typeOfTextP "rotation"
          @?= Right "forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a b"
        typeOfTextP "euler313"
          @?= Right "forall (a : 3). Num rad -> Num rad -> Num rad -> Mat a a"
    , testCase "rotz is θ (e2 ∧ e1): ∧ turns its second vector toward its first" $ do
        evalP "e1 /\\ e2" @?= Right ["[0, 1, 0; -1, 0, 0; 0, 0, 0]"]
        evalP "rotz (90 deg) == pi / 2 * (e2 /\\ e1)" @?= Right ["true"]
        evalP "rotx (1 rad)" @?= Right ["[0, 0, 0; 0, 0, -1; 0, 1, 0]"]
        evalP "roty (1 rad)" @?= Right ["[0, 0, 1; 0, 0, 0; -1, 0, 0]"]
        evalP "rotz (1 rad)" @?= Right ["[0, -1, 0; 1, 0, 0; 0, 0, 0]"]
    , testCase "axisAngle and dual" $ do
        evalP "axisAngle [0, 0, 1] (30 deg) == rotz (30 deg)" @?= Right ["true"]
        evalP "axisAngle [0, 0, 2] (30 deg) == rotz (30 deg)" @?= Right ["true"]
        evalP "axisAngle e1 (1 rad) == rotx (1 rad)" @?= Right ["true"]
        evalP "axisAngle e2 (1 rad) == roty (1 rad)" @?= Right ["true"]
        -- dual is the inverse of ⋆; the generator about n is the dual of -n
        evalP "star (dual [1, 2, 3])" @?= Right ["[1, 2, 3]"]
        evalP "dual e3" @?= Right ["[0, 1, 0; -1, 0, 0; 0, 0, 0]"]
        evalP "dual [1, 2, 3] @ [4, 5, 6] == cross [4, 5, 6] [1, 2, 3]"
          @?= Right ["true"]
        evalP (encloses "1e-20" "expm (axisAngle [1, 1, 1] (120 deg)) @ e1" "e2")
          @?= Right ["true"]
    , testCase "rotation a b takes a to b" $ do
        evalP "rotation e1 e2 == rotz (90 deg)" @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotation e1 e2)" "expm (rotz (90 deg))")
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm (rotation [1, 2, 3] [-2, 0, 1]) @ [1, 2, 3]"
              "norm [1, 2, 3] / norm [-2, 0, 1] * [-2, 0, 1]"
          )
          @?= Right ["true"]
        -- any dimensions: only the directions matter
        evalP "rotation ([1, 0, 0] m) ([0, 5, 0] s) == rotz (90 deg)" @?= Right ["true"]
        -- parallel: the zero bivector; antiparallel: half a turn in the plane through e3
        evalP "rotation [1, 1, 0] [2, 2, 0]" @?= Right ["[0, 0, 0; 0, 0, 0; 0, 0, 0]"]
        evalP (encloses "1e-20" "expm (rotation e1 (-e1)) @ e1" "-e1")
          @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotation e1 (-e1)) @ e2" "e2") @?= Right ["true"]
        -- along e3 itself, the plane through e1
        evalP (encloses "1e-20" "expm (rotation e3 (-e3)) @ e3" "-e3")
          @?= Right ["true"]
    , testCase "euler313 is the perifocal-to-inertial matrix" $ do
        -- Ω = 30°, i = 45°, ω = 60°, entries by the textbook formula
        let q =
              T.unwords
                [ "let o = 30 deg in let i = 45 deg in let w = 60 deg in"
                , "[[cos o * cos w - sin o * sin w * cos i, -cos o * sin w - sin o * cos i * cos w, sin o * sin i],"
                , "[sin o * cos w + cos o * cos i * sin w, -sin o * sin w + cos o * cos i * cos w, -cos o * sin i],"
                , "[sin i * sin w, sin i * cos w, cos i]]"
                ]
        evalP (encloses "1e-20" "euler313 (30 deg) (45 deg) (60 deg)" q)
          @?= Right ["true"]
    , testCase
        "every constructor's bivector is exactly antisymmetric, enclosures and all"
        $ do
          let antisymmetric b = evalP ("let b = " <> b <> " in b + transpose b == 0 * b")
          antisymmetric "rotz (30 deg ± 0.01 rad)" @?= Right ["true"]
          antisymmetric "axisAngle [1, 1, 1] (120 deg)" @?= Right ["true"]
          antisymmetric "axisAngle ([1, 2, 2] ± 0.1) (40 deg ± 0.01 rad)"
            @?= Right ["true"]
          antisymmetric "rotation [1, 2, 3] [-2, 0, 1]" @?= Right ["true"]
          antisymmetric "rotation ([1, 2, 3] ± 0.01) [-2, 0, 1]" @?= Right ["true"]
          antisymmetric "rotation e1 (-e1)" @?= Right ["true"]
    , testCase "an uncertain angle makes a bivector with nudged entries" $ do
        evalP
          "let b = bound (rotz (90 deg ± 0.001 rad)) in b.0.1 >= 0.001 && b.1.0 >= 0.001 && b.0.0 == 0"
          @?= Right ["true"]
        evalP "rotz (90 deg ± 0.001 rad)"
          @?= Right ["[0, -1.5708 ± 0.0012, 0; 1.5708 ± 0.0012, 0, 0; 0, 0, 0]"]
    ]
