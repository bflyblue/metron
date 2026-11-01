-- | Axis slots, named axes, spaces and frames.
module Lang.Frames (
  axisSlotTests,
  namedAxesTests,
  partFTests,
) where

import Control.Monad (forM_)
import Data.Bifunctor (first)
import Data.ByteString qualified as BS (pack, replicate)
import Data.Maybe (fromMaybe, isJust)
import Data.Text qualified as T (isInfixOf, unpack)
import Lang.Common (
  eciChart,
  encloses,
  evalP,
  expectError,
  expecting,
  lastN,
  linesIn,
  lvlhCharts,
  multiline,
  persistLines,
  prim2,
  reload,
  runLines,
  runLinesP,
  sessionOf,
  sessionP,
  withTempStore,
 )
import Metron.Builtin (axesDef, frameDef, spaceDef)
import Metron.Codebase (
  Codebase (names, signatures),
  lookupTypeName,
 )
import Metron.Core (
  Fin (FZ),
  Hash (Hash),
  Label (Owner),
  Lit (LTensor),
  NudgeKind (Bound),
  Term (Lam, Let, Lit, Noise, Ref, Var),
  showHash,
 )
import Metron.Dimension (DimAtom (Base), dimFromAtoms, dimOne)
import Metron.Dimension qualified as Dimension (BaseDim (L))
import Metron.Driver (Session (codebase, staging), exportSource)
import Metron.Hash (decodeTypeDef, encodeTypeDef, hashTypeDef)
import Metron.Infer (TypeError (..), elaborateClosed)
import Metron.Primitive.Types (primScheme)
import Metron.TCore (TTerm (TPrimApp, TRef), lintClosed)
import Metron.Type (
  Arg (AAxis, ALen),
  Axis (AAnon, ANamed, AVar),
  Frame (Frame),
  FrameSlot (FrNamed),
  Kind (KAxis, KLen),
  Len (LLit, LVar),
  Scheme (Forall),
  Shape (SCons, SNil),
  Space (Space),
  SpaceSlot (SpNamed),
  Type (TChart, TData, TFun, TOver, TPoint, TTensor),
  TypeDef (TypeDef),
  TypeLookup (TypeLookup),
  selfType,
  structuralLabel,
 )
import Metron.Type.Match (isInstanceOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

-- Axis slots ------------------------------------------------------------------

{- | Design §3.9, stage 2b, and §3.10, part F: a chart declaration mints its
frame, and its axes when it turns; points are typed by their frames, and
amounts and rotations by the axes. Each turned chart here is only typed,
or used once, since its rotation costs an @expm@.
-}
namedAxesTests :: TestTree
namedAxesTests =
  testGroup
    "named axes"
    [ testCase "a chart mints a frame, named as the chart" $ do
        runLinesP [eciChart, ":ls --types eci", ":type eci"]
          @?= Right ["frame eci", "Chart eci"]
        -- Two charts of one body: two frames, two hashes.
        s <- sessionOf [eciChart, "chart lab on GCRS"]
        lookupTypeName "eci" s.staging /= lookupTypeName "lab" s.staging
          @? "one frame for two charts"
        isJust (lookupTypeName "eci" s.staging) @? "no frame for eci"
        linesIn s [":hash eci"] /= linesIn s [":hash lab"] @? "one hash for two charts"
        -- No source declaration has the frame's label kind.
        u <- sessionOf [eciChart, "data Eci = Eci"]
        lookupTypeName "Eci" u.staging /= lookupTypeName "eci" u.staging
          @? "a data type is a chart's frame"
        hashTypeDef (frameDef "eci" False)
          /= hashTypeDef (TypeDef [] [[]] (Owner "eci"))
          @? "an owner stamp is a frame stamp"
        hashTypeDef (frameDef "eci" False) /= hashTypeDef (frameDef "eci" True)
          @? "a frame with parameters is the same type as one without"
        decodeTypeDef (encodeTypeDef (frameDef "eci" True))
          @?= Right (frameDef "eci" True)
        decodeTypeDef (encodeTypeDef (axesDef "eci")) @?= Right (axesDef "eci")
        let inertial = spaceDef "GCRS" [3] (dimFromAtoms [(Base Dimension.L, 1)])
        decodeTypeDef (encodeTypeDef inertial) @?= Right inertial
        expectError
          (linesIn u ["mkChart {Eci} {} eci {} {} {} {}"])
          "mkChart takes the frame a chart declaration mints first"
        -- A rescaling shares its parent's frame and mints none; a scalar
        -- chart's frame is named too.
        t <- sessionOf [eciChart, "chart ekm on eci step km"]
        lookupTypeName "ekm" t.staging @?= Nothing
        isJust (lookupTypeName "temperature.degC" t.staging) @? "no frame for degC"
        linesIn t [":type [1, 2, 3] ekm", "[1, 2, 3] ekm .- [0, 0, 0] eci"]
          @?= Right ["Point eci", "[1000, 2000, 3000] m"]
        -- The frame of a renamed chart follows it.
        r <- sessionOf [eciChart, ":add", ":rename eci frame"]
        linesIn r [":ls --types frame", ":type [1, 2, 3] frame"]
          @?= Right ["frame frame", "Point frame"]
    , testCase "a point is on its frame; rotationOf is Mat space frame" $ do
        runLinesP
          ( lvlhCharts
              ++ [ ":type [1, 2, 3] lvlh"
                 , ":type [1, 2, 3] lvlh .- [0, 0, 0] lvlh"
                 , ":type rotationOf lvlh"
                 , ":type [1, 0, 0] m to lvlh"
                 , ":type spinOf lvlh"
                 , ":type rotationOf lvlh @ ([1, 0, 0] m to lvlh)"
                 , ":type ([1, 0, 0] m to lvlh) from lvlh to eci"
                 ]
          )
          @?= Right
            [ "Point lvlh"
            , "Vec lvlh m"
            , "Mat GCRS lvlh"
            , "Vec lvlh m"
            , "Vec GCRS (1/s)"
            , "Vec GCRS m"
            , "Vec GCRS m"
            ]
        runLinesP
          ( lvlhCharts
              ++ [ encloses "1e-20" "(([1, 2, 3] m to lvlh) from lvlh to eci) / 1 m" "[1, 2, 3]"
                 , encloses "1e-20" "det (rotationOf lvlh)" "1"
                 ]
          )
          @?= Right ["true", "true"]
        -- A chart parameter writes a point on any frame.
        runLinesP
          ( lvlhCharts
              ++ ["let place c x = pointOn c x", ":type place", "place lvlh [1, 2, 3]"]
          )
          @?= Right ["forall c. Chart c -> Coords c -> Point c", "[1, 2, 3] lvlh"]
        -- The wrong rotation is a type error.
        expectError
          ( runLinesP
              (lvlhCharts ++ ["let v = [1, 2, 3] eci .- [0, 0, 0] eci", "rotationOf lvlh @ v"])
          )
          "the axes of lvlh against the axes of GCRS"
    , testCase "a literal takes its frame from use; a named value is anonymous" $ do
        let setup = lvlhCharts ++ ["let p = [1, 2, 3] eci", "let off = [0, 0, 2] m"]
        runLinesP
          (setup ++ ["p .+ [1, 0, 0] m", ":type off", ":type withAxes lvlh off"])
          @?= Right ["[2, 2, 3] eci", "Vec 3 m", "Vec lvlh m"]
        expectError
          (runLinesP (setup ++ ["p .+ off"]))
          "the axes of GCRS against anonymous axes; give it a frame with `withAxes c v`, or `v to c` if it is along its space's base axes"
        -- A function keeps its frame general; a value meets a frame through
        -- withAxes or a signature that keeps it polymorphic.
        runLinesP
          ( setup
              ++ [ "let shift q = q .+ [1, 0, 0] m"
                 , ":type shift"
                 , "shift p"
                 , encloses
                     "1e-20"
                     "(p .+ (withAxes lvlh off from lvlh to eci) .- p) / 1 m"
                     "[0, 0, 2]"
                 , multiline ["off2 :: forall (a : 3). Vec a m", "let off2 = [0, 0, 2] m"]
                 , ":ls off2"
                 , "p .+ off2"
                 , -- :type is the type of `it`, a named value
                   ":type off2"
                 ]
          )
          @?= Right
            [ "forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c"
            , "[2, 2, 3] eci"
            , "true"
            , "off2 : forall (a : 3). Vec a m"
            , "[1, 2, 5] eci"
            , "Vec 3 m"
            ]
    , testCase "roots on one space convert; two spaces never meet" $ do
        let setup = [eciChart, "chart lab on GCRS", "let p = [1, 2, 3] eci"]
        runLinesP
          (setup ++ ["p to lab", "(p .- [0, 0, 0] eci) + ([1, 0, 0] lab .- [0, 0, 0] lab)"])
          @?= Right ["[1, 2, 3] lab", "[2, 2, 3] m"]
        let apart =
              [ eciChart
              , "space Bench = Vec 3 m"
              , "chart lab on Bench"
              , "let p = [1, 2, 3] eci"
              ]
        expectError
          (runLinesP (apart ++ ["p to lab"]))
          "frames of two spaces, GCRS and Bench"
        expectError
          (runLinesP (apart ++ ["(p .- [0, 0, 0] eci) + ([1, 0, 0] lab .- [0, 0, 0] lab)"]))
          "the axes of GCRS against the axes of Bench"
    , testCase "scalar charts are typed by their frames too" $ do
        runLinesP
          [ "20 degC to degF"
          , "77 °F .- 68 °F"
          , ":type 20 degC"
          , ":type degC"
          , "chart warm on ITS90 at 300 K"
          , "1 warm .- 0 warm"
          ]
          @?= Right ["68 degF", "9 deltaF", "Point degC", "Chart degC", "1 K"]
    , testCase "a moving chart has one frame for every time" $ do
        let spinning =
              [ eciChart
              , "let w = 7.2921159e-5 rad/s"
              , "let t0 = 0 unix"
              , "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
              ]
        runLinesP
          ( spinning
              ++ [ ":type rotationOf (spinner t0)"
                 , ":type rotationOf (spinner (t0 .+ 1 s))"
                 , ":type rotationOf (spinner t0) - rotationOf (spinner (t0 .+ 1 s))"
                 , ":type [1, 2, 3] (spinner t0)"
                 ]
          )
          @?= Right
            [ "Mat GCRS spinner"
            , "Mat GCRS spinner"
            , "Mat GCRS spinner"
            , "Point spinner"
            ]
    , testCase "a written type names a frame, its axes and a space's" $ do
        let signed =
              lvlhCharts
                ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] m"]
                   , multiline ["c :: Chart lvlh", "let c = lvlh"]
                   ]
        runLinesP
          ( signed
              ++ [ ":type v"
                 , ":type rotationOf lvlh @ v"
                 , ":type c"
                 , ":type (rotationOf lvlh :: Mat GCRS lvlh)"
                 , ":type (rotationOf lvlh :: Mat eci lvlh)"
                 ]
          )
          @?= Right
            [ "Vec lvlh m"
            , "Vec GCRS m"
            , "Chart lvlh"
            , "Mat GCRS lvlh"
            , "Mat GCRS lvlh"
            ]
        expectError
          (runLinesP (lvlhCharts ++ [":type (rotationOf lvlh :: Mat lvlh GCRS)"]))
          "the axes of"
        runLinesP
          ( lvlhCharts
              ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] lvlh .- [0, 0, 0] lvlh"]
                 , ":type v"
                 ]
          )
          @?= Right ["Vec lvlh m"]
        -- In one group with the chart: a signature framing a chart's
        -- origin, and a data declaration over a chart's axes.
        runLinesP
          [ multiline
              [ eciChart
              , "r0 :: Vec eci m"
              , "let r0 = [7000, 0, 0] km"
              , "chart lvlh on eci at r0 by rotz (90 deg)"
              , "data Obs = Obs (Vec eci m)"
              ]
          , ":type r0"
          , ":type Obs ([1, 2, 3] eci .- [0, 0, 0] eci)"
          , ":type rotationOf lvlh"
          ]
          @?= Right ["Vec GCRS m", "Obs", "Mat GCRS lvlh"]
        -- The group's charts enter first, unchecked: a stored signature a
        -- redefinition they depend on breaks is still checked.
        expectError
          ( runLinesP
              [ eciChart
              , multiline ["k :: Num m", "let k = 3 m"]
              , ":add"
              , multiline
                  ["let k = 2 s", "chart c on eci by rotz (k / 1 s * 1 rad)"]
              ]
          )
          "`k`'s definition has type `Num s`, not as general as its signature `Num m`"
        -- A root chart's origin is along its space's base axes, so a named
        -- value there needs a signature that keeps it polymorphic.
        expectError
          (runLinesP [eciChart, "let o = [100, 200, 0] m", "chart site on GCRS at o"])
          "anonymous axes"
        runLinesP
          [ eciChart
          , multiline ["o :: forall (a : 3). Vec a m", "let o = [100, 200, 0] m"]
          , "chart site on GCRS at o"
          , "[1, 2, 3] site"
          ]
          @?= Right ["[1, 2, 3] site"]
        -- Named slots follow a chart's axes when it is renamed, in a
        -- signature and in a data field, and across a reload.
        let renamed =
              lvlhCharts
                ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] m"]
                   , "data Obs = Obs (Vec lvlh m) (Point lvlh)"
                   , ":add"
                   , ":rename lvlh turned"
                   ]
        moved <- sessionOf renamed
        linesIn moved [":type v", ":view Obs"]
          @?= Right ["Vec turned m", "data Obs = Obs (Vec turned m) (Point turned)"]
        withTempStore $ \dir -> do
          stored <- persistLines dir renamed
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.signatures @?= stored.codebase.signatures
          linesIn loaded [":type v", ":view Obs"]
            @?= Right ["Vec turned m", "data Obs = Obs (Vec turned m) (Point turned)"]
        -- A chart redefined as no chart leaves no frame behind.
        fmap
          (lastN 1)
          (runLinesP [eciChart, ":add", "let eci = 3", ":update", ":ls --types eci"])
          @?= Right ["nothing matches"]
        -- A signature that names a chart's axes reads back in one group
        -- with the chart: through :export and :load, and across a reload.
        s <- sessionOf (signed ++ [":add"])
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        reloaded.codebase.signatures @?= s.codebase.signatures
        reloaded.codebase.names @?= s.codebase.names
        withTempStore $ \dir -> do
          stored <- persistLines dir (signed ++ [":add"])
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.signatures @?= stored.codebase.signatures
          linesIn loaded [":type v"] @?= Right ["Vec lvlh m"]
    , testCase "the library's states are typed by their spaces" $ do
        runLinesP [":use astro", ":type velocityIn", ":type stateFrom"]
          @?= Right
            [ "stored use astro"
            , "forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c -> State c1 s1 -> Vec c (m/s)"
            , "forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c -> Point c1 -> Vec c m -> Vec c (m/s) -> State c1 s1"
            ]
        runLinesP
          ( lvlhCharts
              ++ [ ":use astro"
                 , "let st = stateFrom lvlh (0 unix) ([1, 0, 0] m) ([0, 1, 0] m/s)"
                 , ":type st"
                 , ":type st.pos"
                 , encloses "1e-20" "velocityIn lvlh st / (1 m/s)" "[0, 1, 0]"
                 ]
          )
          @?= Right
            ["stored use astro", "State unix GCRS", "Vec GCRS m", "true"]
    ]

{- | The name slot of a shape position (design §3.9, stage 1). These read
definitions whose stored types carry a named set by hash, with no chart
behind it, and check the unifier, lint and the encoding on the slot
directly; 'namedAxesTests' has them from source.
-}
axisSlotTests :: TestTree
axisSlotTests =
  testGroup
    "axis slots"
    [ testCase "a named axis set does not unify with anonymous axes"
        $ typed (prim2 "add" (ref lvlhV) (Noise Bound (Owner "") 3))
          @?= Left
            ( "expected Vec "
                <> showHash lvlh
                <> ", got Vec 3: the axes of "
                <> showHash lvlh
                <> " against anonymous axes; give it a frame with `withAxes c v`, or `v to c` if it is along its space's base axes"
            )
    , testCase "a literal takes the axes of what it meets (decision 5)"
        $ typed (prim2 "add" (ref lvlhV) (Lit (LTensor ([3], [1, 2, 3]))))
          @?= Right [Forall [] (vecAlong lvlh)]
    , testCase "a local value's free axes are anonymous (decision 5)"
        $ typed
          ( Let
              "off"
              (Lit (LTensor ([3], [1, 2, 3])))
              (prim2 "add" (Var FZ) (Noise Bound (Owner "") 3))
          )
          @?= Right [Forall [] (TTensor (pos (LLit 3) AAnon SNil) dimOne)]
    , testCase "two named axis sets do not unify"
        $ typed (prim2 "add" (ref lvlhV) (ref eciV))
          @?= Left
            ( "expected Vec "
                <> showHash lvlh
                <> ", got Vec "
                <> showHash eci
                <> ": the axes of "
                <> showHash lvlh
                <> " against the axes of "
                <> showHash eci
            )
    , testCase "an axis variable binds to a named set"
        $ typed (Lam "v" (prim2 "add" (Var FZ) (ref lvlhV)))
          @?= Right [Forall [] (TFun (vecAlong lvlh) (vecAlong lvlh))]
    , testCase "dot's contracted positions share one axis variable" $ do
        -- Rows along eci, columns along lvlh, applied to a vector along
        -- lvlh: a vector along eci.
        typed (prim2 "dot" (ref rot) (ref lvlhV)) @?= Right [Forall [] (vecAlong eci)]
        case typed (prim2 "dot" (ref rot) (ref eciV)) of
          Left err -> "the axes of" `T.isInfixOf` err @? T.unpack err
          Right sc -> assertFailure (show sc)
        -- An unknown left operand takes the right's axes at the contracted
        -- position.
        case typed (Lam "v" (prim2 "dot" (Var FZ) (ref lvlhV))) of
          Right [Forall _ (TFun (TTensor left _) _)] -> left @?= pos (LLit 3) (ANamed lvlh) SNil
          other -> assertFailure (show other)
    , testCase "an instance substitutes axis variables" $ do
        let scheme p = fromMaybe (error "no scheme") (primScheme p)
            e = (LLit 3, ANamed eci)
            l = (LLit 3, ANamed lvlh)
        TFun (mat e l) (mat l e) `isInstanceOf` scheme "transpose" @?= True
        TFun (mat e l) (mat e l) `isInstanceOf` scheme "transpose" @?= False
        TFun (mat e l) (mat l e) `isInstanceOf` scheme "inverse" @?= True
        TFun (mat l l) (vecAlong lvlh) `isInstanceOf` scheme "star" @?= True
        TFun (mat e l) (vecAlong lvlh) `isInstanceOf` scheme "star" @?= False
    , testCase "lint checks the contracted axes of dot" $ do
        let at r =
              TPrimApp
                "dot"
                ( TFun
                    (TTensor (pos (LLit 3) (ANamed eci) (pos (LLit 3) (ANamed lvlh) SNil)) dimOne)
                    (TFun (vecAlong r) (vecAlong eci))
                )
                [TRef rot Nothing "", TRef (if r == lvlh then lvlhV else eciV) Nothing ""]
        lintClosed look (at lvlh) @?= Right [Forall [] (vecAlong eci)]
        lintClosed look (at eci)
          @?= Left
            "dot: the right operand's first length and axes are not the left operand's last"
    , testCase "an anonymous position keeps the bytes of a bare length" $ do
        let def ax = TypeDef [] [[TTensor (pos (LLit 3) ax SNil) dimOne]] structuralLabel
        -- no parameters, one constructor of one field: a tensor whose shape
        -- is tag 1, the length 3, the end; no dimension; the structural label
        encodeTypeDef (def AAnon) @?= BS.pack [0, 1, 1, 0x21, 1, 0, 3, 0, 0, 1, 0]
        -- a variable slot is tag 3, the length, the axis (2, its id), the end
        encodeTypeDef (def (AVar 5))
          @?= BS.pack [0, 1, 1, 0x21, 3, 0, 3, 2, 5, 0, 0, 1, 0]
    , testCase "named and variable slots encode under their own tags and decode back" $ do
        let def =
              TypeDef
                [(0, KLen), (1, KAxis)]
                [
                  [ TTensor (pos (LVar 0 0) (AVar 1) (pos (LLit 3) (ANamed lvlh) SNil)) dimOne
                  , TChart
                      ( Frame
                          (FrNamed lvlh)
                          (ANamed lvlh)
                          (Space (SpNamed eci) (pos (LLit 3) AAnon SNil) dimOne (ANamed eci))
                      )
                  , TPoint
                      ( Frame
                          (FrNamed lvlh)
                          (AVar 1)
                          (Space (SpNamed eci) (pos (LLit 3) AAnon SNil) dimOne (AVar 1))
                      )
                  , TOver
                      (Frame (FrNamed lvlh) (AVar 1) (Space (SpNamed eci) SNil dimOne AAnon))
                      (Just dimOne)
                  , TData selfType [ALen (LLit 2), AAxis AAnon]
                  ]
                ]
                structuralLabel
        decodeTypeDef (encodeTypeDef def) @?= Right def
    ]
 where
  eci = Hash (BS.replicate 32 0xe1)
  lvlh = Hash (BS.replicate 32 0x1f)
  eciV = Hash (BS.replicate 32 0xa1)
  lvlhV = Hash (BS.replicate 32 0xa2)
  rot = Hash (BS.replicate 32 0xa3)
  pos = SCons
  vecAlong a = TTensor (pos (LLit 3) (ANamed a) SNil) dimOne
  mat (r, x) (c, y) = TTensor (pos r x (pos c y SNil)) dimOne
  stored =
    [ (eciV, vecAlong eci)
    , (lvlhV, vecAlong lvlh)
    , (rot, mat (LLit 3, ANamed eci) (LLit 3, ANamed lvlh))
    ]
  look = TypeLookup (\k -> (\t -> [Forall [] t]) <$> lookup k stored) (const Nothing)
  ref k = Ref k Nothing ""
  -- Elaborated and linted.
  typed t = do
    (schemes, tt) <- first (.message) (elaborateClosed look t)
    _ <- first ("lint: " <>) (lintClosed look tt)
    pure schemes

{- | Design §3.10, part F, from source: every decision and every example it
writes, with the library's spaces and charts.
-}
partFTests :: TestTree
partFTests =
  testGroup
    "spaces and frames (design §3.10, part F)"
    [ testCase "pointAt places an amount on a chart from its origin along its axes" $ do
        let setup =
              [ "space Shop = Vec 3 m"
              , "chart room on Shop"
              , "chart bench on room at [2, 1, 0] m by rotz (90 deg)"
              , "chart pf on room step km by rotz (30 deg) then rotx (45 deg)"
              ]
        runLinesP
          ( setup
              ++ [ ":type pointAt"
                 , "pointAt bench ([1, 2, 3] m)"
                 , -- the origin and the step apply; the axes are the chart's
                   "pointAt pf ([1, 2, 3] m)"
                 , "pointAt pf ([1, 2, 3] m) == [0, 0, 0] pf .+ withAxes pf ([1, 2, 3] m)"
                 , "pointAt bench ([1, 2, 3] m) .- [0, 0, 0] bench"
                 , "let q = (pointAt bench ([1, 0, 0] m) to room) .- [2, 2, 0] room"
                 , "q · q < 1e-40 m^2"
                 , -- a computed amount along the chart's axes
                   "let off = withAxes pf ([0, 0, 2] m)"
                 , "pointAt pf (off + off)"
                 , -- a scalar chart: degC's origin is 273.15 K
                   "pointAt degC (5 K)"
                 , "pointAt degF (9 deltaF) to degC"
                 ]
          )
          @?= Right
            [ "forall c. Chart c -> Diff c -> Point c"
            , "[1, 2, 3] bench"
            , "[0.001, 0.002, 0.003] pf"
            , "true"
            , "[1, 2, 3] m"
            , "true"
            , "[0, 0, 0.004] pf"
            , "5 degC"
            , "-12.777777777777777777… degC"
            ]
        -- An amount along another chart's axes is not silently relabelled.
        expectError
          (runLinesP (setup ++ ["pointAt pf (withAxes bench ([1, 2, 3] m))"]))
          "the axes of"
    , testCase "shared chart configurations cancel before uncertainty arithmetic" $ do
        runLinesP
          [ "space Review = Vec 3 m"
          , "chart root on Review"
          , "chart parent on root by rotz (30 deg ± 0.1 rad)"
          , "chart a on parent at [1, 0, 0] m"
          , "chart b on parent at [2, 0, 0] m"
          , "([0, 0, 0] a to b) == [-1, 0, 0] b"
          , "let v = withAxes parent ([1, 0, 0] m)"
          , "(v from parent to parent) == v"
          , "(v from a to b) == v"
          , "chart scaled on parent step km"
          , "(v from scaled to parent) == v"
          , "chart moving angle on root by rotz angle"
          , "let w = withAxes (moving (0 rad)) ([1, 0, 0] m)"
          , encloses
              "1e-20"
              "(w from (moving (0 rad)) to (moving (90 deg))) / 1 m"
              "[0, -1, 0]"
          , "chart child angle on (moving angle) at [1, 0, 0] m"
          , encloses
              "1e-20"
              "(([0, 0, 0] (child (0 rad)) from (child (0 rad)) to (moving (90 deg))) .- [0, 0, 0] (moving (90 deg))) / 1 m"
              "[0, -1, 0]"
          ]
          @?= Right (replicate 6 "true")
    , testCase "a chart whose step may be zero is refused by name" $ do
        let session =
              [ "unit zero = 0 m"
              , "unit fuzz = 0 m ± 1 m"
              , "unit wobble = 1 m ± 2 m"
              , "unit two = 2 m"
              , "space Length = Num m"
              , "chart origin on Length"
              , "chart collapsed on origin step zero"
              , "chart fuzzy on origin step fuzz"
              , "chart wide on origin step wobble"
              , "chart under on collapsed step two"
              , "chart root on Length step zero"
              ]
            refused use = runLines (session ++ [use])
        refused "1 collapsed == 2 collapsed"
          @?= Left "error: chart collapsed has no invertible coordinates: its step is zero"
        refused "1 fuzzy"
          @?= Left
            "error: chart fuzzy has no invertible coordinates: its step's enclosure reaches zero"
        refused "1 wide"
          @?= Left
            "error: chart wide has no invertible coordinates: its step's enclosure reaches zero"
        -- a chart on it inherits the refusal, which names the culprit
        refused "1 under"
          @?= Left "error: chart collapsed has no invertible coordinates: its step is zero"
        refused "1 root"
          @?= Left "error: chart root has no invertible coordinates: its step is zero"
    , testCase "a negative step reverses a chart's direction"
        $ runLines
          [ "unit back = -1 m"
          , "unit kback = -1000 m"
          , "space Length = Num m"
          , "chart origin on Length"
          , "chart flipped on origin step back"
          , "chart far on origin at 5 m step kback"
          , "3 flipped"
          , "(3 flipped) to origin"
          , "(3 origin) to flipped"
          , "(3 flipped) .- (1 flipped)"
          , "((3 flipped) .- (1 flipped)) to m"
          , "(1 origin) .- (3 flipped)"
          , "(3 flipped) .+ 1 m"
          , "(2 far) to origin"
          , "(2 far) to flipped"
          , "((2 far) to origin) == (-1995 origin)"
          ]
          @?= Right
            [ "3 flipped"
            , "-3 origin"
            , "-3 flipped"
            , "2 back"
            , "-2 m"
            , "4 m"
            , "2 flipped"
            , "-1995 origin"
            , "1995 flipped"
            , "true"
            ]
    , testCase
        "restricted frame types print signatures that preserve their constraints"
        $ do
          let body = "let shift q = q .+ [1, 0, 0] m"
          expecting (runLinesP [body, ":type shift"]) $ \outs -> case outs of
            [ty] -> do
              ty @?= "forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c"
              runLinesP [multiline ["shift :: " <> ty, body], ":type shift"] @?= Right [ty]
              expectError (runLinesP [body, "shift (20 degC)"]) "a vector against a number"
              expectError
                (runLinesP [body, "shift :: forall c. Point c -> Point c"])
                "Space (Vec 3 m)"
              withTempStore $ \dir -> do
                stored <- persistLines dir [multiline ["shift :: " <> ty, body], ":add"]
                (loaded, notes) <- reload dir
                notes @?= []
                loaded.codebase.signatures @?= stored.codebase.signatures
                linesIn loaded [":type shift"] @?= Right [ty]
                source <- either (assertFailure . T.unpack) pure (exportSource stored Nothing)
                restored <- either (assertFailure . T.unpack) pure (sessionP [source, ":add"])
                restored.codebase.signatures @?= stored.codebase.signatures
            _ -> assertFailure (show outs)
    , testCase "F1: kinds; a binder names its frame's space" $ do
        runLinesP
          [ multiline
              [ "diffK :: forall (c : ITS90). Point c -> Point c -> Num K"
              , "let diffK p q = p .- q"
              ]
          , "diffK (20 degC) (10 degC)"
          , "diffK (491.67 degR) (0 kelvin)"
          , ":ls diffK"
          , multiline
              [ "conv :: forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
              , "let conv p c = p to c"
              ]
          , "conv (20 degC) degF"
          , ":ls conv"
          , ":type \\p q -> p .- q"
          ]
          @?= Right
            [ "10 K"
            , "273.15 K"
            , "diffK : forall (c : ITS90). Point c -> Point c -> Num K"
            , "68 degF"
            , "conv : forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
            , "forall c. Point c -> Point c -> Diff c"
            ]
        -- A frame of one space is not a frame of another: a kind error.
        expectError
          ( runLinesP
              ( eciChart
                  : [ multiline
                        [ "conv :: forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
                        , "let conv p c = p to c"
                        ]
                    , "conv (20 degC) eci"
                    ]
              )
          )
          "frames of two spaces, ITS90 and GCRS"
        expectError
          (runLinesP ["f :: forall (c : Kelvin). Point c -> Point c", "let f p = p"])
          "`Kelvin` is not a space"
    , testCase "F2: spaces are declared and nominal; a chart names its space" $ do
        runLinesP
          ( eciChart
              : [ ":view ITS90"
                , -- TT is also si.TT, the teratesla: both show
                  ":view TT"
                , ":view UTC"
                , ":view GCRS"
                , ":type [1, 2, 3] eci .- [0, 0, 0] eci"
                , "space Other = Num K"
                , "chart oC on Other at 273.15 K"
                , "20 oC .- 0 oC"
                ]
          )
          @?= Right
            [ "space ITS90 = Num K"
            , "-- time.TT"
            , "space TT = Num s"
            , "-- si.TT"
            , "TT = tera * 1 T"
            , "space UTC = Num s"
            , "space GCRS = Vec 3 m"
            , "Vec GCRS m"
            , "20 K"
            ]
        -- Two spaces declared alike are two spaces: their points never convert.
        expectError
          (runLinesP ["space Other = Num K", "chart oC on Other", "20 degC to oC"])
          "frames of two spaces, ITS90 and Other"
        expectError
          (runLinesP [eciChart, "20 degC to eci"])
          "frames of two spaces, ITS90 and GCRS"
        -- TT and UTC are two spaces with no chart between them (design
        -- §3.10, F2): a unix instant and a J2000 one never meet.
        expectError (runLinesP ["0 unix .- 0 J2000"]) "frames of two spaces, UTC and TT"
        expectError (runLinesP ["0 unix to J2000"]) "frames of two spaces, UTC and TT"
        -- No point is written on a space's base, and a chart names its space.
        expectError (runLinesP ["3 ITS90"]) "unknown name `ITS90`"
        expectError
          (runLinesP ["chart degC2 at 273.15 K"])
          "name its space: `chart … on ITS90`"
        expectError
          (runLinesP ["space Bad = Mat 2 2 m"])
          "a space is of numbers or of vectors"
    , testCase "F3: what a chart declaration says decides whether it mints a frame" $ do
        runLinesP
          ( eciChart
              : [ -- a root, an origin, turned axes: each a frame
                  ":type 0 kelvin"
                , "chart warm on degC at 10 K"
                , ":type 0 warm"
                , "0 warm .- (10 degC to warm)"
                , "chart turned on eci by rotz (30 deg)"
                , ":type [1, 2, 3] turned .- [0, 0, 0] turned"
                , -- a step alone is a rescaling: its parent's frame
                  "chart mdegC on degC step mK"
                , ":type 20 mdegC"
                , "20000 mdegC .- 20 degC"
                , "20000 mdegC"
                , -- Rankine is kelvin rescaled: no `to` between them
                  ":type 491.67 degR"
                , "491.67 degR .- 0 kelvin"
                , "(0 kelvin .+ 1 K) to degR"
                ]
          )
          @?= Right
            [ "Point kelvin"
            , "Point warm"
            , "0 K"
            , "Vec turned m"
            , "Point degC"
            , "0 K"
            , "20000 mdegC"
            , "Point kelvin"
            , "273.15 K"
            , "1.8 degR"
            ]
        -- Two charts declared alike are two frames, like two newtypes.
        expectError
          (runLinesP ["chart a1 on ITS90", "chart a2 on ITS90", "0 a1 .- 0 a2"])
          "points on a1 and a2: convert one with `to`"
        -- A chart with parameters is one frame for all its arguments.
        runLinesP
          ( earth
              ++ [ ":type ecef"
                 , ":type ecef (100 J2000)"
                 , ":type [1, 2, 3] (ecef (100 J2000)) .- [0, 0, 0] (ecef (200 J2000))"
                 ]
          )
          @?= Right ["Point J2000 -> Chart ecef", "Chart ecef", "Vec ecef m"]
    , testCase "F3: two bodies are two declarations; what they share is a function" $ do
        let siblings =
              eciChart
                : [ "let posA t = withAxes eci ([7000, 0, 0] km)"
                  , "let posB t = withAxes eci ([0, 7000, 0] km)"
                  , "let lvlhTurn r = rotz (atan2 r.1 r.0)"
                  , "chart lvlhA t on eci at posA t by lvlhTurn (posA t)"
                  , "chart lvlhB t on eci at posB t by lvlhTurn (posB t)"
                  , "let t0 = 0 unix"
                  , "let a = [1, 0, 0] (lvlhA t0)"
                  , "let b = [0, 1, 0] (lvlhB t0)"
                  ]
        runLinesP (siblings ++ [":type a", ":type b", "b .- b"])
          @?= Right ["Point lvlhA", "Point lvlhB", "[0, 0, 0] m"]
        expectError
          (runLinesP (siblings ++ ["b .- a"]))
          "points on lvlhB and lvlhA: convert one with `to`"
        expectError
          (runLinesP (siblings ++ ["(a .- a) + (b .- b)"]))
          "the axes of lvlhA against the axes of lvlhB"
        -- Converted to one frame, they subtract.
        runLinesP
          ( siblings
              ++ [ encloses
                     "1e-15"
                     "((b from (lvlhB t0) to eci) .- (a from (lvlhA t0) to eci)) / 1 m"
                     "[-7000002, 7000000, 0]"
                 ]
          )
          @?= Right ["true"]
    , testCase "F4: Point, Chart, Diff and Axes; Diff reduces once the space is known" $ do
        runLinesP
          ( lvlhCharts
              ++ [ ":type 20 degC .- 10 degC"
                 , ":type 20 degF .- 10 degF"
                 , ":type [1, 2, 3] lvlh .- [0, 0, 0] lvlh"
                 , "chart bench on GCRS at [1, 0, 0] m"
                 , ":type [1, 2, 3] bench .- [0, 0, 0] bench"
                 , multiline ["d :: Diff lvlh", "let d = [1, 0, 0] m"]
                 , ":type d"
                 , multiline ["k :: Coords lvlh", "let k = [1, 0, 0]"]
                 , ":type k"
                 , ":type \\p q -> p .- q"
                 , ":type \\c -> pointOn c"
                 , multiline
                     [ "good :: forall (c : GCRS). Point c -> Point c -> Num m"
                     , "let good p q = norm (p .- q)"
                     ]
                 , "good ([3, 4, 0] eci) ([0, 0, 0] eci)"
                 ]
          )
          @?= Right
            [ "Num K"
            , "Num K"
            , "Vec lvlh m"
            , "Vec GCRS m"
            , "Vec lvlh m"
            , "Vec lvlh"
            , "forall c. Point c -> Point c -> Diff c"
            , "forall c. Chart c -> Coords c -> Point c"
            , "5 m"
            ]
        -- Arithmetic on Diff of a frame whose space nothing says waits, and
        -- is refused when the definition is generalised.
        expectError
          (runLinesP ["let bad p q = vmap abs (p .- q)"])
          "the amount between points on a frame of a space not known here: give a signature naming the space"
    , testCase "F5: the primitives over frames; another frame is reported as one" $ do
        runLinesP
          ( lvlhCharts
              ++ [ ":type pointOn"
                 , ":type toChart"
                 , ":type rotationOf"
                 , ":type withAxes"
                 , "([1.5, 2.25, 3] lvlh).0"
                 , ":type ([1.5, 2.25, 3] lvlh).2"
                 ]
          )
          @?= Right
            [ "forall c. Chart c -> Coords c -> Point c"
            , "forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
            , "forall s (c : s). Chart c -> Mat s c"
            , "forall (s : Space (Vec n d)) (c : s) (n : Len) d d1. Chart c -> Vec n d1 -> Vec c d1"
            , "1.5 m"
            , "Num m"
            ]
        expectError
          (evalP "20 degC .- 68 degF")
          "points on degC and degF: convert one with `to`"
        expectError (evalP "20 degC .+ (5 degC)") "an amount and a point"
    , testCase "F6: a point holds its coordinates on its frame, the step applied" $ do
        runLinesP
          ( lvlhCharts
              ++ [ "20 degC .- 0 degC"
                 , -- printed on the chart it was written on, the step divided out
                   "chart ground on eci at [100, 200, 0] m step km"
                 , "[7, 0, 0] ground"
                 , "[7, 0, 0] ground .- [0, 0, 0] ground"
                 , -- inside a turned frame, exact: no rotation applies
                   "[1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , "([1, 2, 3] lvlh .+ [1, 0, 0] m).0"
                 , -- a point fixed on a moving body is a constant
                   "chart spinner t on eci by rotz (1 rad/s * (t .- 0 unix)) spinning [0, 0, 1] rad/s"
                 , "[1, 2, 3] (spinner (0 unix)) == [1, 2, 3] (spinner (100 unix))"
                 ]
          )
          @?= Right
            [ "20 K"
            , "[7, 0, 0] ground"
            , "[7, 0, 0] km"
            , "[1, -3, 3] m"
            , "2 m"
            , "true"
            ]
    , testCase "F7: a chart with parameters is converted from a named configuration" $ do
        let sat =
              earth
                ++ [ ":add"
                   , "data Sat = Sat {epoch :: Point J2000, pos :: Vec ecef m}"
                   , "let lvlhTurn s = rotz (atan2 s.pos.1 s.pos.0)"
                   , -- linked: the parent applied to the child's own parameters
                     "chart lvlh s on (ecef s.epoch) at s.pos by lvlhTurn s"
                   , "let s = Sat {epoch = 0 J2000, pos = [7000, 0, 0] km}"
                   , "let t0 = 0 J2000"
                   , "let p = [1, 2, 3] (lvlh s)"
                   ]
        lastN 4
          <$> runLinesP
            ( sat
                ++ [ ":type p"
                   , encloses
                       "1e-12"
                       "((p from (lvlh s) to (ecef t0)) .- [7000000, 0, 0] (ecef t0)) / 1 m"
                       "[1, 2, 3]"
                   , -- the target applied
                     "let q = [6378000, 0, 0] eci"
                   , encloses
                       "1e-9"
                       "((q to (ecef t0)) .- [0, 0, 0] (ecef t0)) / 1 m"
                       "expm (-(rotz (gmst t0))) @ [6378000, 0, 0]"
                   , -- a point on a chart without parameters needs no from
                     "let r = [1, 2, 3] eci"
                   , "r to eci"
                   ]
            )
          @?= Right ["Point lvlh", "true", "true", "[1, 2, 3] eci"]
        -- The chart a point was written on is never used for a conversion.
        expectError
          (runLinesP (sat ++ ["p to eci"]))
          "lvlh takes arguments: write p from (lvlh …) to eci"
        expectError
          (runLinesP (sat ++ ["p from (ecef t0) to eci"]))
          "charts on lvlh and ecef"
        -- Writing a point needs an applied chart.
        expectError
          (runLinesP (sat ++ ["[1, 2, 3] ecef"]))
          "`ecef` takes arguments: a point is written on an applied chart, as in [1, 2, 3] (ecef t0)"
        -- Inherited: the parent's parameters become the child's.
        lastN 2
          <$> runLinesP
            ( sat
                ++ [ "chart arm q t on (ecef t) at [1, 0, 0] m by roty q"
                   , ":type arm"
                   , encloses
                       "1e-15"
                       "(([0, 0, 0] (arm (30 deg) t0) from (arm (30 deg) t0) to (ecef t0)) .- [0, 0, 0] (ecef t0)) / 1 m"
                       "[1, 0, 0]"
                   ]
            )
          @?= Right ["Num rad -> Point J2000 -> Chart arm", "true"]
    , testCase "F7: the three subtractions" $ do
        let cities =
              earth
                ++ [ "let t0 = 0 J2000"
                   , "let t1 = 0 J2000 .+ 1 s"
                   , "chart lvlhA t on eci at withAxes eci ([7000, 0, 0] km) by rotz (90 deg)"
                   , "let a = [6378000, 0, 0] (ecef t0)"
                   , "let b = [0, 6378000, 0] (ecef t0)"
                   , "let e0 = ecef t0"
                   , "let e1 = ecef t1"
                   , "let la = lvlhA t0"
                   ]
        runLinesP
          ( cities
              ++ [ -- 1. on one frame: relative to the frame, whatever the
                   -- configurations its points were written with
                   "b .- a"
                 , "[0, 6378000, 0] (ecef t1) .- a"
                 , -- 2. across the tree: a point on eci seen from one on ecef
                   encloses "1e-9" "(([0, 0, 0] eci to e0) .- a) / 1 m" "[-6378000, 0, 0]"
                 , -- 3. both in a third frame at one configuration: the
                   -- difference re-expressed
                   encloses
                     "1e-6"
                     "(((b from e0 to la) .- (a from e0 to la)) - ((b .- a) from e0 to la)) / 1 m"
                     "[0, 0, 0]"
                 , -- at two configurations: a new quantity, the frame's motion
                   -- between them included, about ω R δt
                   "let moved = (a from e1 to eci) .- (a from e0 to eci)"
                 , "let dist = mid (norm (mid moved) / 1 m)"
                 , "dist > 400 && dist < 500"
                 ]
          )
          @?= Right
            [ "[-6378000, 6378000, 0] m"
            , "[-6378000, 6378000, 0] m"
            , "true"
            , "true"
            , "true"
            ]
    , testCase
        "F8: any chart after a literal writes a point; one with parameters unapplied is refused"
        $ do
          runLinesP
            ( earth
                ++ [ "let c = degF"
                   , "3 c"
                   , "[1, 2, 3] (ecef (0 J2000))"
                   , multiline
                       ["pt :: forall (c : ITS90). Chart c -> Point c", "let pt c = 3 c"]
                   , "pt degF"
                   , "(\\c -> 3 c) degC"
                   ]
            )
            @?= Right ["3 degF", "[1, 2, 3] (ecef (0 J2000))", "3 degF", "3 degC"]
          expectError
            (runLinesP (earth ++ ["3 ecef"]))
            "`ecef` takes arguments: a point is written on an applied chart"
          runLinesP ["let pt c = 3 c", "pt degC"] @?= Right ["3 degC"]
          -- Written as F8 has it, over every space: a number is the coordinate
          -- of a point on a space of numbers only, so the definition is not as
          -- general as its signature (design §3.10, F8).
          expectError
            (runLinesP [multiline ["pt :: forall c. Chart c -> Point c", "let pt c = 3 c"]])
            "not as general as its signature"
    , testCase "F9: printing and encoding" $ do
        runLinesP
          ( lvlhCharts
              ++ [ ":type 20 degC"
                 , ":type degC"
                 , ":type [1, 2, 3] lvlh"
                 , "20 degC"
                 , "[1, 2, 3] lvlh"
                 ]
          )
          @?= Right ["Point degC", "Chart degC", "Point lvlh", "20 degC", "[1, 2, 3] lvlh"]
    , testCase "F10: a chart's clauses, to as the one conversion, on" $ do
        runLinesP
          [ ":view kelvin"
          , ":view degC"
          , ":view degF"
          , ":view degR"
          , ":view JD"
          , ":view MJD"
          , ":view J2000"
          , ":view unix"
          ]
          @?= Right
            [ "chart kelvin on ITS90"
            , "chart degC on ITS90 at 273.15 K"
            , "chart degF on ITS90 at 459.67 deltaF step deltaF"
            , "chart degR on kelvin step deltaF"
            , "chart JD on TT step day"
            , "chart MJD on TT at 2400000.5 day step day"
            , "chart J2000 on TT at 2451545 day step day"
            , "chart unix on UTC"
            ]
        -- step, by, then and spinning are names outside a chart; on is a keyword.
        runLinesP ["let step = 2", "let spinning = 3", "step + spinning"]
          @?= Right ["5"]
        expectError (runLinesP ["let on = 3"]) "unexpected"
        expectError (runLinesP ["let from = 3"]) "unexpected"
        -- along and inChart are retired into to; withAxes stays.
        expectError
          (runLinesP (lvlhCharts ++ ["inChart lvlh ([1, 0, 0] m)"]))
          "unknown name `inChart`"
        expectError
          (runLinesP (lvlhCharts ++ ["along lvlh ([1, 0, 0] m)"]))
          "unknown name `along`"
        -- on subtracts in a frame, and only a subtraction.
        runLinesP
          ( lvlhCharts
              ++ [ encloses
                     "1e-15"
                     "(([1, 2, 3] eci .- [4, 5, 6] eci on lvlh) - (([1, 2, 3] eci to lvlh) .- ([4, 5, 6] eci to lvlh))) / 1 m"
                     "[0, 0, 0]"
                 , ":type [1, 2, 3] eci .- [4, 5, 6] eci on lvlh"
                 ]
          )
          @?= Right ["true", "Vec lvlh m"]
        expectError
          (runLinesP (lvlhCharts ++ ["[1, 2, 3] eci on lvlh"]))
          "`on` subtracts two points in a frame: write b .- a on c"
    , testCase "F10: conversions and on read back to their hashes" $ do
        let stored =
              lvlhCharts
                ++ [ "let viaOn a b = b .- a on lvlh"
                   , multiline
                       ["fromPt :: Point lvlh -> Point eci", "let fromPt p = p from lvlh to eci"]
                   , multiline
                       [ "fromAmt :: Vec lvlh m -> Vec GCRS m"
                       , "let fromAmt v = v from lvlh to eci"
                       ]
                   , multiline ["toAmt :: Vec GCRS m -> Vec lvlh m", "let toAmt v = v to lvlh"]
                   ]
        forM_ ["viaOn", "fromPt", "fromAmt", "toAmt"] $ \n ->
          expecting (runLinesP (stored ++ [":edit " <> n])) $ \outs ->
            runLinesP (lvlhCharts ++ [multiline outs, ":hash " <> n])
              @?= runLinesP (stored ++ [":hash " <> n])
    , testCase
        "F7: with no type to say so, a frame with parameters is refused when converting"
        $ do
          -- A function over any frame cannot know statically: the conversion
          -- refuses at run time, never reading the chart a point was written on.
          let setup =
                earth
                  ++ [ multiline
                         ["toE :: forall (c : GCRS). Point c -> Point eci", "let toE p = p to eci"]
                     ]
          runLinesP (setup ++ [":type toE", "toE ([1, 2, 3] eci)"])
            @?= Right ["forall (c : GCRS). Point c -> Point eci", "[1, 2, 3] eci"]
          expectError
            (runLinesP (setup ++ ["toE ([1, 2, 3] (ecef (0 J2000)))"]))
            "ecef takes arguments: write p from (ecef …) to c"
    ]
 where
  earth =
    eciChart
      : [ "let ω_e = 7.2921159e-5 rad/s"
        , "let gmst t = 280.46061837 deg + 360.98564736629 deg / day * (t .- 0 J2000)"
        , "chart ecef t on eci by rotz (gmst t) spinning [0, 0, 1] * ω_e"
        ]
