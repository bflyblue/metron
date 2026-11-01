-- | The prelude and the standard library.
module Lang.Library (
  preludeTests,
  stdlibTests,
) where

import Control.Monad (forM_)
import Data.List (sort)
import Data.Map.Strict qualified as Map (
  difference,
  keys,
  lookup,
 )
import Data.Set qualified as Set (difference, fromList, toList)
import Data.Text qualified as T (
  intercalate,
  isInfixOf,
  isPrefixOf,
  isSuffixOf,
  takeWhile,
  unpack,
  unwords,
  words,
 )
import Lang.Common (
  evalP,
  evalU,
  expectError,
  expecting,
  lastN,
  libraryListing,
  librarySize,
  multiline,
  runLinesP,
  seeded,
  sessionP,
  typeOfTextP,
 )
import Metron.Builtin (
  boolDef,
  boolHash,
  consC,
  falseC,
  listDef,
  listHash,
  nilC,
  pairC,
  pairDef,
  pairHash,
  trueC,
 )
import Metron.Codebase (
  Codebase (conNames, fieldNames, names, typeDefs, typeNames),
  lookupConName,
  lookupTypeName,
 )
import Metron.Core (ConRef (UserCon))
import Metron.Driver (
  Session (codebase),
  emptySession,
  feed,
  stdlibUpgrade,
 )
import Metron.NameResolution (
  LabelKind (..),
  Qualified (..),
  qualifyName,
 )
import Metron.Prelude (
  stdlibCodebase,
  stdlibDefaultUses,
  stdlibNames,
 )
import Metron.Syntax qualified as S (lastSegment, rootScope)
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

preludeTests :: TestTree
preludeTests =
  testGroup
    "prelude"
    [ testCase "the prelude loads and defines its names"
        $ length stdlibNames > 600 @? "prelude is unexpectedly small"
    , testCase "derived units are coherent" $ do
        evalP "1 N == 1 kg * m / s^2" @?= Right ["true"]
        evalP "1 J" @?= Right ["1 J"]
        evalP "1 J to kg * m^2 / s^2" @?= Right ["1 kg m^2 s^-2"]
        evalP "1 V * 1 A" @?= Right ["1 V A"]
    , testCase "prefixes" $ do
        evalP "1 km" @?= Right ["1 km"]
        evalP "1 km to m" @?= Right ["1000 m"]
        evalP "1 µm == 1 um" @?= Right ["true"]
        evalP "1 mg" @?= Right ["1 mg"]
        evalP "1 GHz to Hz" @?= Right ["1000000000 Hz"]
    , testCase "accepted units" $ do
        evalP "3 h + 30 min" @?= Right ["210 min"]
        evalP "30 min + 3 h" @?= Right ["210 min"]
        evalP "1 L to m^3" @?= Right ["0.001 m^3"]
        evalU ["astro", "physics"] "1 AU / c to s"
          @?= Right ["499.00478383615641191… s"]
    , testCase "conversions chain from the left, and print back so" $ do
        evalP "1 km to m to km" @?= Right ["1 km"]
        evalP "20 degC to degF to kelvin" @?= Right ["293.15 kelvin"]
        evalP "1.5 h to min to s" @?= Right ["5400 s"]
        runLinesP ["let f x = x to m to km", ":view f", "f (1500 m)"]
          @?= Right ["f = \\x -> x to m to km", "1.5 km"]
    , testCase "constants are exact where SI defines them so"
        $ evalU ["physics"] "c" @?= Right ["299792458 m s^-1"]
    , testCase "the hour is hr, with h an alias; Planck's h needs use physics" $ do
        evalP "3 hr to min" @?= Right ["180 min"]
        evalP "3 h" @?= Right ["3 h"]
        evalP "3 hr" @?= Right ["3 hr"]
        evalP "5 km/h to m/s" @?= Right ["1.3888888888888888888… m s^-1"]
        evalP "5 km/hr to m/s" @?= Right ["1.3888888888888888888… m s^-1"]
        evalP "1 h == 1 hr" @?= Right ["true"]
        expectError
          (runLinesP [":use physics", "3 h"])
          "`h` is both `time.h` and `physics.h`"
        evalU ["physics"] "3 hr" @?= Right ["3 hr"]
        evalU ["physics"] "physics.h" @?= Right ["6.62607015e-34 J s"]
        evalU ["physics"] "physics.h == planck" @?= Right ["true"]
    , testCase "the library by domain: si names, prefixes, time, angle, imperial" $ do
        evalP "1 newton == 1 N" @?= Right ["true"]
        evalP "2 newton" @?= Right ["2 newton"]
        evalP "kilo" @?= Right ["1000"]
        evalP "1 metre + 1 km" @?= Right ["1001 metre"]
        evalP "1 kohm == 1 kΩ" @?= Right ["true"]
        evalP "1 week to day" @?= Right ["7 day"]
        evalP "1 turn to deg" @?= Right ["360 deg"]
        evalP "1 steradian == 1 sr" @?= Right ["true"]
        evalP "0 kelvin to degC" @?= Right ["-273.15 degC"]
        evalU ["imperial"] "1 mile to km" @?= Right ["1.609344 km"]
        evalU ["imperial"] "1 psi to Pa" @?= Right ["6894.7572931683613367… Pa"]
        evalU ["imperial"] "60 mph to km/h" @?= Right ["96.56064 km h^-1"]
        evalU ["physics"] "1 eV to J" @?= Right ["1.602176634e-19 J"]
        evalU ["astro", "physics"] "1 ly to AU" @?= Right ["63241.077084266280268… AU"]
        -- A data type's dimension names a unit through the scope.
        runLinesP ["data F = F (Num N)", ":type F"]
          @?= Right ["Num (kg*m/s^2) -> F"]
    , testCase "cross is the Hodge dual of the wedge" $ do
        runLinesP [":view cross"] @?= Right ["cross = \\a -> \\b -> star (a ∧ b)"]
        evalP "[1, 2, 3] × [4, 5, 6] == star ([1, 2, 3] ∧ [4, 5, 6])" @?= Right ["true"]
        -- Contracting ε's last index first gives b × a, so the arguments swap.
        evalP "(ε @ [0, 1, 0]) @ [1, 0, 0]" @?= Right ["[0, 0, 1]"]
    , testCase "vimap maps with each component's position as a value" $ do
        -- defined over timap and signed, so it stays vector-only (design §3.3)
        case evalP "vimap (\\i x -> x) [1, 2; 3, 4]" of
          Left err -> T.isInfixOf "a vector against a matrix" err @? T.unpack err
          Right v -> assertFailure (show v)
        evalP ":view vimap"
          @?= Right ["vimap = \\f -> \\v -> timap (\\i -> \\x -> f i.0 x) v"]
        evalP "vimap (\\i x -> i * x) [10, 20, 30]" @?= Right ["[0, 20, 60]"]
        runLinesP ["let v = [1, 2, 3] m", "vimap (\\i x -> x) v == v"]
          @?= Right ["true"]
        evalP "vimap (\\i x -> i * x) ([1, 2, 3] m)" @?= Right ["[0, 2, 6] m"]
        -- The position is a value, not a literal (design §2.10).
        case evalP "vimap (\\i x -> x ^ i) [1, 2]" of
          Left err -> T.isInfixOf "expecting - or integer literal" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "let v = [1, 2]\nvimap (\\i x -> v.i) v" of
          Left err -> T.isInfixOf "unknown field `i`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "wedge works in any dimension" $ do
        typeOfTextP "\\a b -> a /\\ b"
          @?= Right "forall n d d1. Vec n d -> Vec n d1 -> Mat n n (d*d1)"
        evalP "[1, 0] ∧ [0, 1]" @?= Right ["[0, 1; -1, 0]"]
    , testCase "an orbital calculation with units end to end"
        $ runLinesP
          [ "let r = [7000, 0, 0] km"
          , "let v = [0, 7.5, 0] km / s"
          , ":type r × v"
          , "(r × v).2"
          ]
          @?= Right ["Vec 3 (m^2/s)", "52500 km^2 s^-1"]
    ]

-- The standard library (design §7.7) -------------------------------------------------

stdlibTests :: TestTree
stdlibTests =
  testGroup
    "standard library"
    [ testCase "a name outside the namespaces used by default needs its namespace" $ do
        let inDefault n = any (\u -> (u <> ".") `T.isPrefixOf` n) stdlibDefaultUses
            defaultLast = Set.fromList (map S.lastSegment (filter inDefault stdlibNames))
            outside =
              Set.toList
                ( Set.fromList (map S.lastSegment (filter (not . inDefault) stdlibNames))
                    `Set.difference` defaultLast
                )
        -- The constants and AU among them (design §7.7).
        all (`elem` outside) ["AU", "G", "c", "planck", "g0"] @? show outside
        forM_ outside $ \n ->
          qualifyName TermLabel S.rootScope seeded.codebase n @?= NotFound
    , testCase "no name is ambiguous among the namespaces used by default" $ do
        let cb = seeded.codebase
            used n = any (\u -> (u <> ".") `T.isPrefixOf` n) stdlibDefaultUses
            check kind labels =
              forM_ (filter used labels) $ \n ->
                qualifyName kind S.rootScope cb (S.lastSegment n) @?= Found n
        check TermLabel (Map.keys cb.names ++ Map.keys cb.conNames)
        check TypeLabel (Map.keys cb.typeNames)
        check FieldLabel (Map.keys cb.fieldNames)
        -- The labels are the ones the source and its aliases declare.
        sort
          ( Map.keys cb.names
              ++ Map.keys cb.conNames
              ++ Map.keys cb.fieldNames
              -- A chart's frame is named as the chart (design §3.10, F3).
              ++ Map.keys (Map.difference (Map.difference cb.typeNames cb.conNames) cb.names)
          )
          @?= sort stdlibNames
    , testCase "a ± definition is stamped with its full path: astro.G is not a root G" $ do
        expecting (runLinesP [":use astro", ":hash G", ":hash astro.G"]) $ \case
          [_, g, astroG] -> g @?= astroG
          outs -> assertFailure (show outs)
        expecting
          ( runLinesP
              [ "let G = (6.67430e-11 ±σ 1.5e-15) * 1 m^3 kg^-1 s^-2"
              , ":add"
              , ":hash G"
              , ":hash astro.G"
              ]
          )
          $ \outs -> case lastN 2 outs of
            [g, astroG] -> (astroG /= g) @? "astro.G differs from the root G"
            other -> assertFailure (show other)
    , testCase "std names Bool, Pair and List, the declarations the compiler holds" $ do
        let cb = seeded.codebase
        lookupTypeName "std.Bool" cb @?= Just boolHash
        lookupTypeName "std.Pair" cb @?= Just pairHash
        lookupTypeName "std.List" cb @?= Just listHash
        Map.lookup boolHash cb.typeDefs @?= Just boolDef
        Map.lookup pairHash cb.typeDefs @?= Just pairDef
        Map.lookup listHash cb.typeDefs @?= Just listDef
        map
          (`lookupConName` cb)
          ["std.False", "std.True", "std.Pair", "std.Nil", "std.Cons"]
          @?= map
            (Just . (\(UserCon t i) -> (t, i)))
            [falseC, trueC, pairC, nilC, consC]
        runLinesP
          [ ":view std.Bool"
          , ":view std.Pair"
          , ":view std.List"
          , "true"
          , "True"
          , "std.False"
          , "Pair 1 2"
          , "Cons 1 (Cons 2 Nil)"
          , "if True then (1, {}) else (2, Cons 3 Nil)"
          , ":type Cons"
          , "case (1, true) of Pair a b -> if b then a else 0"
          ]
          @?= Right
            [ "structural data Bool = False | True"
            , "structural data Pair a b = Pair a b"
            , "structural data List a = Nil | Cons a (List a)"
            , "true"
            , "true"
            , "false"
            , "(1, 2)"
            , "{1, 2}"
            , "(1, {})"
            , "forall a. a -> {a} -> {a}"
            , "1"
            ]
    , testCase "the built-in types print by hash, whatever names them" $ do
        -- Renamed or unnamed, Bool is still Bool, and true still true.
        runLinesP
          [ ":rename std.Bool std.Truth"
          , ":rename std.True std.Yes"
          , "Yes"
          , ":type Yes"
          , ":unname std.List"
          , ":type {1}"
          , "(1, 2, 3, 4)"
          , ":type (1, true, {}, (2, 3))"
          ]
          @?= Right
            [ "renamed `std.Bool` to `std.Truth`"
            , "renamed `std.True` to `std.Yes`"
            , "true"
            , "Bool"
            , "removed the label `std.List`"
            , "{Num}"
            , "(1, 2, 3, 4)"
            , "forall a. (Num, Bool, {a}, (Num, Num))"
            ]
        -- The same declarations entered by a user are the same types.
        let mine =
              [ multiline
                  [ "namespace mine"
                  , "  structural data Bool = False | True"
                  , "  structural data Couple a b = Couple a b"
                  ]
              , ":add"
              ]
        s <- either (assertFailure . T.unpack) pure (sessionP mine)
        lookupTypeName "mine.Bool" s.codebase @?= Just boolHash
        lookupTypeName "mine.Couple" s.codebase @?= Just pairHash
        expecting
          ( runLinesP
              ( mine
                  ++ ["mine.True", "mine.Couple 1 true", "(1, true) == mine.Couple 1 mine.True"]
              )
          )
          $ \outs -> lastN 3 outs @?= ["true", "(1, true)", "true"]
        -- A structural type of Bool's shape is Bool.
        expecting
          (runLinesP ["structural data Color = Red | Green", "Red", ":type Green"])
          $ \outs -> lastN 2 outs @?= ["false", "Bool"]
        expectError (runLinesP ["data Bool = Yes | No"]) "`Bool` is a built-in type"
        expectError
          (evalP ("(" <> T.intercalate ", " (replicate 33 "1") <> ")"))
          "a tuple has at most 32 components"
    , testCase "units resolve through the stored uses and print bare" $ do
        evalP "5 km" @?= Right ["5 km"]
        runLinesP ["5 si.km", "1 km to m", "3 degC", "2 time.h"]
          @?= Right ["5 km", "1000 m", "3 degC", "2 h"]
        runLinesP [":type astro.G"] @?= Right ["Num (m^3/(kg*s^2))"]
        expectError (evalP "G") "unknown name `G`"
        evalU ["astro"] "1 AU to km" @?= Right ["149597870.7 km"]
    , testCase ":ls alone shows the root and a line per namespace; :ls si the SI" $ do
        runLinesP [":ls"] @?= Right libraryListing
        expecting (runLinesP [":ls si"]) $ \outs -> do
          length outs @?= librarySize "si"
          ("unit km : Num m" `elem` outs) @? "km"
          ("unit newton : Num (kg*m/s^2)" `elem` outs) @? "newton"
          ("kilo : Num" `elem` outs) @? "kilo"
        expecting (runLinesP [":ls temperature"]) $ \outs ->
          ("chart degC : Chart degC" `elem` outs) @? "degC"
        -- :ls lists a type and its constructor on two lines and no fields:
        -- linalg.Cov2, astro.State and std.Pair are one label and two lines
        -- each, the three fields of Cov2 and of State none.
        expecting (runLinesP [":ls linalg"]) $ \outs ->
          length outs @?= librarySize "linalg" + 1 - 3
        expecting (runLinesP [":ls --all"]) $ \outs -> do
          ("unit si.km : Num m" `elem` outs) @? "full paths with --all"
          -- six records (Cov2, Pair, and astro's State, Body, Elements and
          -- Transfer) list two lines for one label, and their 21 fields none
          length outs @?= length stdlibNames + 6 - 21
        runLinesP [":ls --units furl"] @?= Right ["nothing matches"]
    , localOption (mkTimeout 10_000_000)
        $ testCase
          ":ls lists a unit with a type that reads back: one of it (design §3.10, U9)"
        $ do
          -- It listed `unit kPa : Unit (kg/(m*s^2))`, and `Unit` is refused
          -- in a written type.
          runLinesP [":ls si.kPa"] @?= Right ["unit kPa : Num (kg/(m*s^2))"]
          runLinesP [multiline ["p :: Num (kg/(m*s^2))", "let p = 1 kPa"], "p"]
            @?= Right ["1 kPa"]
          -- A type query matches what is shown.
          expecting (runLinesP [":ls --units si : Num m"]) $ \outs -> do
            ("unit km : Num m" `elem` outs) @? show outs
            all (" : Num m" `T.isSuffixOf`) outs @? show outs
    , testCase "a root name shadows the library's: c and physics.c" $ do
        runLinesP
          [":use physics", "let c = 3e8 m/s", "c", "physics.c", ":add", "c", "physics.c"]
          @?= Right
            [ "stored use physics"
            , "300000000 m s^-1"
            , "299792458 m s^-1"
            , "added c"
            , "300000000 m s^-1"
            , "299792458 m s^-1"
            ]
        expecting
          ( runLinesP
              [":use physics", "let c = 3e8 m/s", "let x = c + physics.c", ":add", ":view x"]
          )
          $ \outs ->
            last outs @?= "x = c + physics.c"
    , testCase "library names are names: :rename, :unname, :edit" $ do
        runLinesP [":rename time.hr time.hour", "3 hour", "2 hour + 30 min", "3 h"]
          @?= Right ["renamed `time.hr` to `time.hour`", "3 hour", "150 min", "3 h"]
        expectError
          (runLinesP [":rename time.hr time.hour", "3 hr"])
          "unknown name `hr`"
        expectError
          (runLinesP [":use astro", ":unname astro.AU", "1 AU"])
          "unknown name `AU`"
        runLinesP [":edit si.km"]
          @?= Right ["namespace si", "  unit km = kilo * 1 metre"]
    , testCase ":uses, :unuse and :use for the stored uses" $ do
        let stored = ["use " <> u <> " (stored)" | u <- stdlibDefaultUses]
            withoutSi = ["use " <> u <> " (stored)" | u <- stdlibDefaultUses, u /= "si"]
        runLinesP [":uses"] @?= Right stored
        runLinesP [":unuse si", ":uses"]
          @?= Right ("removed the stored use si; :use si puts it back" : withoutSi)
        expectError (runLinesP [":unuse si", "5 km"]) "unknown name `km`"
        runLinesP [":unuse si", "5 si.km", ":use si", "5 km", ":uses"]
          @?= Right
            ( [ "removed the stored use si; :use si puts it back"
              , "5 si.km"
              , "stored use si"
              , "5 km"
              ]
                ++ withoutSi
                ++ ["use si (stored)"]
            )
        expectError (runLinesP [":use si"]) "use si is already stored"
        -- A session use and a stored one of the same path: the stored goes first.
        runLinesP ["use si", ":uses", ":unuse si", ":uses", ":unuse si", ":uses"]
          @?= Right
            ( stored
                ++ ["use si", "removed the stored use si; :use si puts it back"]
                ++ withoutSi
                ++ ["use si"]
                ++ withoutSi
            )
        -- The scratch must still check without it.
        expectError
          (runLinesP ["let d = 2 km", ":unuse si"])
          "the pending definitions would not check"
        -- × is the library's cross, so it needs linalg.
        evalP "[1, 0, 0] × [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        expectError (runLinesP [":unuse linalg", "[1, 0, 0] × [0, 1, 0]"]) "cross"
    , testCase ":stdlib upgrade: up to date, added, updated, kept" $ do
        runLinesP [":stdlib upgrade"] @?= Right ["the library is up to date"]
        lib <- either (assertFailure . T.unpack) pure stdlibCodebase
        -- An older library: G as a plain number, c the user rebinds, AU absent.
        old <-
          either
            (assertFailure . T.unpack)
            pure
            ( sessionWith
                emptySession
                [ multiline ["namespace astro", "  let G = 1", "  let gone = 3"]
                , multiline ["namespace physics", "  let c = 2"]
                , ":add"
                , multiline ["namespace physics", "  let c = 5"]
                , "let twice = astro.G * 2"
                , ":update"
                ]
            )
        case stdlibUpgrade lib old of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added si.km" `elem` outs) @? "km added"
            ("added astro.AU" `elem` outs) @? "AU added"
            any ("updated astro.G " `T.isPrefixOf`) outs @? "G updated"
            ("kept physics.c (yours)" `elem` outs) @? "c kept"
            any ("upgraded twice " `T.isPrefixOf`) outs @? "twice upgraded"
            linesIn' s ["physics.c", "astro.gone", "twice", "1 si.km"]
              @?= Right ["5", "3", "1.33486e-10 ±σ 3e-15 m^3 kg^-1 s^-2", "1 si.km"]
            -- A library type comes with its constructor and field labels.
            ("added data linalg.Cov2" `elem` outs) @? "Cov2 added"
            ("added linalg.jointCovariance" `elem` outs) @? "jointCovariance added"
            -- An alias is a label like any other: added as a unit.
            ("added si.newton" `elem` outs) @? "newton added"
            linesIn'
              s
              -- A field is found through a use, as a bare name is.
              [ ":use linalg"
              , ":use si"
              , "(jointCovariance ([1, 2] m ±σ 1 m, [3, 4] m ±σ 1 m)).rv"
              , "2 newton"
              ]
              @?= Right ["stored use linalg", "stored use si", "[0, 0; 0, 0] m^2", "2 newton"]
        -- A type label the codebase has is left alone.
        old2 <-
          either
            (assertFailure . T.unpack)
            pure
            ( sessionWith
                emptySession
                [multiline ["namespace linalg", "  data Cov2 = Cov2"], ":add"]
            )
        case stdlibUpgrade lib old2 of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added data linalg.Cov2" `notElem` outs) @? "Cov2 kept"
            lookupTypeName "linalg.Cov2" s.codebase
              @?= lookupTypeName "linalg.Cov2" old2.codebase
    , testCase
        ":rename and :move re-hash a stamped definition and upgrade its dependents"
        $ do
          let hashOf ls n = fmap last (runLinesP (ls ++ [":hash " <> n]))
          -- A plain definition keeps its hash; a ± one takes its new path's.
          expecting (runLinesP ["let q = 1", ":add", ":rename q r"]) $ \outs ->
            last outs @?= "renamed `q` to `r`"
          expecting
            ( runLinesP
                ["let a = 1 ± 0.1", "let b = a * 2", ":add", ":rename a c", "b", ":todo"]
            )
            $ \outs -> do
              case drop 2 outs of
                renamed : rehashed : upgraded : rest -> do
                  renamed @?= "renamed `a` to `c`"
                  ("re-hashed c #" `T.isPrefixOf` rehashed) @? T.unpack rehashed
                  ("upgraded b #" `T.isPrefixOf` upgraded) @? T.unpack upgraded
                  rest @?= ["2.0 ± 0.2", "nothing to do"]
                other -> assertFailure (show other)
          hashOf ["let a = 1 ± 0.1", ":add", ":rename a c"] "c"
            @?= hashOf ["let c = 1 ± 0.1", ":add"] "c"
          -- A namespace moved: each stamped member re-hashed, as if entered there.
          let lab = [multiline ["namespace lab", "  let x = 1 ± 0.1", "  let y = x + 1"], ":add"]
          expecting (runLinesP (lab ++ [":rename lab field"])) $ \outs ->
            map (T.takeWhile (/= '#')) (lastN 3 outs)
              @?= [ "renamed the 2 labels under `lab` to `field`"
                  , "re-hashed field.x "
                  , "re-hashed field.y "
                  ]
          hashOf (lab ++ [":move lab.x field"]) "field.x"
            @?= hashOf [multiline ["namespace field", "  let x = 1 ± 0.1"], ":add"] "field.x"
          -- The library's G: its dependents follow it.
          expecting
            ( runLinesP
                [ "use astro"
                , "let mEarth = iau2015.earth.mu / G"
                , ":add"
                , ":rename astro.G astro.Gn"
                , ":todo"
                ]
            )
            $ \outs ->
              map (T.unwords . take 2 . T.words) (drop 1 outs)
                @?= [ "renamed `astro.G`"
                    , "re-hashed Gn"
                    , "upgraded mEarth"
                    , "nothing to"
                    ]
    , testCase
        ":rename of a nominal type re-hashes it, its users and the types that use it"
        $ do
          let shapes =
                [ "data Shape = Circle (Num m) | Square (Num m)"
                , "data Wrap = Wrap Shape"
                , "let size s = case s of Circle r -> r; Square a -> a"
                , "let one = Wrap (Circle (1 m))"
                , ":add"
                ]
          expecting
            ( runLinesP
                ( shapes
                    ++ [":rename Shape Form", "size (Square (2 m))", "one", ":view Wrap", ":todo"]
                )
            )
            $ \outs -> do
              let report = takeWhile (/= "2 m") (dropWhile (not . ("renamed" `T.isPrefixOf`)) outs)
              take 1 report @?= ["renamed `Shape` to `Form`"]
              sort (map (T.unwords . take 2 . T.words) (drop 1 report))
                @?= ["re-hashed data", "re-hashed data", "upgraded one", "upgraded size"]
              lastN 3 outs
                @?= ["Wrap (Circle (1 m))", "data Wrap = Wrap Form", "nothing to do"]
          -- The type now has the hash a fresh declaration under the new name has.
          let typeHash ls n = do
                s <- sessionP ls
                pure (lookupTypeName n s.codebase)
          typeHash (shapes ++ [":rename Shape Form"]) "Form"
            @?= typeHash ["data Form = Circle (Num m) | Square (Num m)", ":add"] "Form"
    ]
 where
  linesIn' s0 = go s0 []
   where
    go _ acc [] = Right (concat (reverse acc))
    go s acc (l : rest) = do
      (s', outs) <- feed s l
      go s' (outs : acc) rest
  sessionWith s0 = \case
    [] -> Right s0
    l : ls -> feed s0 l >>= \(s', _) -> sessionWith s' ls
