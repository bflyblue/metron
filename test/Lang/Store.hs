-- | The store on disk and editing.
module Lang.Store (
  storeTests,
  editTests,
) where

import Control.Monad (forM_)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (readFile, writeFile)
import Data.List (sort)
import Data.Map.Strict qualified as Map (
  Map,
  adjust,
  filterWithKey,
  findWithDefault,
  keys,
  keysSet,
  lookup,
  member,
  singleton,
  size,
  unions,
 )
import Data.Maybe (isJust)
import Data.Set qualified as Set (
  difference,
  fromList,
  intersection,
  isSubsetOf,
  member,
  null,
  size,
  union,
 )
import Data.Text (Text)
import Data.Text qualified as T (
  dropWhile,
  isInfixOf,
  isPrefixOf,
  isSuffixOf,
  lines,
  pack,
  replace,
  strip,
  takeWhile,
  unlines,
  unpack,
 )
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Text.IO qualified as TIO (readFile, writeFile)
import Gen (genProgram)
import Lang.Common (
  astroTypes,
  builtinTypeListing,
  editFileOf,
  editScript,
  editSession,
  edited,
  expectError,
  linesIn,
  persistLines,
  reload,
  replaceOnce,
  runLinesP,
  seeded,
  sessionP,
  theSeed,
  timedForAll,
  withTempStore,
 )
import Metron.Codebase (
  Codebase (
    charts,
    conNames,
    fieldNames,
    history,
    names,
    preferences,
    terms,
    typeDefs,
    typeNames,
    units,
    uses
  ),
  lookupName,
  lookupTypeName,
  showReference,
 )
import Metron.Core (alphaEq)
import Metron.Desugar (desugarClosed, noResolver)
import Metron.Driver (
  EditRequest (EditOpen, EditResume),
  EditScope (EditCodebase, EditName, EditNamespace),
  Session (codebase, scratch),
  applyEdit,
  editRequest,
  editScopeArgs,
  editorNote,
  exportSource,
  feed,
 )
import Metron.Hash (decodeStored, encodeStored, hashTerm)
import Metron.Prelude (stdlibDefaultUses)
import Metron.Store (
  MergeReport (..),
  formatVersion,
  mergeStores,
  openStore,
 )
import Metron.Syntax qualified as S (Use (Use))
import System.Directory (
  createDirectoryIfMissing,
  doesDirectoryExist,
  doesFileExist,
  getTemporaryDirectory,
  listDirectory,
  removePathForcibly,
 )
import System.FilePath ((</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (
  Assertion,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )
import Test.Tasty.QuickCheck (
  counterexample,
  discard,
  testProperty,
 )

-- Persistence -----------------------------------------------------------------------
--
-- Design §7.4: terms by hash in the storage encoding, labels as a replayed
-- log, the prelude underneath and never stored as bindings.

storeTests :: TestTree
storeTests =
  testGroup
    "store"
    [ testProperty
        "the storage encoding round-trips every generated program, hints included"
        $ timedForAll (snd <$> genProgram)
        $ \e -> case desugarClosed noResolver e of
          Left _ -> discard
          Right (t, _) -> case decodeStored (encodeStored t) of
            Left err -> counterexample (T.unpack err) False
            Right t' ->
              counterexample
                (show t')
                (alphaEq t t' && encodeStored t' == encodeStored t && hashTerm t' == hashTerm t)
    , testCase "a chart's parent and generator survive a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ "space GCRS = Vec 3 m"
            , "chart eci on GCRS"
            , "chart site on eci at [6378, 0, 0] km"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.names @?= s.codebase.names
        loaded.codebase.charts @?= s.codebase.charts
        loaded.codebase.typeNames @?= s.codebase.typeNames
        linesIn
          loaded
          [ "[1, 2, 3] antenna to eci"
          , ":view antenna"
          , ":view lvlh"
          , ":type [1, 2, 3] lvlh"
          ]
          @?= Right
            [ "[6378003, 2, 4] eci"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
            , "Point lvlh"
            ]
    , testCase "definitions, history, units, labels and cycles survive a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ "let speed = 5 km / h"
            , ":prefer kPa"
            , "unit furlong = 201.168 m"
            , "let r = 10 mm ± 0.01 mm #batch7"
            , "let even n = if n == 0 then true else odd (n - 1); let odd n = if n == 0 then false else even (n - 1)"
            , "unit mmHg = 133.322 Pa"
            , "space ISA = Num Pa"
            , "chart bp on ISA step mmHg"
            , ":add"
            , "let speed = 6 km / h"
            , ":update"
            , ":alias v speed"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        Map.keys loaded.codebase.names @?= Map.keys s.codebase.names
        loaded.codebase.names @?= s.codebase.names
        loaded.codebase.history @?= s.codebase.history
        loaded.codebase.units @?= s.codebase.units
        loaded.codebase.charts @?= s.codebase.charts
        loaded.codebase.preferences @?= s.codebase.preferences
        Map.keysSet s.codebase.terms `Set.isSubsetOf` Map.keysSet loaded.codebase.terms
          @? "every term came back"
        linesIn
          loaded
          [ "speed"
          , "v"
          , ":history speed"
          , "1 furlong to m"
          , "r - r"
          , "even 10"
          , "odd 10"
          , ":view r"
          , "101325 Pa"
          ]
          @?= Right
            [ "6 km h^-1"
            , "6 km h^-1"
            , -- These changed when km became kilo * metre and h an alias of hr,
              -- and when km was respelled kilo * 1 metre (design §3.10, U3), and
              -- again when units became a type: speed is the quantity 5 (km/h),
              -- scale of a unit quotient, and km and h are units by declaration.
              "#av4qv  (current)"
            , "#01d73"
            , "201.168 m"
            , "0 mm"
            , "true"
            , "false"
            , "r = 10 mm ± 0.01 mm #batch7"
            , "101.325 kPa"
            ]
    , testCase
        "a new store is seeded with the library; a reload is the library and the user's, from disk"
        $ withTempStore
        $ \dir -> do
          s <- persistLines dir ["let d = 3 km", ":add"]
          -- The library's terms are on disk, with the user's one beside them.
          onDisk <- listDirectory (dir </> "terms")
          length onDisk @?= Map.size seeded.codebase.terms + 1
          -- Loaded on top of the empty codebase: no prelude step.
          (loaded, notes) <- reload dir
          notes @?= []
          Map.size loaded.codebase.terms @?= Map.size seeded.codebase.terms + 1
          loaded.codebase.names @?= s.codebase.names
          loaded.codebase.history @?= s.codebase.history
          loaded.codebase.units @?= s.codebase.units
          loaded.codebase.charts @?= s.codebase.charts
          loaded.codebase.uses @?= [S.Use u Nothing | u <- stdlibDefaultUses]
          linesIn loaded ["d", "astro.G"]
            @?= Right ["3 km", "6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
          -- The seed is at time 0, before the user's lines.
          ls <- T.lines <$> TIO.readFile (dir </> "names.log")
          all (\u -> ("0 use " <> u) `elem` ls) stdlibDefaultUses
            @? "the stored uses are log lines"
          all ("0 " `T.isPrefixOf`) (takeWhile ("0 " `T.isPrefixOf`) ls) @? "seed first"
          length (filter (not . ("0 " `T.isPrefixOf`)) ls) @?= 1
    , testCase "a seeded store keeps the library's record type across a reload"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir []
          (loaded, notes) <- reload dir
          notes @?= []
          linesIn
            loaded
            [ "let p = jointCovariance ([1, 2] m ±σ 1 m, [3, 4] s ±σ 1 s)"
            , "p.rr"
            , "p.rv"
            , "p {rv = p.rv}"
            , ":covariance ([1, 2] m ±σ 1 m, [3, 4] s ±σ 1 s)"
            , ":ls --types"
            ]
            @?= withBuiltinTypes
              ( [ "[1, 0; 0, 1] m^2"
                , "[0, 0; 0, 0] m s"
                , "Cov2 {rr = [1, 0; 0, 1] m^2, rv = [0, 0; 0, 0] m s, vv = [1, 0; 0, 1] s^2}"
                , "rr [1, 0; 0, 1] m^2"
                , "rv [0, 0; 0, 0] m s"
                , "vv [1, 0; 0, 1] s^2"
                , "bound box ([0, 0] m, [0, 0] s)"
                ]
                  ++ astroTypes
                  ++ [ "data Cov2 n d d1 = Cov2 {rr :: Mat n n (d^2), rv :: Mat n n (d*d1), vv :: Mat n n (d1^2)}"
                     , "Cov2 : forall n d d1. Mat n n (d^2) -> Mat n n (d*d1) -> Mat n n (d1^2) -> Cov2 n d d1"
                     ]
              )
    , testCase
        "a root binding shadows the library's on reload; :use and :unuse persist"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir ["let c = 3e8 m / s", ":add", ":use physics", ":unuse si"]
          (loaded, _) <- reload dir
          loaded.codebase.uses
            @?= [S.Use u Nothing | u <- filter (/= "si") stdlibDefaultUses ++ ["physics"]]
          linesIn loaded ["c", "physics.c", "1 si.km", ":use si", "1 km"]
            @?= Right
              ["300000000 m s^-1", "299792458 m s^-1", "1 si.km", "stored use si", "1 km"]
          ls <- T.lines <$> TIO.readFile (dir </> "names.log")
          any (" unuse si" `T.isSuffixOf`) ls @? "an unuse line"
    , testCase "merging two seeded stores brings nothing across for the library"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              b = root </> "b"
          _ <- persistLines a ["let x = 1", ":add"]
          _ <- persistLines b []
          r <- mergeInto a b
          r @?= MergeReport 0 0 0 []
          _ <- persistLines b ["let y = 2", ":add"]
          r' <- mergeInto a b
          (r'.termsCopied, r'.linesAdded) @?= (1, 1)
    , testCase
        "declared types, their names and a type that uses another survive a reload"
        $ withTempStore
        $ \dir -> do
          s <-
            persistLines
              dir
              [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
              , "data Wrap a = Wrap {shape :: Shape, extra :: a}"
              , "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"
              , ":add"
              , ":unname Circle"
              ]
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.typeDefs @?= s.codebase.typeDefs
          loaded.codebase.typeNames @?= s.codebase.typeNames
          loaded.codebase.conNames @?= s.codebase.conNames
          Map.member "Circle" loaded.codebase.conNames @?= False
          loaded.codebase.fieldNames @?= s.codebase.fieldNames
          linesIn
            loaded
            ["area (Rect (2 m) (3 m))", "(Wrap (Rect (1 m) (1 m)) 2).shape", ":view Wrap"]
            @?= Right
              ["6 m^2", "Rect (1 m) (1 m)", "data Wrap a = Wrap {shape :: Shape, extra :: a}"]
    , testCase "namespaced labels survive a reload with their paths, renamed or not" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ T.unlines
                [ "namespace orbital"
                , "  unit au = 149597870700 m"
                , "  space Distance = Num m"
                , "  chart tip on Distance step au"
                , "  data Body = Body {mass :: Num kg, dist :: Num m}"
                , "  let mu = 3"
                , "  namespace kepler"
                , "    let anomaly e x = x + e * x"
                ]
            , ":add"
            , ":rename orbital.kepler celestial.kepler"
            , ":rename orbital mechanics"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.names @?= s.codebase.names
        -- A chart re-hashes when it moves, its frame stamped with its path
        -- (design §3.10); the log keeps its new version, not the step between.
        let settled = Map.adjust (take 1) "mechanics.tip"
        settled loaded.codebase.history @?= settled s.codebase.history
        loaded.codebase.units @?= s.codebase.units
        loaded.codebase.charts @?= s.codebase.charts
        loaded.codebase.typeNames @?= s.codebase.typeNames
        loaded.codebase.conNames @?= s.codebase.conNames
        loaded.codebase.fieldNames @?= s.codebase.fieldNames
        Map.member "celestial.kepler.anomaly" loaded.codebase.names @? "renamed"
        Map.member "mechanics.mass" loaded.codebase.fieldNames @? "field path"
        Set.member "mechanics.au" loaded.codebase.units @? "unit path"
        Set.member "mechanics.tip" loaded.codebase.charts @? "chart path"
        Map.member "mechanics.Body" loaded.codebase.typeNames @? "type path"
        Map.member "mechanics.Body" loaded.codebase.conNames @? "constructor path"
        Map.member "orbital.mu" loaded.codebase.history @? "history keeps the old path"
        null [n | n <- Map.keys loaded.codebase.names, "orbital." `T.isPrefixOf` n]
          @? "nothing left under orbital"
    , testCase "a let that takes over a unit name stays a quantity after a reload" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["unit dozen = 12", ":add", "let dozen = 13", ":update"]
        (loaded, _) <- reload dir
        Set.member "dozen" loaded.codebase.units @?= False
        linesIn loaded ["dozen * 3", "dozen + 1"] @?= Right ["39", "14"]
        -- and it is no longer a unit the quantity rule accepts
        case linesIn loaded ["3 dozen"] of
          Left err -> T.isInfixOf "`dozen` is a Num, not a unit or a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a type indexed by rank survives a reload" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["data Idx s = Idx (Vec (rank s))", ":add"]
        (loaded, notes) <- reload dir
        notes @?= []
        linesIn loaded [":view Idx", ":type Idx [0, 1, 2]"]
          @?= Right ["data Idx s = Idx (Vec (rank s))", "forall n m k. Idx [n, m, k]"]
    , testCase ":unname persists" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let x = 1", ":add", ":alias y x", ":unname y"]
        (loaded, _) <- reload dir
        Map.member "y" loaded.codebase.names @?= False
        Map.member "x" loaded.codebase.names @?= True
    , testCase "a corrupt term file and a dangling name are reported, the rest loads" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let x = 7", "let y = 11", ":add"]
        writeFile (dir </> "terms" </> "not-a-hash") "junk"
        appendFile
          (dir </> "names.log")
          "1 bind z 0000000000000000000000000000000000000000000000000000000000000000\n"
        (loaded, notes) <- reload dir
        length notes @?= 2
        linesIn loaded ["x + y"] @?= Right ["18"]
    , testCase "a store of another format is refused with one line and left as it is"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir ["let x = 1", ":add"]
          writeFile (dir </> "format") "metron codebase 10\n"
          before <- snapshot dir
          entries <- sort <$> listDirectory dir
          opened <- openStore theSeed dir
          case opened of
            Left err ->
              err
                @?= T.pack dir <> ": this codebase is format 10; this metron opens format 12"
            Right _ -> assertFailure "opened a store of another format"
          snapshot dir >>= (@?= before)
          listDirectory dir >>= (@?= entries) . sort
    , testCase "a store of the current format opens as it was seeded" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let x = 1", ":add"]
        readFile (dir </> "format")
          >>= (@?= "metron codebase " <> show formatVersion <> "\n")
        formatVersion @?= 12
        before <- snapshot dir
        (loaded, notes) <- reload dir
        notes @?= []
        -- Opening it writes nothing: it is not seeded again.
        snapshot dir >>= (@?= before)
        loaded.codebase.uses @?= [S.Use u Nothing | u <- stdlibDefaultUses]
        linesIn loaded ["x", "1 km"] @?= Right ["1", "1 km"]
    , testCase "merging two stores: both sides' definitions, one file per shared term"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              b = root </> "b"
          _ <- persistLines a ["let x = 7", "let shared = 42", ":add"]
          _ <- persistLines b ["let y = 11", "let shared = 42", ":add"]
          termsA <- Set.fromList <$> listDirectory (a </> "terms")
          termsB <- Set.fromList <$> listDirectory (b </> "terms")
          not (Set.null (Set.intersection termsA termsB)) @? "the stores share a term"
          r <- mergeInto a b
          r.termsCopied @?= Set.size (Set.difference termsB termsA)
          r.notes @?= []
          termsA' <- Set.fromList <$> listDirectory (a </> "terms")
          termsA' @?= Set.union termsA termsB
          (loaded, notes) <- reload a
          notes @?= []
          linesIn loaded ["x + y", "shared"] @?= Right ["18", "42"]
    , testCase
        "merging: a name bound on both sides takes the later definition, whichever side it is on"
        $ withTempStore
        $ \root -> do
          let store name def t = do
                let d = root </> name
                _ <- persistLines d ["let x = " <> def, ":add"]
                restamp d t
                pure d
              xAfterMerge target source = do
                _ <- mergeInto target source
                (loaded, _) <- reload target
                pure (linesIn loaded ["x"])
          -- the source's line is later
          a1 <- store "a1" "1" 100
          b1 <- store "b1" "2" 200
          xAfterMerge a1 b1 >>= (@?= Right ["2"])
          -- the target's line is later: appending alone would get this wrong
          a2 <- store "a2" "1" 200
          b2 <- store "b2" "2" 100
          xAfterMerge a2 b2 >>= (@?= Right ["1"])
          ls <- T.lines <$> TIO.readFile (a2 </> "names.log")
          -- The library's seed lines are at time 0 in both, and come first.
          filter (/= "0") (map (T.takeWhile (/= ' ')) ls) @?= ["100", "200"]
          takeWhile (== "0") (map (T.takeWhile (/= ' ')) ls)
            @?= filter (== "0") (map (T.takeWhile (/= ' ')) ls)
    , testCase
        "merging: declared types and their type, con and field labels come across"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              b = root </> "b"
          _ <- persistLines a ["let x = 1", ":add"]
          s <-
            persistLines
              b
              [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
              , "data Body = Body {mass :: Num kg}"
              , ":add"
              ]
          r <- mergeInto a b
          r.typesCopied @?= 2
          (loaded, notes) <- reload a
          notes @?= []
          loaded.codebase.typeDefs @?= s.codebase.typeDefs
          loaded.codebase.typeNames @?= s.codebase.typeNames
          loaded.codebase.conNames @?= s.codebase.conNames
          loaded.codebase.fieldNames @?= s.codebase.fieldNames
          linesIn loaded ["x", "(Body (2 kg)).mass", ":view Shape"]
            @?= Right
              ["1", "2 kg", "data Shape = Circle (Num m) | Rect (Num m) (Num m)"]
    , testCase
        "merging again adds nothing; the other store and both history files are left alone"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              b = root </> "b"
          _ <- persistLines a ["let x = 1", ":add"]
          _ <- persistLines b ["let y = 2", "data Tag = Tag Num", ":add", ":alias z y"]
          writeFile (a </> "history") "x\n"
          writeFile (b </> "history") "y\n"
          before <- snapshot b
          r1 <- mergeInto a b
          (r1.termsCopied > 0 && r1.typesCopied == 1 && r1.linesAdded > 0) @? show r1
          logAfterFirst <- TIO.readFile (a </> "names.log")
          r2 <- mergeInto a b
          r2 @?= MergeReport 0 0 0 []
          TIO.readFile (a </> "names.log") >>= (@?= logAfterFirst)
          snapshot b >>= (@?= before)
          readFile (a </> "history") >>= (@?= "x\n")
          (loaded, _) <- reload a
          linesIn loaded ["x + z", "Tag 3"] @?= Right ["3", "Tag 3"]
    , testCase
        "merging: corrupt files are not copied, a line without a time is reported"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              b = root </> "b"
          _ <- persistLines a ["let x = 1", ":add"]
          _ <- persistLines b ["let y = 2", ":add"]
          writeFile (b </> "terms" </> "not-a-hash") "junk"
          writeFile (b </> "terms" </> replicate 64 '0') "junk"
          appendFile (b </> "names.log") "garbage line\n"
          r <- mergeInto a b
          length r.notes @?= 3
          r.linesAdded @?= 2
          doesFileExist (a </> "terms" </> "not-a-hash") >>= (@?= False)
          doesFileExist (a </> "terms" </> replicate 64 '0') >>= (@?= False)
          ls <- T.lines <$> TIO.readFile (a </> "names.log")
          -- Sorted as if at time 0: after the seed's lines, before the user's.
          take 1 (dropWhile ("0 " `T.isPrefixOf`) ls) @?= ["garbage line"]
          (loaded, _) <- reload a
          linesIn loaded ["x + y"] @?= Right ["3"]
    , testCase
        "merging from what is not a store, or from a store of another format, is refused and touches nothing"
        $ withTempStore
        $ \root -> do
          let a = root </> "a"
              plain = root </> "plain"
              refused src needle = do
                r <- mergeStores theSeed a src
                case r of
                  Left err -> T.isInfixOf needle err @? T.unpack err
                  Right v -> assertFailure (show v)
                doesDirectoryExist a >>= (@?= False)
          createDirectoryIfMissing True plain
          writeFile (plain </> "notes.txt") "hello"
          refused plain "is not a metron codebase"
          listDirectory plain >>= (@?= ["notes.txt"])
          refused (root </> "missing") "no such directory"
          doesDirectoryExist (root </> "missing") >>= (@?= False)
          _ <- persistLines (root </> "future") ["let x = 1", ":add"]
          writeFile (root </> "future" </> "format") "metron codebase 99\n"
          refused
            (root </> "future")
            "this codebase is format 99; this metron opens format 12"
          readFile (root </> "future" </> "format") >>= (@?= "metron codebase 99\n")
    ]
 where
  mergeInto :: FilePath -> FilePath -> IO MergeReport
  mergeInto target source = either (error . T.unpack) id <$> mergeStores theSeed target source
  -- Every line of a store's log at one time, for deterministic merges; the
  -- library's seed lines stay at time 0.
  restamp :: FilePath -> Integer -> IO ()
  restamp d t = do
    ls <- T.lines <$> TIO.readFile (d </> "names.log")
    TIO.writeFile
      (d </> "names.log")
      ( T.unlines
          [ if "0 " `T.isPrefixOf` l then l else T.pack (show t) <> T.dropWhile (/= ' ') l
          | l <- ls
          ]
      )
  -- Every file under a directory with its content.
  snapshot :: FilePath -> IO (Map.Map FilePath ByteString)
  snapshot d = do
    entries <- listDirectory d
    Map.unions
      <$> mapM
        ( \e -> do
            let p = d </> e
            isDir <- doesDirectoryExist p
            if isDir then snapshot p else Map.singleton p <$> BS.readFile p
        )
        entries

-- | The labels and history of two codebases are the same.
sameLabels :: Codebase -> Codebase -> Assertion
sameLabels a b = do
  a.names @?= b.names
  a.history @?= b.history
  a.typeNames @?= b.typeNames
  a.conNames @?= b.conNames
  a.fieldNames @?= b.fieldNames
  a.units @?= b.units
  a.charts @?= b.charts

-- | @updated n #old -> #new@ and its kin, from the two sessions.
movedLine :: Text -> Session -> Session -> Text -> Text
movedLine verb s s' n =
  verb
    <> " "
    <> n
    <> " "
    <> maybe "?" showReference (lookupName n s.codebase)
    <> " -> "
    <> maybe "?" showReference (lookupName n s'.codebase)

editTests :: TestTree
editTests =
  testGroup
    ":edit, the editor round trip"
    [ testCase "the file: a header that says what saving does, then the export" $ do
        s <- editSession
        file <- editFileOf s []
        export <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        (export `T.isSuffixOf` T.strip file) @? T.unpack file
        ("-- :edit: the codebase" `T.isPrefixOf` file) @? T.unpack file
        ("removed" `T.isInfixOf` file) @? "the header names removal"
        ("Deleting everything is refused" `T.isInfixOf` file)
          @? "the header names the refusal"
        ("does not change" `T.isInfixOf` file) @? "the header names the namespace rule"
        -- A namespace exports its own labels; one name, its cycle with it.
        ns <- editFileOf s ["orbital"]
        nsExport <-
          either (assertFailure . T.unpack) pure (exportSource s (Just "orbital"))
        (nsExport `T.isSuffixOf` T.strip ns) @? T.unpack ns
        one <- editFileOf s ["orbital.even"]
        ("let odd" `T.isInfixOf` one) @? T.unpack one
        ("nothing is removed" `T.isInfixOf` one) @? T.unpack one
        ("let x" `T.isInfixOf` one) @?= False
    , testCase "(a) an unchanged file changes nothing" $ do
        s <- editSession
        forM_
          [ ([], EditCodebase)
          , (["orbital"], EditNamespace "orbital")
          , (["std"], EditNamespace "std")
          , (["orbital.Body"], EditName "orbital.Body")
          ]
          $ \(args, target) -> do
            file <- editFileOf s args
            (s', outs) <- edited target file s
            outs @?= ["nothing changed"]
            sameLabels s.codebase s'.codebase
    , testCase "(b) a changed body is updated and its dependents upgraded" $ do
        s <- editSession
        file <- editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = 4\n"
        (s', outs) <- edited EditCodebase file s
        outs
          @?= [ movedLine "updated" s s' "orbital.x"
              , movedLine "upgraded" s s' "orbital.y"
              , movedLine "upgraded" s s' "mechanics.useY"
              ]
        snd <$> feed s' "mechanics.useY" @?= Right ["50"]
        -- History keeps the old version.
        length (Map.findWithDefault [] "orbital.x" s'.codebase.history) @?= 2
        -- From a namespace, a dependent outside it is upgraded by propagation.
        nsFile <-
          editFileOf s ["orbital"] >>= replaceOnce "  let x = 3\n" "  let x = 5\n"
        (s'', nsOuts) <- edited (EditNamespace "orbital") nsFile s
        nsOuts
          @?= [ movedLine "updated" s s'' "orbital.x"
              , movedLine "upgraded" s s'' "orbital.y"
              , movedLine "upgraded" s s'' "mechanics.useY"
              ]
        snd <$> feed s'' "mechanics.useY" @?= Right ["60"]
    , testCase "(c) a definition deleted from the file is removed; history keeps it" $ do
        s <- editSession
        file <- editFileOf s [] >>= replaceOnce "  let fall = \\t -> g0 * t^2 / 2\n" ""
        (s', outs) <- edited EditCodebase file s
        outs @?= ["removed mechanics.fall"]
        lookupName "mechanics.fall" s'.codebase @?= Nothing
        Map.member "mechanics.fall" s'.codebase.history @? "history keeps it"
        -- A dependent of what was removed is left stale, and says so.
        file2 <- editFileOf s [] >>= replaceOnce "  let y = x + 1\n" ""
        (s2, outs2) <- edited EditCodebase file2 s
        case outs2 of
          [removed, left] -> do
            removed @?= "removed orbital.y"
            ("left mechanics.useY stale: it uses orbital.y#" `T.isPrefixOf` left)
              @? T.unpack left
            ("which was removed" `T.isSuffixOf` left) @? T.unpack left
          other -> assertFailure (show other)
        snd <$> feed s2 "mechanics.useY" @?= Right ["40"]
    , testCase "(d) a definition added inside a block is added there" $ do
        s <- editSession
        file <-
          editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = 3\n  let z = x * 7\n"
        (s', outs) <- edited EditCodebase file s
        outs @?= ["added orbital.z"]
        snd <$> feed s' "orbital.z" @?= Right ["21"]
        -- The same body under another keyword is another term: a unit's
        -- declaration makes its body a unit (design §3.10, U7).
        plain <- editFileOf s [] >>= replaceOnce "unit furlong" "let furlong"
        (s2, outs2) <- edited EditCodebase plain s
        outs2 @?= [movedLine "updated" s s2 "furlong"]
        expectError
          (snd <$> feed s2 "2 furlong")
          "`furlong` is a Num m, not a unit or a chart"
    , testCase "(e) a definition moved between blocks is removed and added" $ do
        s <- editSession
        file <-
          editFileOf s []
            >>= replaceOnce "  let spare = 42\n" ""
            >>= replaceOnce "namespace mechanics\n" "namespace mechanics\n  let spare = 42\n"
        (s', outs) <- edited EditCodebase file s
        outs @?= ["added mechanics.spare", "removed orbital.spare"]
        lookupName "mechanics.spare" s'.codebase
          @?= lookupName "orbital.spare" s.codebase
    , testCase
        "(f) an edited type re-hashes; constructors and fields follow, dependents upgrade or are left"
        $ do
          s <- editSession
          let body = lookupTypeName "orbital.Body" s.codebase
          -- One name: the type alone. A field whose dimension changes keeps
          -- the users that only match it, and leaves the one that builds it.
          file <-
            editFileOf s ["orbital.Body"]
              >>= replaceOnce "dist :: Num m}" "dist :: Num s}"
          (s', outs) <- edited (EditName "orbital.Body") file s
          let body' = lookupTypeName "orbital.Body" s'.codebase
          (body' /= body && isJust body') @? "the type re-hashed"
          (fst <$> Map.lookup "orbital.Body" s'.codebase.conNames) @?= body'
          ((\(h', _, _) -> h') <$> Map.lookup "orbital.dist" s'.codebase.fieldNames)
            @?= body'
          ((\(h', _, _) -> h') <$> Map.lookup "orbital.mass" s'.codebase.fieldNames)
            @?= body'
          case outs of
            [updated, upgradedWeight, leftEarth] -> do
              updated @?= "updated data orbital.Body"
              upgradedWeight @?= movedLine "upgraded" s s' "orbital.weight"
              ("left orbital.earth on #" `T.isPrefixOf` leftEarth) @? T.unpack leftEarth
              ("dimensions differ" `T.isInfixOf` leftEarth) @? T.unpack leftEarth
            other -> assertFailure (show other)
          -- The whole codebase: a field added, with its users in the file
          -- written for it.
          whole <-
            editFileOf s []
              >>= replaceOnce "dist :: Num m}" "dist :: Num m, spin :: Num}"
              >>= replaceOnce "Body (6 kg) (1 km)" "Body (6 kg) (1 km) 3"
              >>= replaceOnce "Body mass _ ->" "Body mass _ _ ->"
          (s2, outs2) <- edited EditCodebase whole s
          outs2
            @?= [ "updated data orbital.Body"
                , movedLine "updated" s s2 "orbital.earth"
                , movedLine "updated" s s2 "orbital.weight"
                ]
          Map.member "orbital.spin" s2.codebase.fieldNames @? "the new field is a label"
          -- A field resolves through the scope (design §7.6).
          (snd <$> (feed s2 "use orbital" >>= \(s3, _) -> feed s3 "orbital.earth.spin"))
            @?= Right ["3"]
          -- A field added to the type alone: its users are left, with reasons.
          added <-
            editFileOf s ["orbital.Body"]
              >>= replaceOnce "dist :: Num m}" "dist :: Num m, spin :: Num}"
          (_, outs3) <- edited (EditName "orbital.Body") added s
          -- The two users left, in an order their hashes decide.
          take 1 outs3 @?= ["updated data orbital.Body"]
          sort (map (T.takeWhile (/= '#')) (drop 1 outs3))
            @?= ["left orbital.earth on ", "left orbital.weight on "]
    , testCase "(g) a type error refuses the edit and changes nothing" $ do
        s <- editSession
        file <- editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = 3 m + 1\n"
        case applyEdit EditCodebase file s of
          Left err -> do
            ("error at " `T.isPrefixOf` err) @? T.unpack err
            ("let x = 3 m + 1" `T.isInfixOf` err) @? T.unpack err
            ("dimensions differ" `T.isInfixOf` err) @? T.unpack err
          Right (_, outs) -> assertFailure ("expected an error, got " <> show outs)
        -- An expression in the file, and a parse error, are refused too.
        exprFile <-
          editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = 3\n  x + 1\n"
        expectError (snd <$> applyEdit EditCodebase exprFile s) "holds definitions"
        broken <- editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = \n"
        case applyEdit EditCodebase broken s of
          Left _ -> pure ()
          Right (_, outs) -> assertFailure (show outs)
        -- What the REPL keeps after an error: the session as it was.
        let kept = either (const s) fst (applyEdit EditCodebase file s)
        sameLabels s.codebase kept.codebase
    , testCase "(h) an emptied file is refused" $ do
        s <- editSession
        expectError
          (snd <$> applyEdit EditCodebase "" s)
          "the file defines nothing in the codebase; if you mean to remove it all, use :unname"
        file <- editFileOf s []
        let headerOnly = T.unlines (takeWhile ("--" `T.isPrefixOf`) (T.lines file))
        expectError (snd <$> applyEdit EditCodebase headerOnly s) "defines nothing"
        expectError
          (snd <$> applyEdit (EditNamespace "orbital") "use std\nlet size = 10\n" s)
          "the file defines nothing in `orbital`; if you mean to remove it all, use :unname orbital"
    , testCase "(i) one name: its body updated, deleting it refused, others added" $ do
        s <- editSession
        file <- editFileOf s ["area"]
        file' <- replaceOnce "w * h" "w * h * 2" file
        (s', outs) <- edited (EditName "area") file' s
        outs @?= [movedLine "updated" s s' "area"]
        snd <$> feed s' "area 2 3" @?= Right ["12"]
        gone <- replaceOnce "let area = \\w -> \\h -> w * h\n" "" file
        expectError
          (snd <$> applyEdit (EditName "area") gone s)
          "the file no longer defines `area`; use :unname to remove it"
        more <- replaceOnce "let area" "let perimeter w h = 2 * (w + h)\nlet area" file
        (s3, outs3) <- edited (EditName "area") more s
        outs3 @?= ["added perimeter"]
        snd <$> feed s3 "perimeter 2 3" @?= Right ["10"]
        -- Nothing else is removed, and a cycle round-trips with its members.
        evenFile <- editFileOf s ["orbital.even"]
        (_, evenOuts) <- edited (EditName "orbital.even") evenFile s
        evenOuts @?= ["nothing changed"]
        -- A pending definition prints, but cannot be edited in place.
        case editRequest s{scratch = []} ["nosuch"] of
          Left err -> ("unknown name" `T.isInfixOf` err) @? T.unpack err
          Right other -> assertFailure (show other)
    , testCase "(j) :edit si includes the library; :edit alone never touches it" $ do
        s <- editSession
        file <- editFileOf s ["si"]
        ("unit km = kilo * 1 metre" `T.isInfixOf` file) @? "si.km is in the file"
        file' <-
          replaceOnce "unit km = kilo * 1 metre\n" "unit km = 1001 m\n" file
        (s', outs) <- edited (EditNamespace "si") file' s
        -- The library's own users in si are in the file; the others are
        -- propagated, the user's and astro.de440's bodies (written in km),
        -- independent ones in an order their hashes decide.
        take 1 outs @?= [T.replace "si.km" "km" (movedLine "updated" s s' "si.km")]
        sort (drop 1 outs)
          @?= sort
            ( [ movedLine "upgraded" s s' "orbital.earth"
              , movedLine "upgraded" s s' "trip"
              ]
                ++ [ movedLine "upgraded" s s' ("astro.de440." <> b)
                   | b <-
                       [ "sun"
                       , "mercury"
                       , "venus"
                       , "earth"
                       , "moon"
                       , "mars"
                       , "jupiter"
                       , "saturn"
                       , "uranus"
                       , "neptune"
                       , "pluto"
                       ]
                   ]
            )
        snd <$> feed s' "trip to m" @?= Right ["2002 m"]
        -- The codebase without the library: nothing under si is removed.
        plain <- editFileOf s []
        ("unit km" `T.isInfixOf` plain) @?= False
        changed <- replaceOnce "let size = 10\n" "let size = 11\n" plain
        (s2, _) <- edited EditCodebase changed s
        let underSi c = Map.filterWithKey (\k _ -> "si." `T.isPrefixOf` k) c.names
        underSi s2.codebase @?= underSi s.codebase
    , testCase "(k) :edit --file resumes from a file" $ do
        s <- editSession
        dir <- getTemporaryDirectory
        let path = dir </> "metron-edit-test.metron"
        file <- editFileOf s [] >>= replaceOnce "  let x = 3\n" "  let x = 6\n"
        BS.writeFile path (encodeUtf8 file)
        -- The pure feed refuses to read files; the REPL reads it and reconciles.
        expectError
          (runLinesP (editScript ++ [":edit --file " <> T.pack path]))
          "only the REPL reads files"
        let resume args = case editRequest s args of
              Right (EditResume target p) -> do
                text <- decodeUtf8 <$> BS.readFile p
                edited target text s
              other -> assertFailure (show other)
        (s', outs) <- resume ["--file", T.pack path]
        take 1 outs @?= [movedLine "updated" s s' "orbital.x"]
        snd <$> feed s' "orbital.y" @?= Right ["7"]
        nsFile <-
          editFileOf s ["orbital"] >>= replaceOnce "  let x = 3\n" "  let x = 6\n"
        BS.writeFile path (encodeUtf8 nsFile)
        (_, nsOuts) <- resume ["--file", T.pack path, "orbital"]
        take 1 nsOuts @?= [movedLine "updated" s s' "orbital.x"]
        removePathForcibly path
        editRequest s ["--file"]
          @?= Left "usage: :edit [name|namespace], or :edit --file path [name|namespace]"
    , testCase "(l) a +- definition entered again under its path keeps its hash" $ do
        s <- editSession
        file <- editFileOf s ["orbital.jitter"]
        ("let jitter = 2 ± 0.5" `T.isInfixOf` file) @? T.unpack file
        (s', outs) <- edited (EditName "orbital.jitter") file s
        outs @?= ["nothing changed"]
        lookupName "orbital.jitter" s'.codebase
          @?= lookupName "orbital.jitter" s.codebase
    , testCase "without an editor, :edit prints the pasteable source and says so" $ do
        s <- editSession
        snd <$> feed s ":edit area" @?= Right ["let area = \\w -> \\h -> w * h"]
        editorNote "scripted input opens no editor"
          @?= "note: scripted input opens no editor; this is the source :edit would open"
        export <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        snd <$> feed s ":edit" @?= Right [export]
        case editRequest s ["area"] of
          Right (EditOpen (EditName "area") (Right _) paste) ->
            paste @?= ["let area = \\w -> \\h -> w * h"]
          other -> assertFailure (show other)
        -- A pending definition prints as before, and is not opened.
        pending <-
          either
            (assertFailure . T.unpack)
            pure
            (sessionP (editScript ++ ["let fresh = 1"]))
        case editRequest pending ["fresh"] of
          Right (EditOpen _ (Left err) paste) -> do
            paste @?= ["let fresh = 1"]
            ("is not stored" `T.isInfixOf` err) @? T.unpack err
          other -> assertFailure (show other)
        editScopeArgs s (EditNamespace "orbital") @?= " orbital"
        s2 <-
          either
            (assertFailure . T.unpack)
            pure
            (sessionP (editScript ++ [":namespace orbital"]))
        editScopeArgs s2 (EditName "orbital.x") @?= " .orbital.x"
    ]

{- | A listing of types, then the library's own in the order of their
namespaces: the declarations of the built-in
types, then temperature's and time's (design §3.10, F2).
-}
withBuiltinTypes :: [Text] -> Either Text [Text]
withBuiltinTypes ts =
  Right
    ( ts
        ++ builtinTypeListing
        ++ [ "frame degC"
           , "frame degF"
           , "space ITS90 = Num K"
           , "frame kelvin"
           , "frame J2000"
           , "frame JD"
           , "frame MJD"
           , "space TT = Num s"
           , "frame unix"
           , "space UTC = Num s"
           ]
    )
