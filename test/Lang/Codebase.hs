-- | The codebase, it and namespaces.
module Lang.Codebase (
  codebaseTests,
  itTests,
  namespaceTests,
) where

import Data.List (sort)
import Data.Map.Strict qualified as Map (
  fromListWith,
  member,
  toList,
 )
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T (
  drop,
  isInfixOf,
  isPrefixOf,
  isSuffixOf,
  lines,
  pack,
  take,
  takeWhile,
  unpack,
 )
import Lang.Common (
  astroTypes,
  builtinTypeListing,
  evalP,
  expectError,
  expecting,
  hashShownAs,
  lastN,
  libraryListing,
  linesIn,
  multiline,
  num,
  persistLines,
  reload,
  replacements,
  runLines,
  runLinesP,
  seeded,
  sessionP,
  startsWith,
  toks,
  withTempStore,
 )
import Metron.Codebase (
  Codebase (charts, conNames, fieldNames, names, typeNames, units),
  lookupTypeName,
 )
import Metron.Core (
  Fin (FZ),
  Hint (Hint),
  Term (App, Lam, Ref, Var),
  Vec (VNil),
  showHash,
 )
import Metron.Driver (
  Session (codebase, scope, scratch, staging),
  exportRequest,
  exportSource,
  feed,
  feedFile,
 )
import Metron.Hash (hashTerm)
import Metron.Lexer (Token (TAbs, TField, TIdent))
import Metron.Lexer qualified as L (Token (TNum))
import Metron.Prelude (stdlibDefaultUses)
import Metron.Pretty (renderTerm)
import Metron.Repl qualified as R (
  Continuation (Block),
  continuation,
  highlight,
  namesOf,
 )
import Metron.Syntax qualified as S (Scope (uses))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (
  Assertion,
  assertBool,
  assertEqual,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )

-- | Run lines and keep only outputs matching a predicate.
outputsWhere :: (Text -> Bool) -> [Text] -> Either Text [Text]
outputsWhere p ls = filter p <$> runLines ls

codebaseTests :: TestTree
codebaseTests =
  testGroup
    "codebase"
    [ testCase
        ":ls lists names with their types, filtered by glob, kind or type query"
        $ do
          let ls args =
                runLinesP
                  ( [ "let speed = 7.5 km/s"
                    , "unit furlong = 201.168 m"
                    , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
                    , "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"
                    ]
                      ++ [":ls " <> args]
                  )
          ls ""
            @?= Right
              ( [ "area : Shape -> Num (m^2)"
                , "unit furlong : Unit m"
                , "speed : Num (m/s)"
                , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
                , "Circle : Num m -> Shape"
                , "Rect : Num m -> Num m -> Shape"
                ]
                  ++ libraryListing
              )
          ls "k*m"
            @?= Right
              [ "unit kilogram : Unit kg"
              , "unit klm : Unit (cd*rad^2)"
              , "unit km : Unit m"
              , "unit kohm : Unit (kg*m^2/(s^3*A^2))"
              ]
          ls "--units furl" @?= Right ["unit furlong : Unit m"]
          ls "--charts degC" @?= Right ["chart degC : Chart degC"]
          ls "--types"
            @?= Right
              ( -- The library's types: astro's records, the joint covariance
                -- in blocks, the spaces and the charts' frames, then Bool,
                -- lists and pairs.
                astroTypes
                  ++ [ "data Cov2 n d d1 = Cov2 {rr :: Mat n n (d^2), rv :: Mat n n (d*d1), vv :: Mat n n (d1^2)}"
                     , "Cov2 : forall n d d1. Mat n n (d^2) -> Mat n n (d*d1) -> Mat n n (d1^2) -> Cov2 n d d1"
                     , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
                     , "Circle : Num m -> Shape"
                     , "Rect : Num m -> Num m -> Shape"
                     ]
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
          -- The library's polymorphic constructors match too.
          ls ": Shape -> a"
            @?= Right
              [ "area : Shape -> Num (m^2)"
              , "Cons : forall a. a -> {a} -> {a}"
              , "Pair : forall a b. a -> b -> (a, b)"
              ]
          ls ": {a} -> Num" @?= Right ["length : forall a. {a} -> Num"]
          -- unification both ways: the query's d is one variable, cross has two
          ls ": Vec 3 d -> Vec 3 d -> Vec 3 (d^2)"
            @?= Right ["cross : forall (a : 3) d d1. Vec a d -> Vec a d1 -> Vec a (d*d1)"]
          ls "Rect : Num m -> Num m -> b"
            @?= Right ["Rect : Num m -> Num m -> Shape"]
          ls "nothing-like-this" @?= Right ["nothing matches"]
          case ls "--bogus" of
            Left err -> T.isInfixOf "unknown flag --bogus" err @? T.unpack err
            Right v -> assertFailure (show v)
          case ls ": Nope" of
            Left err -> T.isInfixOf "unknown type `Nope`" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase
        "propagation follows a rebinding only through the name it was made under"
        $ do
          -- `unit meter = m` is the library's `si.metre` term; changing meter must not
          -- rescale km, which is written as kilo * 1 metre.
          let session =
                [ "unit meter = m"
                , ":add"
                , "let d = 3 meter"
                , ":add"
                , "unit meter = 2 m"
                ]
          case runLinesP
            (session ++ [":update", "1 km to m", "d to m", ":todo", ":dependents meter"]) of
            Left err -> assertFailure (T.unpack err)
            Right ls -> do
              filter ("upgraded km" `T.isPrefixOf`) ls @?= []
              any ("upgraded d " `T.isPrefixOf`) ls @? show ls
              drop (length ls - 4) ls @?= ["1000 m", "6 m", "nothing to do", "d"]
          -- :upgrade is scoped the same way: a stale d moves, the library does not
          case runLinesP
            (session ++ [":update --no-upgrade", ":upgrade meter", "1 km to m", "d to m"]) of
            Left err -> assertFailure (T.unpack err)
            Right ls -> drop (length ls - 2) ls @?= ["1000 m", "6 m"]
    , testCase "scratch definitions are usable before :add"
        $ runLines ["let x = 5", "x + 1"] @?= Right ["6"]
    , testCase "redefining a pending name replaces it with a notice"
        $ runLines ["let x = 5", "let x = 6", "x"]
          @?= Right ["replaced pending definition of `x`", "6"]
    , testCase ":add stores new names and clears the scratch"
        $ runLines ["let x = 5", ":add", ":scratch", ":hash x"]
          @?= Right ["added x", "#" <> T.drop 1 (hashText 5)]
    , testCase ":add refuses a changed existing name"
        $ case runLines ["let x = 5", ":add", "let x = 6", ":add"] of
          Left err -> T.isInfixOf "use :update" err @? T.unpack err
          Right _ -> assertFailure "expected a conflict"
    , testCase ":add of an identical definition is fine"
        $ runLines ["let x = 5", ":add", "let x = 5", ":add"]
          @?= Right ["added x", "added x"]
    , testCase ":update rebinds and upgrades dependents (design §7.5)"
        $ expecting
          ( runLines
              ["let x = 5", "let y = x + 1", ":add", "let x = 6", ":update", "y", ":view y"]
          )
        $ \outs -> do
          any (startsWith "updated x") outs @? show outs
          any (startsWith "upgraded y") outs @? show outs
          lastN 2 outs @?= ["7", "y = x + 1"]
    , testCase ":update --no-upgrade leaves dependents on the old version"
        $ expecting
          ( runLines
              [ "let x = 5"
              , "let y = x + 1"
              , ":add"
              , "let x = 6"
              , ":update --no-upgrade"
              , "y"
              , ":view y"
              , ":todo"
              ]
          )
        $ \outs -> do
          any (startsWith "dependents left on old versions: y") outs @? show outs
          case lastN 3 outs of
            [v, view, td] -> do
              v @?= "6"
              startsWith "y = x#" view @? T.unpack view
              startsWith "stale: y uses x#" td @? T.unpack td
            other -> assertFailure (show other)
    , testCase ":upgrade moves stale dependents to the current version"
        $ expecting
          ( runLines
              [ "let x = 5"
              , "let y = x + 1"
              , ":add"
              , "let x = 6"
              , ":update --no-upgrade"
              , ":upgrade x"
              , "y"
              , ":view y"
              , ":todo"
              ]
          )
        $ \outs -> do
          any (startsWith "upgraded y") outs @? show outs
          lastN 3 outs @?= ["7", "y = x + 1", "nothing to do"]
    , testCase "upgrading propagates transitively and through cycles"
        $ case runLines
          [ "let base = 10"
          , "let f n = if n == 0 then base else f (n - 1)"
          , "let g = f 3 + 1"
          , ":add"
          , "let base = 20"
          , ":update"
          , "g"
          , ":view g"
          ] of
          Right outs -> do
            any (startsWith "upgraded f") outs @? show outs
            any (startsWith "upgraded g") outs @? show outs
            lastN 2 outs @?= ["21", "g = f 3 + 1"]
          Left err -> assertFailure (T.unpack err)
    , testCase ":history lists refs newest first after an update"
        $ case runLines ["let x = 5", ":add", "let x = 6", ":update", ":history x"] of
          Right outs -> case lastN 2 outs of
            [cur, old] -> do
              T.isSuffixOf "  (current)" cur @? T.unpack cur
              assertBool "distinct" (T.takeWhile (/= ' ') cur /= old)
            other -> assertFailure (show other)
          Left err -> assertFailure (T.unpack err)
    , testCase
        "historical values and functions resolve in expressions and definitions"
        $ do
          let setup = ["let f x = x + 1", ":add"]
              digest = "#" <> hashShownAs setup "f"
              changed = setup ++ ["let f x = x + 2", ":update"]
          expecting
            ( runLines
                ( changed
                    ++ [ "f" <> digest <> " 10"
                       , digest <> " 10"
                       , "let old = f" <> digest
                       , "old 10"
                       , "let f = 99 in f" <> digest <> " 10"
                       ]
                )
            )
            $ \outs ->
              lastN 4 outs @?= replicate 4 "11"
          expecting (runLines (changed ++ [":unname f", "f" <> digest <> " 10"])) $ \outs ->
            last outs @?= "11"
    , testCase "hash arguments do not steal measurement labels" $ do
        let digest = hashText 5
        expecting
          ( runLines
              [ "let x = 5"
              , ":add"
              , "let ident x = x"
              , "ident (" <> digest <> ")"
              , "let n = 5 ± 1 #sensor"
              , "n - n"
              , "let n2 = 5 ± 1#sensor"
              , "n - n2"
              ]
          )
          $ \outs ->
            lastN 3 outs @?= ["5", "0", "0"]
    , testCase "historical names respect namespace lookup and explicit absolute paths" $ do
        let setup = ["namespace lab\n  let f x = x + 1", ":add"]
            digest = "#" <> hashShownAs setup "lab.f"
        expecting
          ( runLines
              ( setup
                  ++ [ "lab.f" <> digest <> " 3"
                     , ":use lab"
                     , "f" <> digest <> " 4"
                     , ".lab.f" <> digest <> " 5"
                     ]
              )
          )
          $ \outs -> do
            take 1 (drop 1 outs) @?= ["4"]
            lastN 2 outs @?= ["5", "6"]
    , testCase "hash references validate missing, malformed and ambiguous prefixes" $ do
        expectError (runLines ["#w"]) "invalid hash prefix"
        expectError
          (runLines ["#0000000000000000000000000000000000000000000000000000"])
          "no stored version matches"
        expectError
          (runLines ["let x = 5", ":add", "x" <> hashText 6])
          "no stored version matches"
        expectError
          (runLines ["let x = 5", ":add", hashText 5 <> ".0"])
          "member index is only valid"
        let numbers = [0 .. 64]
            groups = Map.fromListWith (++) [(T.take 2 (hashText n), [n]) | n <- numbers]
            prefix = case filter ((> 1) . length . snd) (Map.toList groups) of
              (p, _) : _ -> p
              [] -> error "65 hashes must share one of 32 initial digits"
            setup =
              ["let n" <> T.pack (show n) <> " = " <> T.pack (show n) | n <- [0 :: Int .. 64]]
        expectError (runLines (setup ++ [":add", prefix])) "ambiguous hash reference"
    , testCase "recursive-group references select and validate members" $ do
        let setup = ["let down n = if n == 0 then 0 else down (n - 1)", ":add"]
            digest = "#" <> hashShownAs setup "down"
            groupHash = T.takeWhile (/= '.') digest
        expecting (runLines (setup ++ [digest <> " 3", "down" <> digest <> " 4"])) $ \outs ->
          lastN 2 outs @?= ["0", "0"]
        expectError (runLines (setup ++ [groupHash])) "needs a valid .index"
        expectError (runLines (setup ++ [groupHash <> ".999"])) "needs a valid .index"
    , testCase "bare hash arguments print with grouping and read back" $ do
        let setup = ["let ident x = x", "let five = 5", ":add"]
            fn = hashTerm (Lam (Hint "x") (Var FZ))
            value = hashTerm (num 5)
            source =
              renderTerm
                (\digest _ _ -> showHash digest)
                VNil
                (App (Ref fn Nothing (Hint "")) (Ref value Nothing (Hint "")))
        source @?= showHash fn <> " (" <> showHash value <> ")"
        expecting (runLines (setup ++ [source])) $ \outs -> last outs @?= "5"
    , testCase
        "historical references do not become dependencies on new local bindings"
        $ do
          let setup = ["let x = 5", "let y = x + 1", "let z = y * 2", ":add"]
          expecting
            ( runLines
                ( setup
                    ++ [ "let x = x" <> hashText 5 <> " + 1\nlet newOnly = x * 3"
                       , ":update"
                       , "x"
                       , "y"
                       , "z"
                       , "newOnly"
                       , ":todo"
                       ]
                )
            )
            $ \outs ->
              lastN 5 outs @?= ["6", "7", "14", "18", "nothing to do"]
    , testCase
        "historical record fields and tensor projections remain postfix operations"
        $ do
          let setup =
                [ "data Box = Box {value :: Num}"
                , "let box = Box {value = 7}"
                , "let vector = [3, 4]"
                , ":add"
                ]
              boxRef = "box#" <> hashShownAs setup "box"
              vectorRef = "vector#" <> hashShownAs setup "vector"
          expecting (runLines (setup ++ [boxRef <> ".value", "(" <> vectorRef <> ").0"])) $ \outs ->
            lastN 2 outs @?= ["7", "3"]
    , testCase "historical unit and chart roles come from the referenced version" $ do
        let setup = ["unit track = 400 m", ":add"]
            ref = "track#" <> hashShownAs setup "track"
            changed = setup ++ ["let track = 7", ":update --no-upgrade"]
        expecting (runLinesP (changed ++ ["5 * " <> ref <> " to m"])) $ \outs ->
          last outs @?= "2000 m"
        expectError (runLinesP (changed ++ [ref])) "a unit is not an expression"
        let chartRef = "degC#" <> hashShownAs [] "degC"
        expecting (runLinesP ["20 " <> chartRef <> " to degF"]) $ \outs ->
          last outs @?= "68 degF"
    , testCase "historical references survive a store reload" $ withTempStore $ \dir -> do
        let setup = ["let f x = x + 1", ":add"]
            digest = "#" <> hashShownAs setup "f"
        _ <-
          persistLines
            dir
            ( setup
                ++ [ "let f x = x + 2"
                   , ":update"
                   , "let previous = f" <> digest
                   , ":add"
                   ]
            )
        (s, notes) <- reload dir
        notes @?= []
        linesIn s ["previous 10", "f" <> digest <> " 10", "f 10"]
          @?= Right ["11", "11", "12"]
    , testCase "alpha-equivalent definitions share a hash"
        $ expecting
          ( outputsWhere
              (startsWith "#")
              ["let f x = x + 1", "let g y = y + 1", ":hash f", ":hash g"]
          )
        $ \case
          [a, b] -> a @?= b
          other -> assertFailure (show other)
    , testCase ":names finds every label of a hash"
        $ case runLines ["let x = 5", "let five = 5", ":add", ":hash x"] of
          Right outs ->
            runLines ["let x = 5", "let five = 5", ":add", ":names " <> last outs]
              @?= Right ["added x", "added five", last outs <> " five x"]
          Left err -> assertFailure (T.unpack err)
    , testCase ":dependents lists definitions that mention the current ref"
        $ expecting
          ( runLines
              [ "let x = 5"
              , "let y = x + 1"
              , "let z = x * 2"
              , "let w = 7"
              , ":add"
              , ":dependents x"
              ]
          )
        $ \outs ->
          drop 4 outs @?= ["y", "z"]
    , testCase
        ":view shows current references by name and prints with minimal parentheses"
        $ runLines ["let f a b = (a + b) * -a", ":view f"]
          @?= Right ["f = \\a -> \\b -> (a + b) * -a"]
    , testCase ":view of a cycle member names the other members"
        $ runLines
          [ "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)"
          , ":view odd"
          ]
          @?= Right ["odd = \\n -> if n == 0 then false else even (n - 1)"]
    , testCase "cycle hash is independent of the order members are entered"
        $ let evenDef = "let even n = if n == 0 then true else odd (n - 1)"
              oddDef = "let odd n = if n == 0 then false else even (n - 1)"
              a = runLines [evenDef <> "\n" <> oddDef, ":hash even", ":hash odd"]
              b = runLines [oddDef <> "\n" <> evenDef, ":hash even", ":hash odd"]
           in do
                a @?= b
                case a of
                  Right [he, ho] -> do
                    T.takeWhile (/= '.') he @?= T.takeWhile (/= '.') ho
                    assertBool "distinct members" (he /= ho)
                  other -> assertFailure (show other)
    , testCase "a self-recursive definition is a one-member cycle"
        $ case runLines
          [ "let fact n = if n == 0 then 1 else n * fact (n - 1)"
          , ":hash fact"
          , ":view fact"
          ] of
          Right [hf, view] -> do
            T.isSuffixOf ".0" hf @? T.unpack hf
            view @?= "fact = \\n -> if n == 0 then 1 else n * fact (n - 1)"
          other -> assertFailure (show other)
    , testCase ":edit prints a definition as source"
        $ runLines ["let double x = x * 2", ":add", ":edit double"]
          @?= Right ["added double", "let double = \\x -> x * 2"]
    , testCase ":alias and :unname manage labels only"
        $ case runLines
          ["let x = 5", ":add", ":alias five x", ":unname x", "five", ":history x"] of
          Right outs -> do
            outs !! 3 @?= "5"
            length (drop 4 outs) @?= 1
          Left err -> assertFailure (T.unpack err)
    , testCase ":forget drops a pending definition"
        $ case runLines ["let x = 5", ":forget x", "x"] of
          Left err -> T.isInfixOf "unknown name" err @? T.unpack err
          Right outs -> assertFailure (show outs)
    , testCase ":todo reports pending and clean states" $ do
        runLines ["let x = 5", ":todo"] @?= Right ["pending: x (use :add or :update)"]
        runLines [":todo"] @?= Right ["nothing to do"]
    , testCase "unknown name in a command"
        $ runLines [":view nope"] @?= Left "unknown name `nope`"
    ]
 where
  hashText :: Rational -> Text
  hashText r = showHash (hashTerm (num r))

-- The last result -------------------------------------------------------------------

{- | Feed lines as the REPL does: an input that fails prints its error and
leaves the session as it was.
-}
replLinesP :: [Text] -> [Either Text [Text]]
replLinesP = go seeded
 where
  go _ [] = []
  go s (l : ls) = case feed s l of
    Left err -> Left err : go s ls
    Right (s', outs) -> Right outs : go s' ls

itTests :: TestTree
itTests =
  testGroup
    "it, the last result"
    [ testCase "it is the last expression" $ do
        runLinesP ["1 + 2", "it * 2"] @?= Right ["3", "6"]
        runLinesP ["1 + 2", "it * 2", "it + 1"] @?= Right ["3", "6", "7"]
        -- On one line, each expression is `it` for the next.
        runLinesP ["1 + 2; it * 10"] @?= Right ["3", "30"]
    , testCase ":type, :view and :exact see it" $ do
        runLinesP ["3 m + 2 m", ":type it"] @?= Right ["5 m", "Num m"]
        runLinesP ["1 + 2", ":view it"] @?= Right ["3", "it = 1 + 2"]
        -- a new it absorbs the previous one, so :view shows the whole expression
        runLinesP ["1 + 2", "it * 2", ":view it", "it + 1", ":view it"]
          @?= Right ["3", "6", "it = (1 + 2) * 2", "7", "it = (1 + 2) * 2 + 1"]
        -- A nudge declared in the last expression is labelled with its name.
        runLinesP ["2 ± 0.1", ":exact it"]
          @?= Right ["2.0 ± 0.1", "2 + 0.1·e[bound, it]"]
    , testCase "it before any expression is an unknown name" $ do
        case evalP "it" of
          Left err -> T.isInfixOf "unknown name `it`" err @? T.unpack err
          Right v -> assertFailure (show v)
        case runLinesP [":type it"] of
          Left err -> T.isInfixOf "unknown name `it`" err @? T.unpack err
          Right v -> assertFailure (show v)
        -- and a definition that uses it is refused as unknown, not as `it`
        case runLinesP ["let x = it"] of
          Left err -> T.isInfixOf "unknown name `it`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a definition cannot store it, nor define it" $ do
        let refused input = case runLinesP ["1 + 2", input] of
              Left err ->
                T.isInfixOf
                  "`it` is the last result and cannot be stored; paste its definition (:view it) instead"
                  err
                  @? T.unpack err
              Right v -> assertFailure (show v)
        refused "let x = it"
        refused "let x = it + 1"
        case runLinesP ["let it = 5"] of
          Left err ->
            T.isInfixOf "`it` is the last result and cannot be defined" err @? T.unpack err
          Right v -> assertFailure (show v)
        -- A parameter called `it` is not the last result.
        runLinesP ["1 + 2", "let f it = it + 1", "f 1"] @?= Right ["3", "2"]
    , testCase "it is never stored or listed" $ do
        case sessionP ["let y = 5", "y + 1", "it * 2", ":add"] of
          Left err -> assertFailure (T.unpack err)
          Right s -> do
            Map.member "it" s.codebase.names @?= False
            Map.member "it" s.staging.names @?= False
            Map.member "y" s.codebase.names @?= True
            -- still usable after the add
            snd <$> feed s "it" @?= Right ["12"]
        case runLinesP ["1 + 2", ":ls --all"] of
          Left err -> assertFailure (T.unpack err)
          Right outs -> filter ("it " `T.isPrefixOf`) outs @?= []
    , testCase "an error leaves the previous it" $ do
        let results = replLinesP ["1 + 2", "1 / 0", "it +", "it * 2"]
        map (either (const Nothing) Just) results
          @?= [Just ["3"], Nothing, Nothing, Just ["6"]]
        take 1 (drop 1 results) @?= [Left "error: division by zero"]
    , testCase "it outlives the scratch definitions it used" $ do
        runLinesP ["let y = 5", "y + 1", "let y = 6", "it", "y + 1"]
          @?= Right ["6", "replaced pending definition of `y`", "6", "7"]
        runLinesP ["let y = 5", "y + 1", ":forget y", "it * 2"]
          @?= Right ["6", "forgot `y`", "12"]
    , testCase "it names a reference only when nothing else does" $ do
        -- `5` and `x` share a hash; `x` is renamed `w`, so `z` prints the
        -- current name, and `it`, which sorts first, does not take its place.
        let setup = ["let x = 5", "let z = x + 1", ":add", ":alias w x", ":unname x", "5"]
        expecting (runLinesP (setup ++ [":hash w", ":hash it"])) $ \outs ->
          case lastN 2 outs of
            [hw, hi] -> hw @?= hi
            other -> assertFailure (show other)
        expecting (runLinesP (setup ++ [":view z"])) $ \outs ->
          lastN 1 outs @?= ["z = w + 1"]
    ]

-- | The orbital example: a root @mu@, and a namespace with its own.
orbitalSetup :: [Text]
orbitalSetup =
  [ "let mu = 100"
  , multiline
      [ "namespace orbital"
      , "  let mu = 3"
      , "  let period a = a * mu"
      ]
  , ":add"
  ]

{- | A codebase for the export round trip: two namespaces, a nested one, a
root definition, a unit, a chart, a record with a field a function uses, a
cycle, a block definition shadowing a root name, and a prelude reference.
-}
exportScript :: [Text]
exportScript =
  [ multiline
      [ "let size = 10"
      , "let d = 2 km"
      , "unit furlong = 201.168 m"
      , "namespace orbital"
      , "  unit au = 149597870700 m"
      , "  space Distance = Num m"
      , "  chart tip on Distance at 1 au step au"
      , "  data Body = Body {mass :: Num kg, dist :: Num m}"
      , "  let weight b = b.mass * 9.81 m/s^2"
      , "  let size = 3"
      , "  let both = size + .size"
      , "  let even n = if n == 0 then true else odd (n - 1)"
      , "  let odd n = if n == 0 then false else even (n - 1)"
      , "  let earth = Body {mass = 6 kg, dist = 1 au}"
      , "  namespace kepler"
      , "    let anomaly e x = x + e * x"
      , "    let viaParent = orbital.size * 2"
      , "namespace mechanics"
      , "  let g0 = 9.80665 m/s^2"
      , "  let fall t = g0 * t^2 / 2"
      , "  let useOrbital = orbital.kepler.anomaly 1 2 + orbital.weight orbital.earth / g0 / 1 kg"
      , "  data Probe = Probe {body :: orbital.Body, place :: Num m}"
      , "  let probePlace p = p.place"
      ]
  , ":add"
  ]

namespaceTests :: TestTree
namespaceTests =
  testGroup
    "namespaces"
    [ testCase
        "a multiline defines orbital.*, and a bare name inside resolves there first"
        $ do
          runLinesP (orbitalSetup ++ ["orbital.period 2", "orbital.mu", "mu"])
            @?= Right ["added mu", "added orbital.mu", "added orbital.period", "6", "3", "100"]
          expecting (runLinesP (orbitalSetup ++ [":view orbital.period"])) $ \outs ->
            last outs @?= "orbital.period = \\a -> a * orbital.mu"
    , testCase "blocks nest"
        $ runLinesP
          [ multiline
              [ "namespace orbital"
              , "  namespace kepler"
              , "    let anomaly e x = x + e * x"
              ]
          , "orbital.kepler.anomaly 1 2"
          ]
          @?= Right ["4"]
    , testCase "a multiline's statements must be indented under it"
        $ expectError
          (runLinesP [multiline ["namespace orbital", "let x = 1"]])
          "has no statements"
    , testCase "use: bare names from the namespace resolve, and :type names them" $ do
        expecting (runLinesP (orbitalSetup ++ ["use orbital", "period 2"])) $ \outs ->
          last outs @?= "6"
        let ty src = fmap last (runLinesP (orbitalSetup ++ ["use orbital", ":type " <> src]))
        ty "period" @?= ty "orbital.period"
        expecting
          ( runLinesP
              (orbitalSetup ++ [":uses", "use orbital", ":uses", ":unuse orbital", ":uses"])
          )
          $ \outs ->
            let stored = ["use " <> u <> " (stored)" | u <- stdlibDefaultUses]
             in lastN 19 outs @?= stored ++ stored ++ ["use orbital"] ++ stored
    , testCase "use … as: an alias prefix"
        $ expecting (runLinesP (orbitalSetup ++ ["use orbital as o", "o.period 2"]))
        $ \outs ->
          last outs @?= "6"
    , testCase "two uses offering a name is an error, not a choice"
        $ expectError
          ( runLinesP
              [ multiline ["namespace a", "  let x = 1"]
              , multiline ["namespace b", "  let x = 2"]
              , "use a"
              , "use b"
              , "x + 1"
              ]
          )
          "`x` is both `a.x` and `b.x`; write one of them"
    , testCase
        "a command's name the uses offer as several: :view shows each, a query takes its kind"
        $ do
          let hashOf p = runLinesP [":hash " <> p]
          -- A type in one namespace and a term in another: both, types first,
          -- each after its full path.
          runLinesP [":view TT"]
            @?= Right ["-- time.TT", "space TT = Num s", "-- si.TT", "TT = tera * 1 T"]
          -- A query about a definition takes the one term among them.
          runLinesP [":hash TT"] @?= hashOf "si.TT"
          runLinesP [":history TT"] @?= runLinesP [":history si.TT"]
          -- Two terms: :view shows both, a query lists them.
          runLinesP [":use physics", ":view h"]
            @?= Right
              [ "stored use physics"
              , "-- physics.h"
              , "physics.h = 6.62607015e-34 J * s"
              , "-- time.h"
              , "time.h = 60 min"
              ]
          expectError
            (runLinesP [":use physics", ":hash h"])
            "`h` is both `physics.h` and `time.h`; write one of them"
          -- One match is as before, and none is unknown.
          runLinesP [":view UTC"] @?= Right ["space UTC = Num s"]
          expectError (runLinesP [":view nosuch"]) "unknown name `nosuch`"
    , testCase "an absolute .name picks the root's"
        $ runLinesP
          [ "let period a = a"
          , multiline
              [ "namespace orbital"
              , "  let period a = a * 3"
              , "  let near = period 5"
              , "  let far = .period 5"
              ]
          , "orbital.near"
          , "orbital.far"
          ]
          @?= Right ["15", "5"]
    , testCase "a full path works from the root without a use"
        $ expecting (runLinesP (orbitalSetup ++ ["orbital.period (orbital.mu)"]))
        $ \outs ->
          last outs @?= "9"
    , testCase
        "a data type in a multiline: its constructor and fields, inside and out"
        $ do
          let setup =
                [ multiline
                    [ "namespace orbital"
                    , "  data Body = Body {mass :: Num kg, dist :: Num m}"
                    , "  let earth = Body {mass = 6 kg, dist = 1 m}"
                    , "  let massOf b = b.mass"
                    , "  let far b = case b of"
                    , "    Body m d -> d"
                    ]
                ]
          runLinesP
            (setup ++ ["orbital.massOf orbital.earth", "orbital.far orbital.earth"])
            @?= Right ["6 kg", "1 m"]
          runLinesP (setup ++ ["orbital.Body {mass = 2 kg, dist = 3 m}"])
            @?= Right ["orbital.Body {mass = 2 kg, dist = 3 m}"]
          runLinesP
            ( setup
                ++ [ "let b = orbital.Body {mass = 2 kg, dist = 3 m}"
                   , "case b of orbital.Body m d -> m"
                   ]
            )
            @?= Right ["2 kg"]
          expecting (runLinesP (setup ++ [":add", ":view orbital.Body"])) $ \outs ->
            last outs
              @?= "data orbital.Body = orbital.Body {mass :: Num kg, dist :: Num m}"
    , testCase "a cycle inside a multiline"
        $ runLinesP
          [ multiline
              [ "namespace p"
              , "  let even n = if n == 0 then true else odd (n - 1)"
              , "  let odd n = if n == 0 then false else even (n - 1)"
              ]
          , "p.even 4"
          , "p.odd 4"
          ]
          @?= Right ["true", "false"]
    , testCase "a name is never both a label and a namespace" $ do
        expectError
          (runLinesP (orbitalSetup ++ ["let orbital = 1"]))
          "`orbital` is a namespace; a definition cannot have its name"
        expectError
          ( runLinesP
              ["let period = 1", ":add", multiline ["namespace period", "  let x = 1"]]
          )
          "`period` is a definition; it cannot also be a namespace"
        -- The library's labels are under its namespaces (design §7.7).
        expectError
          (runLinesP [multiline ["namespace si.km", "  let x = 1"]])
          "`si.km` is a definition; it cannot also be a namespace"
        expectError
          (runLinesP [":namespace si.km"])
          "`si.km` is a definition; it cannot also be a namespace"
    , testCase "a ± definition's namespace reaches its hash; a plain one's does not" $ do
        let hashOf ls n = fmap last (runLinesP (ls ++ [":hash " <> n]))
        -- The owner stamp is the full path (design §3.2.4).
        ( hashOf ["let r = 1 m ± 0.1 m"] "r"
            /= hashOf [multiline ["namespace a", "  let r = 1 m ± 0.1 m"]] "a.r"
          )
          @? "a.r and r are two measurements"
        hashOf ["let q = 1 m"] "q"
          @?= hashOf [multiline ["namespace a", "  let q = 1 m"]] "a.q"
        -- Two namespaces, one text: two terms, and their difference keeps both nudges.
        let two =
              [ multiline ["namespace a", "  let x = 1 ± 0.1"]
              , multiline ["namespace b", "  let x = 1 ± 0.1"]
              ]
        (hashOf two "a.x" /= hashOf two "b.x") @? "a.x and b.x are two measurements"
        expecting (runLinesP (two ++ ["a.x - b.x", ":covariance a.x - b.x"])) $ \outs ->
          lastN 3 outs @?= ["0.0 ± 0.2", "variance 0", "bound 0.2"]
    , testCase ":namespace: single lines land under it, and :scratch shows the path" $ do
        runLinesP [":namespace", ":namespace orbital", ":namespace"]
          @?= Right ["namespace . (the root)", "namespace orbital", "namespace orbital"]
        runLinesP
          [ ":namespace orbital"
          , "let x = 1"
          , ":scratch"
          , ":namespace ."
          , ":scratch"
          , "orbital.x"
          ]
          @?= Right
            [ "namespace orbital"
            , "pending: x"
            , "namespace . (the root)"
            , "pending: orbital.x"
            , "1"
            ]
        -- A block nests under the current namespace.
        runLinesP
          [ ":namespace orbital"
          , multiline ["namespace kepler", "  let anomaly e x = x + e * x"]
          , ":namespace ."
          , "orbital.kepler.anomaly 1 2"
          ]
          @?= Right ["namespace orbital", "namespace . (the root)", "4"]
    , testCase "a use inside a block does not leak out of it"
        $ expectError
          ( runLinesP
              [ multiline ["namespace a", "  let x = 1"]
              , multiline ["namespace b", "  use a", "  let y = x", "let z = x"]
              ]
          )
          "unknown name `x`"
    , testCase "a nominal type's namespace reaches its hash" $ do
        root <- either (assertFailure . T.unpack) pure (sessionP ["data T = T Num"])
        inner <-
          either
            (assertFailure . T.unpack)
            pure
            (sessionP [multiline ["namespace a", "  data T = T Num"]])
        (lookupTypeName "a.T" inner.staging /= lookupTypeName "T" root.staging)
          @? "a.T and T are two types"
        isJust (lookupTypeName "T" root.staging) @? "declared"
        isJust (lookupTypeName "a.T" inner.staging) @? "declared"
    , testCase ":ls of a namespace lists its labels relative to it" $ do
        expecting
          ( runLinesP
              [ multiline
                  [ "namespace orbital"
                  , "  unit au = 149597870700 m"
                  , "  data Body = Body {mass :: Num kg}"
                  , "  let mu = 3"
                  ]
              , ":add"
              , ":ls orbital"
              ]
          )
          $ \outs ->
            lastN 4 outs
              @?= [ "unit au : Unit m"
                  , "mu : Num"
                  , "data Body = Body {mass :: Num kg}"
                  , "Body : Num kg -> Body"
                  ]
        expecting (runLinesP (orbitalSetup ++ [":namespace orbital", ":ls"])) $ \outs ->
          lastN 2 outs @?= ["mu : Num", "period : forall s d. Tensor s d -> Tensor s d"]
        -- Alone at the root: the root's own labels, then the namespaces under it.
        expecting (runLinesP (orbitalSetup ++ [":ls"])) $ \outs ->
          lastN 10 outs
            @?= sort ("namespace orbital (2 names)" : libraryListing)
        expecting
          ( runLinesP
              ( orbitalSetup
                  ++ [ multiline ["namespace orbital.kepler", "  let e = 1"]
                     , ":namespace orbital"
                     , ":ls"
                     ]
              )
          )
          $ \outs ->
            lastN 3 outs
              @?= [ "mu : Num"
                  , "period : forall s d. Tensor s d -> Tensor s d"
                  , "namespace kepler (1 name)"
                  ]
    , testCase
        ":rename a definition, and a namespace with its units, types and fields"
        $ do
          expecting
            ( runLinesP
                ( orbitalSetup
                    ++ [":rename orbital.period orbital.T", "orbital.T 2", ":history orbital.period"]
                )
            )
            $ \outs -> do
              lastN 2 (init outs) @?= ["renamed `orbital.period` to `orbital.T`", "6"]
              ("(current)" `T.isInfixOf` last outs) @? "history keeps the old name"
          expectError
            ( runLinesP
                (orbitalSetup ++ [":rename orbital.period orbital.T", "orbital.period 2"])
            )
            "unknown"
          let setup =
                [ multiline
                    [ "namespace orbital"
                    , "  unit au = 149597870700 m"
                    , "  data Body = Body {mass :: Num kg}"
                    , "  let earth = Body {mass = 6 kg}"
                    ]
                , ":add"
                , ":rename orbital mechanics"
                ]
          expecting
            ( runLinesP
                ( setup
                    ++ [ "2 mechanics.au"
                       , "use mechanics"
                       , "earth.mass"
                       , "mechanics.Body {mass = 1 kg}"
                       ]
                )
            )
            $ \outs ->
              map (T.takeWhile (/= '#')) (lastN 6 outs)
                @?= [ "renamed the 5 labels under `orbital` to `mechanics`"
                    , "re-hashed data mechanics.Body"
                    , "re-hashed mechanics.earth "
                    , "2 mechanics.au"
                    , "6 kg"
                    , "Body {mass = 1 kg}"
                    ]
          expectError (runLinesP (setup ++ ["orbital.earth"])) "unknown"
    , testCase ":rename refuses a clash and changes nothing" $ do
        expectError
          (runLinesP (orbitalSetup ++ ["let Tq = 1", ":add", ":rename orbital.period Tq"]))
          "`Tq` is already a label; nothing was changed"
        expectError
          (runLinesP (orbitalSetup ++ ["let x = 1", ":add", ":rename x mu.y"]))
          "`mu` is a definition; it cannot also be a namespace"
    , testCase ":move puts a definition or a namespace under another" $ do
        expecting
          ( runLinesP
              ( orbitalSetup
                  ++ [ "let period a = a + 1"
                     , ":add"
                     , ":move period orbital.slow"
                     , "orbital.slow.period 1"
                     ]
              )
          )
          $ \outs -> lastN 2 outs @?= ["moved 1 label to `orbital.slow`", "2"]
        expecting
          ( runLinesP
              (orbitalSetup ++ [":move orbital mechanics", "mechanics.orbital.period 2"])
          )
          $ \outs -> lastN 2 outs @?= ["moved 2 labels to `mechanics`", "6"]
    , testCase ":alias and :unname of a namespace" $ do
        expecting
          ( runLinesP
              (orbitalSetup ++ [":alias o2 orbital", "o2.period 2", "orbital.period 2"])
          )
          $ \outs ->
            lastN 3 outs @?= ["`o2` now also names the 2 labels under `orbital`", "6", "6"]
        expecting
          (runLinesP (orbitalSetup ++ [":unname orbital", ":history orbital.mu"]))
          $ \outs ->
            last (init outs)
              @?= "removed the 2 labels under `orbital`; :history name still finds them"
        expectError
          (runLinesP (orbitalSetup ++ [":unname orbital", "orbital.mu"]))
          "unknown"
    , testCase "printing: relative inside the namespace, full outside" $ do
        expecting
          ( runLinesP
              (orbitalSetup ++ [":namespace orbital", ":view period", ":edit period"])
          )
          $ \outs -> lastN 2 outs @?= ["period = \\a -> a * mu", "let period = \\a -> a * mu"]
        expecting (runLinesP (orbitalSetup ++ [":edit orbital.period"])) $ \outs ->
          lastN 2 outs @?= ["namespace orbital", "  let period = \\a -> a * mu"]
        -- The root's km prints bare inside a namespace that has none of its own.
        expecting
          ( runLinesP
              [ multiline ["namespace orbital", "  let d = 2 km"]
              , ":add"
              , ":namespace orbital"
              , ":view d"
              ]
          )
          $ \outs -> last outs @?= "d = 2 km"
    , testCase "printing: the shortest spelling that resolves back" $ do
        -- A use makes a name print bare.
        expecting
          ( runLinesP
              (orbitalSetup ++ ["let gg = orbital.period 1", ":add", "use orbital", ":view gg"])
          )
          $ \outs -> last outs @?= "gg = period 1"
        -- Two uses offering x: each keeps its path.
        expecting
          ( runLinesP
              [ multiline ["namespace a", "  let x = 1"]
              , multiline ["namespace b", "  let x = 2"]
              , "let y = a.x + b.x"
              , ":add"
              , "use a"
              , "use b"
              , ":view y"
              ]
          )
          $ \outs -> last outs @?= "y = a.x + b.x"
        -- A multiline with its own km refers to the library's by its path.
        expecting
          ( runLinesP
              [ multiline
                  ["namespace orbital", "  let km = 5", "  let d = 2 si.km", "  let e = km"]
              , ":add"
              , ":namespace orbital"
              , ":view d"
              , ":view e"
              , "d"
              ]
          )
          $ \outs -> lastN 3 outs @?= ["d = 2 si.km", "e = km", "2 si.km"]
        -- A root name with the spelling the library has takes a leading dot.
        expecting
          ( runLinesP
              [ multiline
                  ["let km = 5", "namespace orbital", "  let km = 6", "  let d = .km + km"]
              , ":add"
              , ":namespace orbital"
              , ":view d"
              ]
          )
          $ \outs -> last outs @?= "d = .km + km"
    , testCase "a file's uses last for the file only" $ do
        s <- either (assertFailure . T.unpack) pure (sessionP orbitalSetup)
        case feedFile s (multiline ["use orbital", "period 2"]) of
          Left err -> assertFailure (T.unpack err)
          Right (s', outs) -> do
            outs @?= ["6"]
            s'.scope.uses @?= []
    , testCase "completion: dotted names and used names" $ do
        s <- either (assertFailure . T.unpack) pure (sessionP orbitalSetup)
        ("orbital.period" `elem` replacements s "orb")
          @? "orb completes to orbital.period"
        ("orbital.period" `elem` replacements s "orbital.pe") @? "orbital.pe completes"
        u <-
          either
            (assertFailure . T.unpack)
            pure
            (sessionP (orbitalSetup ++ ["use orbital"]))
        ("period" `elem` replacements u "per") @? "a used name completes bare"
    , testCase "the REPL waits for a namespace's block" $ do
        R.continuation "namespace orbital" @?= Just R.Block
        R.continuation "namespace orbital.kepler" @?= Just R.Block
        R.continuation "use orbital" @?= Nothing
    , testCase ":export reads back to the same labels and hashes" $ do
        original <- either (assertFailure . T.unpack) pure (sessionP exportScript)
        source <- either (assertFailure . T.unpack) pure (exportSource original Nothing)
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        let same :: (Eq a, Show a) => String -> (Codebase -> a) -> Assertion
            same what f =
              assertEqual
                (what <> "\n" <> T.unpack source)
                (f original.codebase)
                (f reloaded.codebase)
        same "names" (.names)
        same "typeNames" (.typeNames)
        same "conNames" (.conNames)
        same "fieldNames" (.fieldNames)
        same "units" (.units)
        same "charts" (.charts)
        -- The shadowed root name needs its leading dot inside the block.
        (".size" `T.isInfixOf` source) @? T.unpack source
        -- A prelude term is referenced by name, never exported.
        ("let km" `T.isInfixOf` source) @?= False
        -- Every declared type is named, none left as a hash.
        ("#" `T.isInfixOf` source) @?= False
    , testCase ":export of a namespace, of nothing, and with a pending scratch" $ do
        s <- either (assertFailure . T.unpack) pure (sessionP exportScript)
        expecting (runLinesP (exportScript ++ [":export orbital.kepler"])) $ \outs ->
          T.lines (last outs)
            @?= ["use " <> u | u <- stdlibDefaultUses]
              ++ [ "namespace orbital"
                 , "  namespace kepler"
                 , "    let anomaly = \\e -> \\x -> x + e * x"
                 , "    let viaParent = orbital.size * 2"
                 ]
        runLinesP [":export"] @?= Right []
        case exportSource s{scratch = []} (Just "nowhere") of
          Right t -> t @?= ""
          Left err -> assertFailure (T.unpack err)
        expecting (runLinesP (exportScript ++ ["let pending = 1", ":export mechanics"])) $ \outs ->
          last (T.lines (last outs))
            @?= "-- not exported: 1 pending definitions (:add or :update them first)"
        expectError (runLinesP [":export a b c"]) "usage: :export"
        -- A single word that is no namespace is a file when it looks like a
        -- path, which only the REPL writes; a bare word is a misspelt namespace.
        expectError (runLinesP [":export out.metron"]) "only the REPL writes files"
        expectError (runLinesP [":export dir/out"]) "only the REPL writes files"
        expectError
          (runLinesP [":export orbitl"])
          "`orbitl` is not a namespace; to write a file give a path like orbitl.metron"
        fmap fst (exportRequest s ["orbitl"])
          @?= Left
            "`orbitl` is not a namespace; to write a file give a path like orbitl.metron"
        expectError
          (runLinesP [":export nowhere out.metron"])
          "`nowhere` is not a namespace"
        fmap fst (exportRequest s ["out.metron"]) @?= Right (Just "out.metron")
        fmap fst (exportRequest s ["orbital", "out.metron"])
          @?= Right (Just "out.metron")
        fmap snd (exportRequest s ["orbital", "out.metron"])
          @?= exportSource s (Just "orbital")
    , testCase ":export refuses a definition on a version no name points at"
        $ expectError
          ( runLinesP
              [ "let x = 5"
              , "let y = x + 1"
              , ":add"
              , "let x = 6"
              , ":update --no-upgrade"
              , ":unname x"
              , ":export"
              ]
          )
          "cannot export: `y` uses"
    , testCase "lexing: a dot not glued to a value is an absolute name" $ do
        toks ".km" @?= Right [TAbs "km"]
        toks "2 .km" @?= Right [L.TNum 2, TAbs "km"]
        toks "b.mass" @?= Right [TIdent "b", TField "mass"]
        toks ".orbital.period" @?= Right [TAbs "orbital", TField "period"]
    , testCase "units and types across namespaces" $ do
        let setup =
              [ multiline ["namespace orbital", "  unit au = 149597870700 m"]
              , ":add"
              , multiline
                  [ "namespace orbital"
                  , "  data Orbit = Orbit {radius :: Num au}"
                  , "  let one = 1 au"
                  ]
              , "data Pair = Pair orbital.Orbit orbital.Orbit"
              ]
        runLinesP (setup ++ ["2 orbital.au", "orbital.one to km", "3 .si.km"])
          @?= Right ["added orbital.au", "2 orbital.au", "149597870.7 km", "3 km"]
        expecting (runLinesP (setup ++ [":add", ":view Pair", ":edit orbital.Orbit"])) $ \outs ->
          lastN 3 outs
            @?= [ "data Pair = Pair orbital.Orbit orbital.Orbit"
                , "namespace orbital"
                , "  data Orbit = Orbit {radius :: Num m}"
                ]
    , testCase "a dotted name is plain in the highlighter" $ do
        s <- either (assertFailure . T.unpack) pure (sessionP orbitalSetup)
        R.highlight (R.namesOf s) "orbital.period 2" @?= "orbital.period 2"
    ]
