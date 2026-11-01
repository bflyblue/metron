-- | The REPL.
module Lang.Repl (
  replTests,
) where

import Data.Text (Text)
import Data.Text qualified as T (
  breakOn,
  drop,
  dropWhile,
  intercalate,
  length,
  null,
  pack,
  singleton,
  splitOn,
  unpack,
 )
import Lang.Common (
  coloured,
  completeAt,
  evalP,
  grey',
  keyword',
  red',
  replacements,
  runLinesP,
  seeded,
  sessionP,
  shapeArea,
  shapeDecl,
  toks,
  type',
  unit',
 )
import Metron.Lexer (Token (TIdent, TOp, TSqrt, TSup))
import Metron.Parser (parseProgram)
import Metron.Repl qualified as R (
  Completion (Completion, display),
  Continuation (Block, Trailing, Unclosed),
  Kind (
    Caret,
    Echo,
    Note,
    Plain,
    Problem,
    Signature,
    Source,
    Type,
    Value
  ),
  classify,
  completions,
  continuation,
  echoInput,
  highlight,
  highlightType,
  loadsFile,
  namesOf,
  needsMore,
  paint,
  render,
  splitUnits,
 )
import Metron.Unicode qualified as U (
  completions,
  lookupName,
  matching,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

{- | The ASCII spellings of design §2.8, keyed by their unicode form, for the
agreement test: a unicode entry must lex as its ASCII spelling does.
-}
asciiSpellings :: [(Text, Text)]
asciiSpellings =
  [ ("λ", "\\")
  , ("→", "->")
  , ("⊗", "*")
  , ("·", "@")
  , ("⋅", "@")
  , ("×", "><")
  , ("⊙", ".*")
  , ("⊘", "./")
  , ("÷", "/")
  , ("≤", "<=")
  , ("≥", ">=")
  , ("≠", "/=")
  , ("∨", "||")
  , ("¬", "not")
  , ("∧", "/\\")
  , ("⋆", "star")
  , ("±", "+-")
  , ("±σ", "+-s")
  , ("°C", "degC")
  , ("°F", "degF")
  , ("∘", ".")
  , ("π", "pi")
  , ("°", "deg")
  , ("″", "arcsec")
  , ("′", "arcmin")
  ]

-- | Remove every @ESC [ … m@ sequence.
stripSgr :: Text -> Text
stripSgr t = case T.breakOn "\ESC[" t of
  (before, rest)
    | T.null rest -> before
    | otherwise -> before <> stripSgr (T.drop 1 (T.dropWhile (/= 'm') rest))

replTests :: TestTree
replTests =
  testGroup
    "repl"
    [ testCase "commands complete at the start of a line" $ do
        let cs = replacements seeded ":l"
        all (`elem` cs) [":ls", ":load"] @? show cs
        all (":l" `isPrefixOfS`) cs @? show cs
        replacements seeded "  :up" @?= [":update", ":upgrade"]
        filter (":" `isPrefixOfS`) (replacements seeded "x :l") @?= []
    , testCase ":set and :colour complete their arguments" $ do
        replacements seeded ":set un" @?= ["unicode"]
        replacements seeded ":set " @?= ["precision", "sigma", "unicode"]
        replacements seeded ":set unicode o" @?= ["on", "off"]
        replacements seeded ":colour of" @?= ["off"]
        R.completions seeded (reverse ":set ") "un"
          @?= [R.Completion "unicode" "unicode" True]
    , testCase "names complete from the session: units, constructors, keywords" $ do
        -- The prelude's prefixed units are spelled with the SI symbol: km, kN.
        let ks = replacements seeded "3 k"
        all (`elem` ks) ["km", "kN", "kJ", "kPa", "kat"] @? show ks
        all ("k" `isPrefixOfS`) ks @? show ks
        replacements seeded "x + 3k" @?= ks
        "where" `elem` replacements seeded "f x whe" @? "where"
        replacements seeded "f x " @?= []
        let s =
              either (error . T.unpack) id
                $ sessionP [shapeDecl]
        replacements s "area (Ci" @?= ["Circle"]
        "Shape" `elem` replacements s ":view Sh" @? "Shape"
    , testCase "fields complete after a dot" $ do
        let s =
              either (error . T.unpack) id
                $ sessionP
                  [ "data Body = Body {mass :: Num kg, vel :: Vec 3 (m/s)}"
                  , "let b = Body (5 kg) ([0, 0, 1] m/s)"
                  ]
        completeAt s "b.ma" @?= Just ("b", [R.Completion ".mass" "mass" True])
        map (.display) (R.completions s "b" ".ma") @?= ["mass"]
        -- Every field completes, the library's among them: Cov2's, and
        -- astro's State, Body, Elements and Transfer.
        map (.display) (R.completions s "b" ".")
          @?= [ "a"
              , "argp"
              , "dv1"
              , "dv2"
              , "dv3"
              , "e"
              , "epoch"
              , "flattening"
              , "i"
              , "j2"
              , "mass"
              , "mu"
              , "nu"
              , "pos"
              , "raan"
              , "radius"
              , "rate"
              , "rr"
              , "rv"
              , "tof"
              , "vel"
              , "vv"
              ]
    , testCase ":load completes file names" $ do
        completeAt seeded ":load fo" @?= Nothing
        R.loadsFile " :load " @? ":load"
        R.loadsFile ":edit --file /tm" @? ":edit --file"
        completeAt seeded ":edit --file fo" @?= Nothing
        not (R.loadsFile ":ls") @? ":ls"
        not (R.loadsFile ":edit fo") @? ":edit"
    , testCase "a backslash name completes from the unicode table only" $ do
        completeAt seeded "2 \\mu"
          @?= Just (reverse "2 ", [R.Completion "\x03BC" "\x03BC" False])
        replacements seeded "3 m \\pm" @?= ["±"]
        replacements seeded "3 m \\pms" @?= ["±σ"]
        replacements seeded "(\\Omega" @?= ["\x03A9"]
        completeAt seeded "m\\^2" @?= Just ("m", [R.Completion "²" "²" False])
        replacements seeded "s\\^-" @?= ["⁻"]
        replacements seeded "\\lam" @?= ["λ"]
        let os = replacements seeded "\\o"
        length os > 1 && all ("\\o" `isPrefixOfS`) os @? show os
        -- Nothing from the codebase: `kat` is a name, `\kat` is not an entry.
        replacements seeded "\\kat" @?= []
    , testCase
        "every unicode entry lexes as a documented ASCII spelling or is an identifier"
        $ sequence_
          [ agrees name u @? T.unpack ("\\" <> name <> " -> " <> u)
          | (name, u) <- U.completions
          ]
    , testCase "unicode lookup prefers an exact name" $ do
        U.lookupName "pm" @?= Just "±"
        map fst (U.matching "pm") @?= ["pm"]
        map fst (U.matching "pr") @?= ["prime"]
    , testCase "classify: errors, notes, signatures, values" $ do
        let block = "error at 1:5\n  3 m + 2 s\n      ^^^\n  cannot add a length to a time"
        map fst (R.classify (Left block)) @?= [R.Problem, R.Source, R.Caret, R.Problem]
        R.classify (Left "unknown name `x`") @?= [(R.Problem, "unknown name `x`")]
        R.classify (Right ["pending: data Shape", "added area"])
          @?= [(R.Note, "pending: data Shape"), (R.Note, "added area")]
        map
          fst
          ( R.classify
              (Right ["namespace std (812 names)"])
          )
          @?= [R.Note]
        map
          fst
          (R.classify (Right ["area : Shape -> Num (m^2)", "unit furlong : Unit m"]))
          @?= [R.Signature, R.Signature]
        map
          fst
          ( R.classify
              (Right ["12.566… m^2", "(1 m, 2 s)", "f = \\xs -> case xs of x : rest -> x"])
          )
          @?= [R.Value, R.Value, R.Value]
        -- A real error block keeps its text, line for line.
        case evalP "3 m + true" of
          Left err -> T.intercalate "\n" (map snd (R.classify (Left err))) @?= err
          Right v -> assertFailure (show v)
    , testCase "classify: the ≡ echo and a function type" $ do
        map fst (R.classify (Right ["  ≡ 3 m² + 4 m² -- hi", "(a → b) → {a} → {b}"]))
          @?= [R.Echo, R.Type]
        -- A later line of a multi-line definition is not a type.
        map fst (R.classify (Right ["    Rect w h -> w * h"])) @?= [R.Value]
        map fst (R.classify (Right ["`z` now also names #e21lk", "(input abandoned)"]))
          @?= [R.Note, R.Note]
    , testCase "splitUnits: the trailing unit of a value that does not lex" $ do
        R.splitUnits "12.566… m^2" @?= ("12.566… ", "m^2")
        R.splitUnits "[1, 2, 3] km s⁻¹" @?= ("[1, 2, 3] ", "km s⁻¹")
        R.splitUnits "9.81 m/s^2" @?= ("9.81 ", "m/s^2")
        R.splitUnits "293.15 K (point)" @?= ("293.15 ", "K (point)")
        -- Not a unit: types, booleans, constructors, bare numbers.
        mapM_
          (\t -> R.splitUnits t @?= (t, ""))
          [ "Num m -> Shape"
          , "true"
          , "Rect (1 m) (2 m)"
          , "42"
          , "Just 1"
          , "precision 15"
          , "a -> Maybe a -> a"
          ]
    , testCase "needsMore: brackets, trailing tokens, commands, comments" $ do
        let more = map R.needsMore
        more
          [ "let f x ="
          , "[1, 2,"
          , "case s of"
          , "f (3 m"
          , "x +"
          , "\\x ->"
          , "data Shape = Circle (Num m) |"
          , "λx →"
          , "f ∘"
          , "f ."
          , "3 m ±"
          , "if c then"
          , "let x = 1;"
          , "a `dot`"
          , "let f x = x\n  where"
          , "let f x = x + -- more to come\n  1 *"
          ]
          @?= replicate 16 True
        more
          [ "let f x = x"
          , "[1, 2; 3, 4]"
          , "x -- comment ("
          , "1 + 2 --"
          , ":ls ("
          , ":type \\x ->"
          , "b.mass"
          , "v.0"
          , "x == true"
          , "f (3 m))"
          , ""
          , "let f x =\n  x + 1"
          , "{- unclosed"
          ]
          @?= replicate 13 False
        R.continuation "f (3 m" @?= Just R.Unclosed
        R.continuation "case s of" @?= Just R.Block
        R.continuation "x +" @?= Just (R.Trailing "+")
        R.continuation "let f x =" @?= Just (R.Trailing "=")
        R.continuation "\\x →" @?= Just (R.Trailing "->")
    , testCase "needsMore: a block after of runs to a blank line" $ do
        let opening = "let area s = case s of"
            two = opening <> "\n  Circle r -> pi * r^2"
            three = two <> "\n  Rect w h -> w * h"
        map R.needsMore [opening, two, three] @?= [True, True, True]
        R.continuation three @?= Just R.Block
        -- The blank line ends it, here and for an input that would not parse.
        R.needsMore (three <> "\n") @?= False
        R.needsMore (three <> "\n   ") @?= False
        R.needsMore (opening <> "\n") @?= False
        R.needsMore "let xs = [1,\n" @?= False
        R.needsMore "let f x = y * 2 where\n  y = x + 1" @?= True
        -- The joined text parses as one input under the layout rule.
        runLinesP
          [ shapeDecl
          , three
          , ":type area"
          , "area (Rect (2 m) (3 m))"
          ]
          @?= Right
            [ "Shape -> Num (m^2)"
            , "6 m^2"
            ]
        runLinesP ["let f x = y * 2 where\n  y = x + 1", "f 3"]
          @?= Right ["8"]
        runLinesP ["let xs = [1,\n  2, 3]", "xs"] @?= Right ["[1, 2, 3]"]
    , testCase "highlight: keywords magenta, units cyan, the rest plain" $ do
        R.highlight names "let f x = 3 km + x"
          @?= keyword' "let" <> " f x = 3 " <> unit' "km" <> " + x"
        R.highlight names "if true then 2 s else 3 h"
          @?= keyword' "if"
            <> " "
            <> keyword' "true"
            <> " "
            <> keyword' "then"
            <> " 2 "
            <> unit' "s"
            <> " "
            <> keyword' "else"
            <> " 3 "
            <> unit' "h"
        -- A unicode spelling is coloured as the token it lexes to.
        R.highlight names "20 °C" @?= "20 " <> unit' "°C"
    , testCase "highlight: a data declaration, types and constructors yellow" $ do
        let decl = "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
            numM = type' "Num" <> " " <> unit' "m"
            expected =
              keyword' "data"
                <> " "
                <> type' "Shape"
                <> " = "
                <> type' "Circle"
                <> " ("
                <> numM
                <> ") | "
                <> type' "Rect"
                <> " ("
                <> numM
                <> ") ("
                <> numM
                <> ")"
        R.highlight (R.namesOf shapes) decl @?= expected
        -- Before the session knows it, as the scripted echo sees it.
        R.highlight names decl @?= expected
        R.highlight names "structural data Pair a b = Pair a b"
          @?= keyword' "structural"
            <> " "
            <> keyword' "data"
            <> " "
            <> type' "Pair"
            <> " a b = "
            <> type' "Pair"
            <> " a b"
    , testCase "paint: a signature's type, highlighted as a type" $ do
        R.paint (R.namesOf shapes) R.Signature "area : Shape -> Num (m^2)"
          @?= "area : "
            <> type' "Shape"
            <> " -> "
            <> type' "Num"
            <> " ("
            <> unit' "m"
            <> "^2)"
        R.paint names R.Signature "unit furlong : Unit m"
          @?= keyword' "unit" <> " furlong : " <> type' "Unit" <> " " <> unit' "m"
        -- A unit is cyan where a dimension goes: an argument, or in a product.
        R.paint names R.Signature "g : Num (kg·m/s²) -> Vec 3 (1/s)"
          @?= "g : "
            <> type' "Num"
            <> " ("
            <> unit' "kg"
            <> "·"
            <> unit' "m"
            <> "/"
            <> unit' "s"
            <> "²) -> "
            <> type' "Vec"
            <> " 3 (1/"
            <> unit' "s"
            <> ")"
        -- Type variables named like units stay plain where a type goes.
        R.paint names R.Type "(g → m) → {g}" @?= "(g → m) → {g}"
        R.highlightType names "g -> Num g"
          @?= "g -> " <> type' "Num" <> " " <> unit' "g"
        -- A data declaration's parameters are variables, as forall's are.
        R.highlight names "data Box d = Box (Num d)"
          @?= keyword' "data"
            <> " "
            <> type' "Box"
            <> " d = "
            <> type' "Box"
            <> " ("
            <> type' "Num"
            <> " d)"
    , testCase "paint: values, records, references, comments" $ do
        R.paint names R.Value "12.566… m^2" @?= "12.566… " <> unit' "m" <> "^2"
        R.paint names R.Value "[1, 2, 3] km s⁻¹"
          @?= "[1, 2, 3] " <> unit' "km" <> " " <> unit' "s" <> "⁻¹"
        R.paint names R.Value "293.15 K (point)"
          @?= "293.15 " <> unit' "K" <> " (point)"
        R.paint (R.namesOf bodies) R.Value "Body {mass = 5 kg, pos = [1, 2, 3] km}"
          @?= type' "Body"
            <> " {mass = 5 "
            <> unit' "kg"
            <> ", pos = [1, 2, 3] "
            <> unit' "km"
            <> "}"
        R.paint names R.Value "#a3f9k" @?= grey' "#a3f9k"
        R.paint names R.Value "#a3f9k.1  (current)"
          @?= grey' "#a3f9k.1" <> "  (current)"
        R.highlight names "x -- note" @?= "x " <> grey' "-- note"
        R.highlight names "x {- a -} + 1" @?= "x " <> grey' "{- a -}" <> " + 1"
        R.paint names R.Echo "  ≡ 3 m² + 4 m² -- hi"
          @?= "  "
            <> grey' "≡"
            <> " 3 "
            <> unit' "m"
            <> "² + 4 "
            <> unit' "m"
            <> "² "
            <> grey' "-- hi"
    , testCase "highlight: a variable named like a unit is plain where it is bound" $ do
        R.highlight
          (R.namesOf shapes)
          shapeArea
          @?= keyword' "let"
            <> " area s = "
            <> keyword' "case"
            <> " s "
            <> keyword' "of"
            <> " "
            <> type' "Circle"
            <> " r -> pi * r^2; "
            <> type' "Rect"
            <> " w h -> w * h"
        R.highlight names "\\s -> s + 1 h" @?= "\\s -> s + 1 " <> unit' "h"
        R.highlight names "3 m + 2 s" @?= "3 " <> unit' "m" <> " + 2 " <> unit' "s"
    , testCase "paint: an error block keeps its carets under the excerpt" $ case evalP "3 m + 2 s" of
        Right v -> assertFailure (show v)
        Left err -> do
          let painted = R.render True names (Left err)
          painted
            @?= [ red' "error at 1:7"
                , "  3 " <> unit' "m" <> " + 2 " <> unit' "s"
                , coloured "1;31" "        ^^^"
                , red' "  expected Num m, got Num s: dimensions differ by m/s"
                ]
          map stripSgr painted @?= T.splitOn "\n" err
          -- The visible columns of the excerpt and the carets are unchanged.
          map (T.length . stripSgr) painted @?= map T.length (T.splitOn "\n" err)
    , testCase "paint: what does not lex falls back to its kind" $ do
        R.paint names R.Value "3 m $ 4 km" @?= "3 m $ 4 " <> unit' "km"
        R.paint names R.Signature "x : Num m ?" @?= "x : " <> type' "Num m ?"
        R.paint names R.Source "  3 $ m" @?= "  3 $ m"
        R.paint names R.Note "pending: data Shape" @?= grey' "pending: data Shape"
        R.paint names R.Problem "error at 1:5" @?= red' "error at 1:5"
        R.paint names R.Caret "      ^^^" @?= coloured "1;31" "      ^^^"
        R.paint names R.Note "" @?= ""
        R.highlight names "3 $ m" @?= "3 $ m"
    , testCase "colour off changes nothing; the scripted echo" $ do
        let err = "error at 1:7\n  3 m + 2 s\n        ^^^\n  cannot add"
        R.render False names (Left err) @?= [err]
        R.render False names (Right ["a\nb", "c"]) @?= ["a\nb", "c"]
        R.echoInput False names "let x = 3 km" @?= "> let x = 3 km"
        R.echoInput True names "let x = 3 km"
          @?= coloured "1" "> " <> keyword' "let" <> " x = 3 " <> unit' "km"
        R.echoInput True names ":ls --units g" @?= coloured "1" "> " <> ":ls --units g"
        R.echoInput True names ":type 3 km"
          @?= coloured "1" "> " <> ":type 3 " <> unit' "km"
    , testCase "painting only adds escape codes" $ do
        let lines' =
              [ "let f x = 3 km + x"
              , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
              , "area : Shape -> Num (m^2)"
              , "12.566… m^2"
              , "Body {mass = 5 kg, pos = [1, 2, 3] km}"
              , "  ≡ λx → x -- hi"
              , "x -- note"
              , "#a3f9k.1  (current)"
              , "3 m $ 4 km"
              , "  3 $ m"
              , "20 °C"
              , "Ω and µ, folded"
              , "e\x0301 composes"
              , "a\tb"
              ]
            kinds =
              [ R.Plain
              , R.Note
              , R.Echo
              , R.Signature
              , R.Type
              , R.Value
              , R.Source
              , R.Problem
              , R.Caret
              ]
        sequence_
          [ stripSgr (R.paint names k l) @?= l
          | l <- lines'
          , k <- kinds
          ]
        mapM_ (\l -> stripSgr (R.highlight names l) @?= l) lines'
        mapM_ (\l -> stripSgr (R.echoInput True names l) @?= "> " <> l) lines'
        -- Everything the prelude lists, painted as the REPL would.
        case evalP ":ls --all" of
          Left e -> assertFailure (T.unpack e)
          Right outs -> do
            let painted = R.render True names (Right outs)
            map stripSgr painted @?= concatMap (T.splitOn "\n") outs
    ]
 where
  names = R.namesOf seeded
  shapes =
    either (error . T.unpack) id
      $ sessionP [shapeDecl]
  bodies =
    either (error . T.unpack) id
      $ sessionP ["data Body = Body {mass :: Num kg, pos :: Vec 3 km}"]
  isPrefixOfS p x = take (length p) x == p
  agrees name u
    | Just n <- lookup u superscripts =
        toks ("m" <> glued u) == Right [TIdent "m", TSup n]
          && isRight (evalP ("2" <> glued u))
          && evalP ("2" <> glued u) == evalP ("2^" <> T.pack (show n))
    | name == "sqrt" =
        -- A prefix operator where sqrt is an application (§7.3): same value.
        toks u == Right [TSqrt] && evalP "√9" == evalP "sqrt 9" && isRight (evalP "√9")
    | u `elem` ["·", "⋅"] =
        -- A token of its own, a product in a dimension (design §4.1), and
        -- in an expression the same program as @.
        toks ("a " <> u <> " b") == Right [TIdent "a", TOp "·", TIdent "b"]
          && isRight (parseProgram ("a " <> u <> " b"))
          && parseProgram ("a " <> u <> " b") == parseProgram "a @ b"
    | Just a <- lookup u asciiSpellings =
        let lexed = toks ("a " <> u <> " b")
         in isRight lexed && lexed == toks ("a " <> a <> " b")
    | otherwise =
        toks u == Right [TIdent u] || toks ("x" <> u) == Right [TIdent ("x" <> u)]
  superscripts = [(T.singleton c, n) | (c, n) <- zip "⁰¹²³⁴⁵⁶⁷⁸⁹" [0 ..]] ++ [("⁻", -1)]
  glued u = if u == "⁻" then "⁻¹" else u
  isRight = either (const False) (const True)
