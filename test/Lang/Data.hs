-- | Data types and records.
module Lang.Data (
  dataTests,
) where

import Data.Map.Strict qualified as Map (lookup, size)
import Data.Maybe (fromMaybe)
import Data.Text qualified as T (isInfixOf, isPrefixOf, unpack)
import Lang.Common (
  evalP,
  runLinesP,
  seeded,
  sessionP,
  typeOfTextP,
 )
import Metron.Builtin (
  boolHash,
  builtinDefs,
  listDef,
  listHash,
  maxTupleArity,
  pairDef,
  pairHash,
  tupleArity,
  tupleHash,
 )
import Metron.Codebase (
  Codebase (conNames, typeDefs, typeNames),
  lookupTypeName,
 )
import Metron.Core (showHash)
import Metron.Driver (Session (codebase))
import Metron.Hash (hashHex)
import Metron.Parser (parseProgram, parseType)
import Metron.Syntax qualified as S (
  DataDecl (constructors, name, params, structural),
  Name (text),
  Statement (SData),
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

-- Tuples, lists and case --------------------------------------------------------------
--
-- Design §2.3, §5.1: Con and Case replaced If and the boolean literal.

dataTests :: TestTree
dataTests =
  testGroup
    "data"
    [ testCase "tuples: construction, types, fst and snd, equality" $ do
        evalP "(1, 2 m)" @?= Right ["(1, 2 m)"]
        typeOfTextP "(1, 2 m, true)" @?= Right "(Num, Num m, Bool)"
        evalP "fst (3, 4)" @?= Right ["3"]
        evalP "snd (3, 4 s)" @?= Right ["4 s"]
        evalP "(1, 2) == (1, 2)" @?= Right ["true"]
        evalP "(1, 2) == (1, 3)" @?= Right ["false"]
        typeOfTextP "fst" @?= Right "forall a b. (a, b) -> a"
    , testCase "lists: literals, cons, the prelude functions, laziness" $ do
        evalP "{1, 2, 3}" @?= Right ["{1, 2, 3}"]
        evalP "1 : {2, 3}" @?= Right ["{1, 2, 3}"]
        typeOfTextP "{1 m, 2 m}" @?= Right "{Num m}"
        evalP "map (\\x -> x * 2) {1, 2, 3}" @?= Right ["{2, 4, 6}"]
        evalP "length (range 1 10)" @?= Right ["10"]
        evalP "foldl (\\a b -> a + b) (0 m) {1 m, 2 m, 3 m}" @?= Right ["6 m"]
        evalP "zip {1, 2} {true, false}" @?= Right ["{(1, true), (2, false)}"]
        evalP "reverse (range 1 5)" @?= Right ["{5, 4, 3, 2, 1}"]
        evalP "filter (\\x -> x > 2) (range 1 5)" @?= Right ["{3, 4, 5}"]
        evalP "{1, 2} == {1, 2, 3}" @?= Right ["false"]
        typeOfTextP "map" @?= Right "forall a b. (a -> b) -> {a} -> {b}"
        typeOfTextP "zip" @?= Right "forall a b. {a} -> {b} -> {(a, b)}"
        -- a cons cell's tail is a thunk: an error in it surfaces only when walked
        evalP "fst (case 1 : {1 / 0} of {} -> (0, 0); x : _ -> (x, 0))" @?= Right ["1"]
    , testCase
        "case: one constructor deep, exhaustive, canonical order; _ and variables fill in"
        $ do
          evalP "case (1, 2) of (a, b) -> a + b" @?= Right ["3"]
          evalP "case {1, 2} of {} -> 0; x : _ -> x" @?= Right ["1"]
          runLinesP
            [ "let f xs = case xs of {} -> 0; x : rest -> x + f rest"
            , "f (range 1 100)"
            , ":view f"
            ]
            @?= Right ["5050", "f = \\xs -> case xs of {} -> 0; x : rest -> x + f rest"]
          evalP "case true of true -> 1; false -> 2" @?= Right ["1"]
          evalP "case {1} of {} -> 0; xs -> length xs" @?= Right ["1"]
          evalP "(case {1, 2} of {} -> 0; x : _ -> x) + 1" @?= Right ["2"]
          evalP "if true then 1 else 2" @?= Right ["1"]
          runLinesP ["let g c = if c then 1 else 2", ":view g", ":core g"]
            @?= Right
              ["g = \\c -> if c then 1 else 2", "g = \\(c : Bool) -> if c then 1.0 else 2.0"]
          case evalP "case 5 of x -> x + 1" of
            Left err -> T.isInfixOf "at least one constructor pattern" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalP "case {1} of {} -> 0" of
            Left err -> T.isInfixOf "does not cover Cons" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalP "case (1, 2) of (a, b) -> a; {} -> 0" of
            Left err -> T.isInfixOf "does not belong" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalP "if 1 then 2 else 3" of
            Left err -> T.isInfixOf "the condition of `if` must be a Bool" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "case alternatives as a layout block"
        $ runLinesP
          [ "let sumList xs = case xs of\n  {} -> 0\n  x : rest -> x + sumList rest"
          , "sumList {1, 2, 3}"
          ]
          @?= Right ["6"]
    , testCase "a state as a pair of vectors with different dimensions"
        $ runLinesP
          [ "let state = ([7000, 0, 0] km, [0, 7.5, 0] km/s)"
          , "case state of (r, v) -> norm v"
          , ":type state"
          ]
          @?= Right ["7.5 km s^-1", "(Vec 3 m, Vec 3 (m/s))"]
    , testCase "declared types: constructors, case, types, printing" $ do
        runLinesP
          [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
          , "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"
          , "area (Rect (3 m) (4 m))"
          , ":type Circle"
          , ":type area"
          , "Rect (1 m) (2 m)"
          , "map area {Circle (1 m), Rect (1 m) (2 m)}"
          , ":type {Circle (1 m)}"
          , ":view Shape"
          , ":edit Shape"
          , ":scratch"
          ]
          @?= Right
            [ "12 m^2"
            , "Num m -> Shape"
            , "Shape -> Num (m^2)"
            , "Rect (1 m) (2 m)"
            , "{3.1415926535897932384… m^2, 2 m^2}"
            , "{Shape}"
            , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
            , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
            , "pending: data Shape"
            , "pending: area"
            ]
        -- A constructor is a function: partial application and bare use.
        runLinesP
          [ "data Maybe a = Nothing | Just a"
          , "map Just {1, 2}"
          , "let fromMaybe d m = case m of Nothing -> d; Just x -> x"
          , "fromMaybe 0 (Just 5)"
          , "fromMaybe 0 Nothing"
          , ":type fromMaybe"
          , ":type Nothing"
          ]
          @?= Right
            [ "{Just 1, Just 2}"
            , "5"
            , "0"
            , "forall a. a -> Maybe a -> a"
            , "forall a. Maybe a"
            ]
    , testCase "declared types: parameters take their kinds from use; recursion" $ do
        runLinesP
          [ "data Q d = Q (Num d) (Num d)"
          , "let lo q = case q of Q a _ -> a"
          , "lo (Q (1 m) (2 m))"
          , ":type Q"
          , ":type lo"
          , "data V n = V (Vec n m) (Vec n (m/s))"
          , ":type V"
          , "data Tree a = Leaf | Node (Tree a) a (Tree a)"
          , "let sumTree z t = case t of Leaf -> z; Node l x r -> sumTree z l + x + sumTree z r"
          , "sumTree (0 kg) (Node (Node Leaf (1 kg) Leaf) (2 kg) (Node Leaf (3 kg) Leaf))"
          , ":type sumTree"
          , ":view Tree"
          , "data Body = Body (Num kg) (Vec 3 m) (Vec 3 (m/s))"
          , "let mass b = case b of Body m _ _ -> m"
          , "mass (Body (5 kg) ([1,2,3] km) ([4,5,6] km/s))"
          , "data E = E (Num (kg*m^2/s^2)) (Num N) (Num (m/s²)) (Point degC) Bool (Num, {Num m})"
          , ":view E"
          ]
          @?= Right
            [ "1 m"
            , "forall d. Num d -> Num d -> Q d"
            , "forall d. Q d -> Num d"
            , "forall n. Vec n m -> Vec n (m/s) -> V n"
            , "6 kg"
            , "forall s d. Tensor s d -> Tree (Tensor s d) -> Tensor s d"
            , "data Tree a = Leaf | Node (Tree a) a (Tree a)"
            , "5 kg"
            , "data E = E (Num (kg*m^2/s^2)) (Num (kg*m/s^2)) (Num (m/s^2)) (Point degC) Bool (Num, {Num m})"
            ]
    , testCase "declared types: == and /= when every field compares" $ do
        runLinesP
          [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
          , "Circle (1 m) == Circle (1 m)"
          , "Circle (1 m) == Circle (100 cm)"
          , "Circle (1 m) == Circle (2 m)"
          , "Circle (1 m) == Rect (1 m) (1 m)"
          , "Rect (1 m) (2 m) /= Rect (1 m) (2 m)"
          , "{Circle (1 m)} == {Circle (1 m)}"
          , "(Circle (1 m), true) == (Circle (1 m), false)"
          , "data Maybe a = Nothing | Just a"
          , "Just 1 == Just 1"
          , "Nothing == Just 1"
          , "Just (Circle (1 m)) == Just (Circle (1 m))"
          , "Just {1, 2} /= Just {1, 2, 3}"
          , ":type \\x -> Just x == Nothing"
          ]
          @?= Right
            [ "true"
            , "true"
            , "false"
            , "false"
            , "false"
            , "true"
            , "false"
            , "true"
            , "false"
            , "true"
            , "true"
            , "Num -> Bool"
            ]
        -- Recursive types: the self occurrence is the instance being derived.
        runLinesP
          [ "data Tree a = Leaf | Node (Tree a) a (Tree a)"
          , "let t = Node (Node Leaf (1 kg) Leaf) (2 kg) Leaf"
          , "t == Node (Node Leaf (1 kg) Leaf) (2 kg) Leaf"
          , "t == Node (Node Leaf (1 kg) Leaf) (2 kg) (Node Leaf (3 kg) Leaf)"
          , "t == Node Leaf (2 kg) Leaf"
          , "Leaf == Node Leaf 1 Leaf"
          , "data Pair a b = Pair a b"
          , "Pair 1 2 == Pair 1 2"
          , "Pair 1 (2 m) == Pair 1 (3 m)"
          , "Pair (Leaf, true) {1} == Pair (Leaf, true) {1}"
          , -- a nested type: the recursion is at another argument
            "data Nest a = Flat a | Deep (Nest (a, a))"
          , "Deep (Flat (1, 2)) == Deep (Flat (1, 2))"
          , "Deep (Flat (1, 2)) == Flat 1"
          , -- a parameter no field compares asks nothing of its argument
            "data Tag a = Tag | Wrap (Tag (a -> a))"
          , "Wrap Tag == Wrap Tag"
          ]
          @?= Right
            [ "true"
            , "false"
            , "false"
            , "false"
            , "true"
            , "false"
            , "true"
            , "true"
            , "false"
            , "true"
            ]
        -- Uncertain fields compare as numbers do.
        runLinesP
          [ "data Shape = Circle (Num m)"
          , "let c = Circle (1 m ± 1 mm)"
          , "c == c"
          , "c == Circle (2 m)"
          ]
          @?= Right ["true", "false"]
        let refused src needle = case runLinesP src of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        refused
          ["data F = F (Num -> Num)", "F (\\x -> x) == F (\\x -> x)"]
          "no equality on F"
        refused
          ["data H = H Num | G (Num, Num -> Num)", "H 1 == H 1"]
          "no equality on H"
        refused
          ["data Maybe a = Nothing | Just a", "Just (\\x -> x + 1) == Nothing"]
          "no equality on Num -> Num"
    , testCase "records: named fields, construction, access, update, printing" $ do
        runLinesP
          [ "data Body = Body {mass :: Num kg, pos :: Vec 3 m, vel :: Vec 3 (m/s)}"
          , "let b = Body {mass = 5 kg, pos = [1,2,3] km, vel = [4,5,6] km/s}"
          , "b.mass"
          , ":type b.pos"
          , "let b2 = b {vel = [0,0,0] m/s, mass = 6 kg}"
          , "b2"
          , "let kinetic b = 0.5 * b.mass * norm b.vel ^ 2"
          , ":type kinetic"
          , ":view kinetic"
          , "let bump dv b = b {vel = b.vel + dv}"
          , "(bump ([1,1,1] m/s) b).vel"
          , ":view bump"
          , -- a field name never captures a variable of the same name
            "let vel = [9,9,9] m/s"
          , "(b {vel = vel}).vel"
          , ":view Body"
          , "data Pair a b = Pair {first :: a, second :: b}"
          , "(Pair {first = 1, second = 2 m}).second"
          , "(Pair 1 true).first"
          , ":type Pair"
          ]
          @?= Right
            [ "5 kg"
            , "Vec 3 m"
            , "Body {mass = 6 kg, pos = [1, 2, 3] km, vel = [0, 0, 0] m s^-1}"
            , "Body -> Num (kg*m^2/s^2)"
            , "kinetic = \\b -> 0.5 * (case b of Body mass _ _ -> mass) * norm (case b of Body _ _ vel -> vel)^2"
            , "[4001, 5001, 6001] m s^-1"
            , "bump = \\dv -> \\b -> case b of Body mass pos vel -> Body mass pos ((case b of Body _ _ vel' -> vel') + dv)"
            , "[9, 9, 9] m s^-1"
            , "data Body = Body {mass :: Num kg, pos :: Vec 3 m, vel :: Vec 3 (m/s)}"
            , "2 m"
            , "1"
            , "forall a b. a -> b -> Pair a b"
            ]
        let refused src needle = case runLinesP src of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
            body = "data Body = Body {mass :: Num kg, pos :: Vec 3 m}"
        refused [body, "Body {mass = 1 kg}"] "missing field pos"
        refused
          [body, "Body {mass = 1 kg, pos = [0,0,0] m, mass = 2 kg}"]
          "field `mass` is given twice"
        refused
          [body, "let b = Body {mass = 1 kg, pos = [0,0,0] m}", "b {nope = 1}"]
          "unknown field `nope`"
        refused
          [body, "let b = Body {mass = 1 kg, pos = [0,0,0] m}", "b.nope"]
          "unknown field `nope`"
        refused
          [body, "data P = P {x :: Num}", "P {mass = 1 kg}"]
          "`P` has no field `mass`"
        refused
          [body, "data P = P {x :: Num}", "P {x = 1, mass = 1 kg}"]
          "field `mass` belongs to another type"
        refused
          ["data E = A {x :: Num} | B {y :: Num}"]
          "field names need a type with one constructor"
        refused ["data E = E {x :: Num, x :: Num}"] "field `x` appears twice"
        -- braces after a constructor are a record only with `{name ::`; otherwise a list type
        runLinesP ["data Hs = G {Num} | N", "G {1, 2}", "G {}", ":type G", ":view Hs"]
          @?= Right ["G {1, 2}", "G {}", "{Num} -> Hs", "data Hs = G {Num} | N"]
        refused [body, "mass"] "is a field; write it after a value"
        -- field labels can be removed, with their dot; the type and its
        -- values then print positionally, since a record needs every name
        runLinesP
          [body, ":add", ":unname .mass", ":view Body", "Body (1 kg) ([0, 0, 0] m)"]
          @?= Right
            [ "added Body"
            , "removed the label `.mass`"
            , "data Body = Body (Num kg) (Vec 3 m)"
            , "Body (1 kg) ([0, 0, 0] m)"
            ]
        -- a glued .name is a field, so composition needs spaces
        evalP "(sqrt . abs) (-16)" @?= Right ["4"]
        case evalP "(sqrt.abs) (-16)" of
          Left err -> T.isInfixOf "unknown field `abs`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "record values print with their field names and read back" $ do
        let decls =
              [ "data Body = Body {mass :: Num kg, pos :: Vec 3 m}"
              , "data Pair a b = Pair {first :: a, second :: b}"
              , "data Maybe a = Nothing | Just a"
              , "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
              ]
            -- each value as it prints, and as the printed text prints again
            cases =
              [
                ( "Pair {first = Body {mass = 1 kg, pos = [1,2,3] m}, second = Just (Body {mass = -2 kg, pos = [0,0,0] km})}"
                , "Pair {first = Body {mass = 1 kg, pos = [1, 2, 3] m}, second = Just (Body {mass = -2 kg, pos = [0, 0, 0] km})}"
                )
              , -- a record inside a positional constructor keeps its parentheses

                ( "Just (Body {mass = 5 kg, pos = [0,0,0] m})"
                , "Just (Body {mass = 5 kg, pos = [0, 0, 0] m})"
                )
              , -- a positional value inside a record needs none

                ( "Pair {first = Rect (1 m) (2 m), second = Nothing}"
                , "Pair {first = Rect (1 m) (2 m), second = Nothing}"
                )
              ,
                ( "Pair (Circle (1 m)) (1, 2 m)"
                , "Pair {first = Circle (1 m), second = (1, 2 m)}"
                )
              , ("{Body (5 kg) ([0,0,0] m)}", "{Body {mass = 5 kg, pos = [0, 0, 0] m}}")
              ,
                ( "Pair (Pair 1 true) (-3 m s^-2)"
                , "Pair {first = Pair {first = 1, second = true}, second = -3 m s^-2}"
                )
              ]
        mapM_
          ( \(src, printed) -> do
              runLinesP (decls ++ [src]) @?= Right [printed]
              runLinesP (decls ++ [printed]) @?= Right [printed]
          )
          cases
        -- a type mixing a named constructor with a positional one is refused
        -- (field names need one constructor), so a record is never partly named
        -- except by :unname, as above
        case runLinesP ["data E = A {x :: Num} | B Num"] of
          Left err ->
            T.isInfixOf "field names need a type with one constructor" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "rank in type syntax: a data declaration can index by a shape's rank" $ do
        runLinesP
          [ "data Idx s = Idx (Vec (rank s))"
          , ":type Idx"
          , ":view Idx"
          , "data Tagged s d = Tagged (Tensor s d) (Vec (rank s))"
          , ":type Tagged"
          , "Tagged [1, 2; 3, 4] [0, 1]"
          , ":type Tagged [1, 2; 3, 4] [0, 1]"
          , "let tagged t idx = Tagged t idx"
          , ":type tagged"
          ]
          @?= Right
            [ "forall s. Vec (rank s) -> Idx s"
            , "data Idx s = Idx (Vec (rank s))"
            , "forall s d. Tensor s d -> Vec (rank s) -> Tagged s d"
            , "Tagged [1, 2; 3, 4] [0, 1]"
            , "Tagged [2, 2] 1"
            , "forall s d. Tensor s d -> Vec (rank s) -> Tagged s d"
            ]
        let refused src needle = case runLinesP src of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        refused
          [ "data Tagged s d = Tagged (Tensor s d) (Vec (rank s))"
          , "Tagged [1, 2; 3, 4] [0]"
          ]
          "lengths differ: 2 and 1"
        refused ["data R rank = R (Vec rank)"] "cannot be a parameter"
        refused ["data R s = R (rank s)"] "rank s is a length, not a type"
        refused ["data R s = R (Vec rank)"] "rank takes a shape"
        refused ["data R n = R (Vec (rank n n))"] "rank takes one shape"
    , testCase "declared types: identity is the stamped or structural definition" $ do
        s <-
          either (assertFailure . T.unpack) pure
            $ sessionP
              [ "data P a b = P a b"
              , "data P2 a b = Q2 a b"
              , "structural data S1 a b = S1 a b"
              , "structural data S2 a b = S2 a b"
              , ":add"
              ]
        let cb = s.codebase
            tyOf n = fromMaybe (error (T.unpack n)) (lookupTypeName n cb)
        -- The same shape under another name is another type; structurally it is the same one.
        (tyOf "P" == tyOf "P2") @?= False
        tyOf "S1" @?= tyOf "S2"
        -- Both names and all four constructors stay bound, beside the library's.
        Map.size cb.typeNames - Map.size seeded.codebase.typeNames @?= 4
        Map.size cb.conNames - Map.size seeded.codebase.conNames @?= 4
        runLinesP
          ["data P a b = P a b", "P 1 2", "structural data T a = T a", "T (T 1)"]
          @?= Right ["P 1 2", "T (T 1)"]
    , testCase "the built-in types are the structural declarations of their shape" $ do
        s <-
          either (assertFailure . T.unpack) pure
            $ sessionP
              [ "structural data B = F | T"
              , "structural data P2 a b = P2 a b"
              , "structural data T3 a b c = T3 a b c"
              , "structural data L a = N | C a (L a)"
              , ":add"
              ]
        let tyOf n = fromMaybe (error (T.unpack n)) (lookupTypeName n s.codebase)
        tyOf "B" @?= boolHash
        tyOf "P2" @?= pairHash
        tyOf "T3" @?= tupleHash 3
        tyOf "L" @?= listHash
        Map.lookup (tyOf "L") s.codebase.typeDefs @?= Just listDef
        -- Every hash a tuple can have is recognised, and none other.
        map (tupleArity . tupleHash) [2 .. maxTupleArity]
          @?= map Just [2 .. maxTupleArity]
        tupleArity boolHash @?= Nothing
        builtinDefs pairHash @?= Just pairDef
        -- Fixed by the declarations and the encoding alone: a change to either
        -- re-hashes every boolean, tuple and list in every store.
        map hashHex [boolHash, pairHash, listHash, tupleHash 3]
          @?= [ "da4c961ee015cf46c8d0b895fc0389167cde6d607e55d99711e5009037fd9f9f"
              , "eb18ffa4c555a267cf8685c34eddcc91173f39f891d6f8416ad22cc335a622ef"
              , "6505bc4bf900d90b75c0aebc93ca31d01663e8ac136d080fcb556320b96358f7"
              , "1ffef3bbc6c59ff71b8b1292db64185e97e96e78ef1002befa2efbf4e746df9e"
              ]
        map showHash [boolHash, pairHash, listHash] @?= ["#r969c", "#tccfv", "#ck2ro"]
    , testCase "declared types: what is refused" $ do
        let refused src needle = case runLinesP src of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        refused ["data Bad a = Bad (Num a) a"] "used both as a dimension and as a type"
        refused ["data Vec = V"] "is a built-in type"
        refused ["data Dup = A | A"] "constructor `A` appears twice"
        refused ["data Dup a a = D a"] "parameter `a` appears twice"
        refused ["data W = W Nope"] "unknown type `Nope`"
        refused
          ["data Maybe a = Nothing | Just a", "data W = W Maybe"]
          "`Maybe` takes 1 argument, given 0"
        refused
          ["data W = W (Num furlong)"]
          "`furlong` is not a unit or a dimension variable"
        refused
          ["data W = W (Vec [m])"]
          "a length is a number, a parameter, a frame's or a space's axes, or rank s"
        refused
          ["data W = W (Vec m)"]
          "`m` is a unit, not a length: a vector's length comes first, Vec 3 m"
        refused
          ["data Maybe a = Nothing | Just a", "case Just 1 of Nothing -> 0"]
          "does not cover Just"
        refused
          ["data Maybe a = Nothing | Just a", "case Just 1 of Nothing -> 0; Just -> 1"]
          "has 1 fields"
        refused
          ["data Shape = Circle (Num m)", "Circle 1"]
          "expected Num m, got Num"
        refused
          ["data Shape = Circle (Num m)", "Circle (1 m) (2 m)"]
          "Shape is not a function"
        -- `1 m` is an application too: the unit is the second argument, and
        -- the type error says how to write the quantity
        refused
          ["data Shape = Circle (Num m)", "Circle 1 m"]
          "hint: 1 and `m` are two separate arguments here; a quantity in argument position needs parentheses: (1 m)"
        refused
          ["data Shape = Circle (Num m)", "let c = Circle 1 m"]
          "hint: 1 and `m` are two separate arguments"
        refused ["let f a b = a + b", "f [1,2] km 3"] "parentheses: (the vector km)"
        -- a bound name is not a unit, so no hint
        case runLinesP ["let g m = sqrt 2 m"] of
          Left err -> not (T.isInfixOf "hint:" err) @? T.unpack err
          Right v -> assertFailure (show v)
        -- :add refuses a type that exists with another definition.
        refused
          [ "data Shape = Circle (Num m)"
          , ":add"
          , "data Shape = Circle (Num s)"
          , ":add"
          ]
          "already exists with a different definition"
    , testCase "declared types: names are labels" $ do
        let outs =
              runLinesP
                [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
                , ":add"
                , ":unname Circle"
                , "Rect (1 m) (2 m)"
                , ":view Shape"
                , ":unname Shape"
                , ":type Rect"
                ]
        case outs of
          Right [_, removed, rect, viewed, _, ty] -> do
            removed @?= "removed the label `Circle`"
            rect @?= "Rect (1 m) (2 m)"
            T.isPrefixOf "data Shape = #" viewed @? T.unpack viewed
            T.isPrefixOf "Num m -> Num m -> #" ty @? T.unpack ty
          other -> assertFailure (show other)
    , testCase
        "constructors and definitions share one namespace; the newer label wins"
        $ do
          runLinesP
            [ "1 T"
            , "data Temp = T (Num K)"
            , "T (300 K)"
            , ":type T"
            , "let T = 2"
            , "T + 1"
            ]
            @?= Right ["1 T", "T (300 K)", "Num K -> Temp", "3"]
          case runLinesP ["data Temp = T (Num K)", "1 T"] of
            Left err ->
              T.isInfixOf "is a function, Num K -> Temp, not a unit or a chart" err
                @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "the type grammar" $ do
        let ok src = case parseType src of
              Left err -> assertFailure (T.unpack err)
              Right _ -> pure ()
        mapM_
          ok
          [ "Num m"
          , "Vec 3 m -> Maybe a"
          , "(a, Num (kg*m^2/s^2))"
          , "{Tree a}"
          , "Point (Vec 3 m)"
          , "Tensor [2, 3] d"
          , "Num"
          ]
        case parseProgram "structural data Pair a b = Pair a b | Other (Num m)" of
          Right [S.SData d] -> do
            d.name.text @?= "Pair"
            map (.text) d.params @?= ["a", "b"]
            map (\(c, fs) -> (c.text, length fs)) d.constructors
              @?= [("Pair", 2), ("Other", 1)]
            d.structural @?= True
          other -> assertFailure (show other)
    ]
