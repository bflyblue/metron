-- | Whole inputs through the session, and soundness.
module Lang.EndToEnd (
  endToEndTests,
  soundnessTests,
) where

import Data.Text qualified as T (intercalate, isInfixOf, unpack)
import Lang.Common (
  desugarText,
  evalP,
  evalText,
  runLines,
  typeOfText,
 )
import Metron.Core (
  Fin (FZ),
  Lit (LTensor),
  Term (Lam, Lit, Pack, Var),
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end to end"
    [ testCase "1 + 4.5 is exact" $ evalText "1 + 4.5" @?= Right ["5.5"]
    , testCase "exact thirds" $ evalText "1/3 * 3" @?= Right ["1"]
    , testCase "repeating decimal"
        $ evalText "2/3" @?= Right ["0.66666666666666666666…"]
    , testCase "lambda" $ evalText "(\\x y -> x * y + 1) 3 4" @?= Right ["13"]
    , testCase "unicode lambda and operators"
        $ evalText "(λx → x ⊗ 2) 21" @?= Right ["42"]
    , testCase "if with booleans"
        $ evalText "if 1 < 2 && ¬false then 10 else 20" @?= Right ["10"]
    , testCase "superscript power" $ evalText "2³ + 2⁻¹" @?= Right ["8.5"]
    , testCase "section" $ evalText "(+ 1) 41" @?= Right ["42"]
    , testCase "projection"
        $ evalText "[1, 2, 3].1 + [[1, 2], [3, 4]].1.0" @?= Right ["5"]
    , testCase "elementwise arithmetic on tensors" $ do
        evalText "[1, 2] + [3, 4]" @?= Right ["[4, 6]"]
        evalText "-[[1, 2], [3, 4]]" @?= Right ["[-1, -2; -3, -4]"]
        evalText "[[1, 2], [3, 4]] == [[1, 2], [3, 4]]" @?= Right ["true"]
    , testCase "tensor primitives" $ do
        evalText "dot [1, 2, 3] [4, 5, 6]" @?= Right ["32"]
        evalP "cross [1, 0, 0] [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalText "transpose [[1, 2], [3, 4]]" @?= Right ["[1, 3; 2, 4]"]
        evalText "vmap (\\x -> x * 2) [[1, 2], [3, 4]]" @?= Right ["[2, 4; 6, 8]"]
    , testCase "a rank-three tensor"
        $ evalText "[[[1, 2], [3, 4]], [[5, 6], [7, 8]]].1.0.1" @?= Right ["6"]
    , testCase "constant literals fold into one node, constructions do not"
        $ case (desugarText "[[1, 2], [3, 4]]", desugarText "\\x -> [x, 2]") of
          ( Right (Lit (LTensor ([2, 2], [1, 2, 3, 4])))
            , Right (Lam _ (Pack [Var FZ, Lit (LTensor ([], [2]))]))
            ) -> pure ()
          other -> assertFailure (show other)
    , testCase "a name defined twice in one group is an error"
        $ case evalText "let x = 5\nlet x = 6" of
          Left err -> T.isInfixOf "defined twice" err @? T.unpack err
          Right _ -> assertFailure "expected an error"
    , testCase "statements in a group may refer to each other in any order"
        $ evalText "y\nlet y = x + 1\nlet x = 5" @?= Right ["6"]
    , testCase "where" $ evalText "let f x = x * k where k = 2\nf 21" @?= Right ["42"]
    , testCase "function definitions"
        $ evalText "let twice f x = f (f x)\nlet inc = (+ 1)\ntwice inc 5" @?= Right ["7"]
    , testCase "division by zero is a runtime error"
        $ evalText "1 / 0" @?= Left "error: division by zero"
    , testCase "an unknown unit is an unknown name"
        $ case evalText "3 furlongs" of
          Left err -> T.isInfixOf "unknown name `furlongs`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "recursion"
        $ evalText "let fact n = if n == 0 then 1 else n * fact (n - 1)\nfact 10"
          @?= Right ["3628800"]
    , testCase "mutual recursion in one group"
        $ evalText
          "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)\neven 10\nodd 7"
          @?= Right ["true", "true"]
    , testCase "recursion through a codebase reference across inputs"
        $ runLines
          ["let fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)", "fib 20"]
          @?= Right ["6765"]
    , testCase "transcendentals print their certain digits"
        $ evalText "sqrt 2" @?= Right ["1.4142135623730950488…"]
    , testCase "parse error mentions the position"
        $ case evalText "1 +" of
          Left err -> T.isInfixOf "1:4" err @? T.unpack err
          Right _ -> assertFailure "expected an error"
    , testCase "a dimension's exponent is an unbounded integer, never wrapped" $ do
        runLines [":type 1 m^18446744073709551616"]
          @?= Right ["Num (m^18446744073709551616)"]
        evalText "1 m^18446744073709551616" @?= Right ["1 m^18446744073709551616"]
        evalText "(1 m^18446744073709551616) / (1 m^18446744073709551616)"
          @?= Right ["1"]
        runLines [":type 1 m^-18446744073709551617"]
          @?= Right ["Num (1/m^18446744073709551617)"]
    , testCase "a length, count or position past a machine integer is refused" $ do
        let refused src = case evalText src of
              Left err ->
                T.isInfixOf "a tensor has at most 2^40 components" err @? T.unpack err
              Right out -> assertFailure (show out)
        refused "[1, 2].18446744073709551616"
        refused "contract 0 18446744073709551616 [1, 2; 3, 4]"
        refused "slice 0 18446744073709551616 [1, 2; 3, 4]"
        refused "f :: Vec 18446744073709551616 -> Num\nlet f v = 1"
        refused "g :: forall (a : 18446744073709551616). Vec a -> Vec a\nlet g v = v"
    , testCase "a tensor past the components limit is refused when built" $ do
        let vector n = "[" <> T.intercalate ", " (replicate n "1") <> "]"
            refused src = case runLines [":set components 100", src] of
              Left err -> T.isInfixOf "more than 100" err @? T.unpack err
              Right out -> assertFailure (show out)
        refused (vector 101)
        refused ("let v = " <> vector 11 <> " in outer v v")
        refused ("let v = " <> vector 11 <> " in wedge v v")
        refused ("let v = " <> vector 11 <> " in dot (outer v [1]) (outer [1] v)")
        refused ("[" <> T.intercalate ", " (replicate 3 (vector 50)) <> "]")
        runLines
          [ ":set components 100"
          , "(" <> vector 100 <> ").99"
          , ":set components 150"
          , "(" <> vector 101 <> ").100"
          ]
          @?= Right ["1", "1"]
    , testCase "an empty tensor takes its element type from context" $ do
        -- an ascription
        evalText "([] :: Vec 0 m)" @?= Right ["[] m"]
        evalText "dot ([] :: Vec 0 m) ([] :: Vec 0 m)" @?= Right ["0 m^2"]
        evalText "transpose ([] :: Mat 0 3 m)" @?= Right ["[; ; ] m"]
        -- unification with another operand, inside a polymorphic function
        evalText "let v = ([] :: Vec 0 m) in dot v (if true then v else [])"
          @?= Right ["0 m^2"]
        runLines ["let g v = dot v (if true then v else [])", "g ([] :: Vec 0 kg)"]
          @?= Right ["0 kg^2"]
        -- a signature
        runLines ["e :: Vec 0 m", "let e = []", "dot e e"] @?= Right ["0 m^2"]
        -- a definition left open, each use choosing
        runLines ["let z = []", ":type z", "(z :: Vec 0 m) .* (z :: Vec 0 s)"]
          @?= Right ["forall s d. Tensor (0 : s) d", "[] m s"]
    , testCase "an empty tensor nothing fixes is a type error, not an internal one" $ do
        let ambiguous r = case r of
              Left err ->
                T.isInfixOf "ambiguous: nothing fixes the shape or dimension" err
                  && not (T.isInfixOf "internal error" err)
                  @? T.unpack err
              Right out -> assertFailure (show out)
        ambiguous (evalText "[]")
        ambiguous (evalText "(1, [])")
        ambiguous (evalText "dot ([] :: Vec 0 m) []")
        ambiguous (runLines ["let e = []", "e"])
        -- inside a function it is the caller's to fix
        evalText "\\x -> []" @?= Right ["<function>"]
        runLines [":type []"] @?= Right ["forall s d. Tensor (0 : s) d"]
        -- a value that never consults its open dimension is built without it
        runLines ["data Box d = Empty | Full (Num d)", "Empty", ":type Empty"]
          @?= Right ["Empty", "forall d. Box d"]
    , testCase
        "mapping takes its result's dimension from its type, forcing no element"
        $ do
          -- lazy: the other component's division by zero is never forced
          evalText "(vmap (\\x -> 1 / x) [0, 2]).1" @?= Right ["0.5"]
          evalText "(vzipWith (\\a b -> a / b) [1, 1] [0, 2]).1" @?= Right ["0.5"]
          evalText "(timap (\\i x -> 1 / x) [0, 2]).1" @?= Right ["0.5"]
          -- empty: the function's dimension, not the input's
          evalText "vmap (\\x -> x * m) ([] :: Vec 0)" @?= Right ["[] m"]
          evalText "let e = vmap (\\x -> x * m) ([] :: Vec 0) in dot e e"
            @?= Right ["0 m^2"]
          evalText "vzipWith (\\a b -> a * b) ([] :: Vec 0 m) ([] :: Vec 0 s)"
            @?= Right ["[] m s"]
          evalText "timap (\\i x -> x * m) ([] :: Vec 0)" @?= Right ["[] m"]
          -- inside a polymorphic function, the caller's dimension
          runLines
            [ "let f g xs = vmap g xs"
            , "dot (f (\\x -> x * m) ([] :: Vec 0)) (f (\\x -> x * s) ([] :: Vec 0))"
            ]
            @?= Right ["0 m s"]
          runLines ["let h v = vmap (\\x -> x * 1 kg) v", "h ([] :: Vec 0)"]
            @?= Right ["[] kg"]
    ]

-- Closing the lint promise ---------------------------------------------------------

soundnessTests :: TestTree
soundnessTests =
  testGroup
    "soundness"
    [ testCase "functions cannot be compared"
        $ case evalText "(\\x -> x) == (\\x -> x)" of
          Left err -> T.isInfixOf "no equality on" err @? T.unpack err
          Right v -> assertFailure ("compared functions: " <> show v)
    , testCase "booleans compare through the equality instance" $ do
        evalText "true == false" @?= Right ["false"]
        evalText "(1 < 2) == true" @?= Right ["true"]
    , testCase "an unknown equality type defaults to Num"
        $ typeOfText "\\a b -> a == b" @?= Right "Num -> Num -> Bool"
    , testCase "equality is shape-polymorphic on tensors" $ do
        evalText "[1, 2] == [1, 2]" @?= Right ["true"]
        evalText "[[1, 2], [3, 4]] /= [[1, 2], [3, 5]]" @?= Right ["true"]
        evalText "3 == 3" @?= Right ["true"]
    , testCase "comparing tensors of different shapes is a static error"
        $ case evalText "[1, 2] == [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ" err @? T.unpack err
          Right v -> assertFailure (show v)
    ]
