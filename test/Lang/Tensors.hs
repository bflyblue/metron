-- | Products, contraction and slices.
module Lang.Tensors (
  productTests,
  contractionTests,
  sliceTests,
) where

import Data.Text qualified as T (isInfixOf, unpack)
import Lang.Common (
  evalP,
  evalText,
  runLines,
  runLinesP,
  typeOfText,
  typeOfTextP,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))

-- Products ------------------------------------------------------------------------

productTests :: TestTree
productTests =
  testGroup
    "products"
    [ testCase "tensor product covers scaling and plain multiplication" $ do
        evalText "2 * 3" @?= Right ["6"]
        evalText "2 * [1, 2]" @?= Right ["[2, 4]"]
        evalText "[1, 2] * 2" @?= Right ["[2, 4]"]
        evalText "[1, 2] ⊗ [3, 4]" @?= Right ["[3, 4; 6, 8]"]
    , testCase "contracting product is dot, matrix-vector and matrix-matrix" $ do
        evalText "[1, 2, 3] · [4, 5, 6]" @?= Right ["32"]
        evalText "[[1, 2], [3, 4]] @ [1, 1]" @?= Right ["[3, 7]"]
        evalText "[[1, 2], [3, 4]] @ [[0, 1], [1, 0]]" @?= Right ["[2, 1; 4, 3]"]
        evalText "[[[1, 2], [3, 4]], [[5, 6], [7, 8]]] @ [1, 0]"
          @?= Right ["[1, 3; 5, 7]"]
    , testCase "cross product, both spellings" $ do
        evalP "[1, 0, 0] × [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalP "[1, 0, 0] >< [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalP "cross [0, 1, 0] [1, 0, 0]" @?= Right ["[0, 0, -1]"]
    , testCase "indices: a vector's positions as exact dimensionless values" $ do
        evalText "indices [5, 6, 7]" @?= Right ["[0, 1, 2]"]
        evalText "indices ([5, 6, 7] m)" @?= Right ["[0, 1, 2]"]
        evalText "indices [5, 6, 7] == [0, 1, 2]" @?= Right ["true"]
        -- The argument's components are not forced.
        evalText "indices [1 / 0, 2]" @?= Right ["[0, 1]"]
        evalText "indices ([1, 2, 3] m) ⊙ ([1, 2, 3] m)" @?= Right ["[0, 2, 6] m"]
        case evalText "indices [[1, 2], [3, 4]]" of
          Left err -> T.isInfixOf "expected Vec n d, got Mat 2 2" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "vzipWith combines two tensors of one shape elementwise" $ do
        evalText "vzipWith (\\a b -> a * b) [1, 2, 3] [4, 5, 6]"
          @?= Right ["[4, 10, 18]"]
        evalText "vzipWith (\\a b -> a + b) ([1, 2] m) ([3, 4] m)"
          @?= Right ["[4, 6] m"]
        evalText "vzipWith (\\a b -> a * b) [[1, 2], [3, 4]] [[1, 0], [0, 1]]"
          @?= Right ["[1, 0; 0, 4]"]
        evalText "bound (vzipWith (\\a b -> a + b) ([1, 2] ± 0.1) [0, 0])"
          @?= Right ["[0.1, 0.1]"]
        case evalText "vzipWith (\\a b -> a * b) [1, 2] [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "timap maps with each component's multi-index (design §3.3)" $ do
        evalText "timap (\\i x -> i.0 * x) [10, 20, 30]" @?= Right ["[0, 20, 60]"]
        evalText "timap (\\i x -> i.0 + i.1) [[0, 0], [0, 0]]"
          @?= Right ["[0, 1; 1, 2]"]
        evalText
          "timap (\\i x -> if i.0 == i.1 then x else 0) [[1, 2, 3], [4, 5, 6], [7, 8, 9]]"
          @?= Right ["[1, 0, 0; 0, 5, 0; 0, 0, 9]"]
        evalText
          "timap (\\i x -> i.2) [[[1, 2, 3], [4, 5, 6]], [[7, 8, 9], [10, 11, 12]]] == [[[0, 1, 2], [0, 1, 2]], [[0, 1, 2], [0, 1, 2]]]"
          @?= Right ["true"]
        evalText
          "timap (\\i x -> 100 * i.0 + 10 * i.1 + i.2) [[[1, 2, 3], [4, 5, 6]], [[7, 8, 9], [10, 11, 12]]] == [[[0, 1, 2], [10, 11, 12]], [[100, 101, 102], [110, 111, 112]]]"
          @?= Right ["true"]
        -- A number has rank 0 and an empty index.
        evalText "timap (\\i x -> x + 1) 5" @?= Right ["6"]
        -- Units ride along, and the result's dimension is the function's.
        evalText "timap (\\i x -> x) ([1, 2] m)" @?= Right ["[1, 2] m"]
        evalText "timap (\\i x -> i.0 * x / 1 s) ([1, 2] m)" @?= Right ["[0, 2] m s^-1"]
        evalText "bound (timap (\\i x -> x) ([1, 2] ± 0.1))" @?= Right ["[0.1, 0.1]"]
        -- The index is exact.
        evalText "timap (\\i x -> i.0 / 3) [0, 0] == [0, 1/3]" @?= Right ["true"]
        case evalText "timap (\\i x -> i.1 * x) [1, 2, 3]" of
          Left err ->
            T.isInfixOf
              "expected Tensor (n : m : s) d, got Vec 3: a tensor of rank at least 2 against a vector"
              err
              @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "elementwise product and division" $ do
        evalText "[1, 2] ⊙ [3, 4]" @?= Right ["[3, 8]"]
        evalText "[1, 2] .* [3, 4]" @?= Right ["[3, 8]"]
        evalText "[1, 2] ⊘ [2, 4]" @?= Right ["[0.5, 0.5]"]
        evalText "[1, 2] ./ [2, 4]" @?= Right ["[0.5, 0.5]"]
    , testCase "scalar division"
        $ evalText "[2, 4] / 2 + [[1, 2], [3, 4]].0 / 1" @?= Right ["[2, 4]"]
    , testCase "elementwise division by zero fails only for that element" $ do
        evalText "([1, 2] ./ [0, 2]).1" @?= Right ["1"]
        evalText "([1, 2] ./ [0, 2]).0" @?= Left "error: division by zero"
    , testCase "quantity rule multiplies a literal by a declared unit" $ do
        -- A dimensionless unit with no units left in it shows a plain number.
        runLines ["unit dozen = 12", "3 dozen", "3 dozen to dozen/dozen"]
          @?= Right ["3 dozen", "36"]
        -- to takes a unit, not an amount (design §3.10, U6).
        case runLines ["unit dozen = 12", "3 dozen to 1"] of
          Left err -> T.isInfixOf "an amount after `to`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "juxtaposition is for units and charts, by type" $ do
        evalP "5 g" @?= Right ["5 g"]
        evalP "3 (m/s)" @?= Right ["3 m s^-1"]
        evalP "90 deg to rad" @?= Right ["1.5707963267948966192… rad"]
        -- What follows a literal is refused by its type (design §3.10, U4).
        case runLinesP ["let a = [1, 2; 3, 4]", "5 a"] of
          Left err ->
            T.isInfixOf "`a` is a Mat 2 2, not a unit or a chart: write the `*`" err
              @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "2 pi" of
          Left err ->
            T.isInfixOf "`pi` is a Num, not a unit or a chart: write the `*`" err
              @? T.unpack err
          Right v -> assertFailure (show v)
        -- A dynamic suffix is now a chart, never a first-class unit.
        evalP "(\\c -> 5 c) degC" @?= Right ["5 degC"]
        case evalP "let f x = x in 3 f" of
          Left err -> T.isInfixOf "not a unit or a chart: write the `*`" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "3 (f x)" of
          Left err -> T.isInfixOf "unknown name `f`" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "3 furlongs" of
          Left err -> T.isInfixOf "unknown name `furlongs`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "names work prefix and infix" $ do
        evalText "outer 2 [1, 2]" @?= Right ["[2, 4]"]
        evalText "[1, 2] `dot` [3, 4]" @?= Right ["11"]
        evalText "within 5 1 == (5 ± 1)"
          @?= Left "error: cannot decide comparison at sigma 3: the difference is 0.0 ± 2.0"
    ]

{- | Contraction and index permutation with literal positions (design §3.3,
§4.2): any rank, typed from the literals.
-}
contractionTests :: TestTree
contractionTests =
  testGroup
    "contraction and permutation"
    [ testCase "contract 0 1 is the trace of a matrix, in its unit" $ do
        evalText "contract 0 1 [[1, 2], [3, 4]]" @?= Right ["5"]
        evalText "contract 0 1 ([[1, 2], [3, 4]] m)" @?= Right ["5 m"]
        evalText "contract 1 0 [[1, 2], [3, 4]]" @?= Right ["5"]
    , testCase "contraction of a rank-3 tensor over each pair of positions" $ do
        -- t[a][b][c] = 1 + 4a + 2b + c
        let t = "[[[1, 2], [3, 4]], [[5, 6], [7, 8]]]"
        evalText ("contract 0 1 " <> t) @?= Right ["[8, 10]"]
        evalText ("contract 0 2 " <> t) @?= Right ["[7, 11]"]
        evalText ("contract 1 2 " <> t) @?= Right ["[5, 13]"]
        -- Unequal lengths elsewhere: shape [2, 3, 2], pairing positions 0 and 2.
        evalText "contract 0 2 [[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]"
          @?= Right ["[9, 13, 17]"]
    , testCase "the contracting product is a contraction of the tensor product" $ do
        evalText
          "let a = [[1, 2], [3, 4]] in let b = [5, 6] in a · b == contract 1 2 (a * b)"
          @?= Right ["true"]
        evalText
          "let a = [[1, 2], [3, 4]] in let c = [[0, 1], [5, 7]] in a · c == contract 1 2 (a * c)"
          @?= Right ["true"]
    , testCase "permute [1, 0] is transpose" $ do
        evalText "let a = [[1, 2, 3], [4, 5, 6]] in permute [1, 0] a == transpose a"
          @?= Right ["true"]
        evalP "permute [1, 0] ([[1, 2], [3, 4]] km)" @?= Right ["[1, 3; 2, 4] km"]
    , testCase "a rank-3 permutation moves lengths and components together" $ do
        -- position q of the result is position p_q of the operand:
        -- r[x][y][z] = t[y][z][x]
        evalText
          "permute [2, 0, 1] [[[1, 2, 3], [4, 5, 6]]] == [[[1, 4]], [[2, 5]], [[3, 6]]]"
          @?= Right ["true"]
        typeOfText "permute [2, 0, 1] [[[1, 2, 3], [4, 5, 6]]]"
          @?= Right "Tensor [3, 1, 2]"
    , testCase "permuting the leading positions leaves the rest alone" $ do
        typeOfText "permute [0, 1] [[[1, 2, 3], [4, 5, 6]]]"
          @?= Right "Tensor [1, 2, 3]"
        typeOfText "permute [1, 0] [[[1, 2, 3], [4, 5, 6]]]"
          @?= Right "Tensor [2, 1, 3]"
        evalText "permute [1, 0] [[[1, 2, 3], [4, 5, 6]]] == [[[1, 2, 3]], [[4, 5, 6]]]"
          @?= Right ["true"]
    , testCase "types are computed from the literal positions" $ do
        typeOfText "\\t -> contract 0 1 t"
          @?= Right "forall n s d. Tensor (n : n : s) d -> Tensor s d"
        typeOfText "\\t -> contract 0 2 t"
          @?= Right "forall n m s d. Tensor (n : m : n : s) d -> Tensor (m : s) d"
        typeOfText "\\t -> permute [2, 0, 1] t"
          @?= Right "forall n m k s d. Tensor (n : m : k : s) d -> Tensor (k : n : m : s) d"
        typeOfText "\\t -> permute [1, 0] t"
          @?= Right "forall n m s d. Tensor (n : m : s) d -> Tensor (m : n : s) d"
        typeOfTextP "trace" @?= Right "forall n s d. Tensor (n : n : s) d -> Tensor s d"
    , testCase "the prelude's trace" $ do
        evalP "trace [[1, 2, 3], [4, 5, 6], [7, 8, 10]]" @?= Right ["16"]
        -- Above rank two it is the partial trace over the first two positions.
        evalP "trace [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]" @?= Right ["[8, 10]"]
    , testCase "the tensor argument may be left off" $ do
        evalText "let tr = contract 0 1 in tr [[1, 2], [3, 4]]" @?= Right ["5"]
        evalText "(permute [1, 0]) [[1, 2], [3, 4]]" @?= Right ["[1, 3; 2, 4]"]
    , testCase "positions must be literal naturals, distinct, a permutation" $ do
        let fails src needle = case runLines [src] of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        fails
          "contract 0 0 [[1, 2], [3, 4]]"
          "two different positions, not position 0 with itself"
        fails
          "\\x y -> contract x y [[1, 2], [3, 4]]"
          "the positions of contract must be literal natural numbers"
        fails
          "contract (-1) 0 [[1, 2], [3, 4]]"
          "the positions of contract must be literal natural numbers"
        fails
          "contract 0.5 1 [[1, 2], [3, 4]]"
          "the positions of contract must be literal natural numbers"
        fails "contract" "contract takes two literal positions and then a tensor"
        fails "contract 0" "contract takes two literal positions and then a tensor"
        fails
          "permute [0, 0] [[1, 2], [3, 4]]"
          "permute [0, 0] is not a permutation of 0 .. 1"
        fails
          "permute [1] [[1, 2], [3, 4]]"
          "permute [1] is not a permutation of 0 .. 0"
        fails
          "permute [] [[1, 2], [3, 4]]"
          "permute takes a literal vector of natural numbers"
        fails
          "\\p -> permute p [[1, 2], [3, 4]]"
          "permute takes a literal vector of natural numbers"
        fails "permute" "permute takes a literal permutation and then a tensor"
    , testCase "rank and length mismatches are type errors" $ do
        let fails src needle = case runLines [src] of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        fails
          "contract 0 2 [[1, 2], [3, 4]]"
          "contract 0 2 needs a tensor of rank at least 3, got Mat 2 2"
        fails
          "permute [2, 0, 1] [[1, 2], [3, 4]]"
          "permute [2, 0, 1] needs a tensor of rank at least 3"
        fails "contract 0 1 [[1, 2, 3], [4, 5, 6]]" "lengths differ: 2 and 3"
        fails "contract 0 1 [1, 2]" "needs a tensor of rank at least 2"
        fails "contract 0 1 (noise 2)" "needs a tensor of rank at least 2"
    , testCase "contraction sums nudges: two independent bounds on the diagonal" $ do
        evalText "bound (contract 0 1 ([[1, 2], [3, 4]] ± 0.1))" @?= Right ["0.2"]
        evalText "bound (permute [1, 0] ([[1, 2], [3, 4]] ± 0.1))"
          @?= Right ["[0.1, 0.1; 0.1, 0.1]"]
    , testCase ":view reads both back as written" $ do
        runLines
          ["let f a = contract 0 1 (permute [1, 0] a)", ":view f", "f [[1, 2], [3, 4]]"]
          @?= Right ["f = \\a -> contract 0 1 (permute [1, 0] a)", "5"]
        runLines ["let g = permute [2, 0, 1]", ":view g"]
          @?= Right ["g = permute [2, 0, 1]"]
    ]

sliceTests :: TestTree
sliceTests =
  testGroup
    "slicing along an axis"
    [ testCase "m._.i is column i of a matrix" $ do
        evalText "[1, 2; 3, 4]._.0" @?= Right ["[1, 3]"]
        evalText "[1, 2; 3, 4]._.1" @?= Right ["[2, 4]"]
        evalText "[1, 2, 3; 4, 5, 6]._.2" @?= Right ["[3, 6]"]
    , testCase "a column is a row of the transpose" $ do
        evalText "let m = [1, 2, 3; 4, 5, 6] in m._.0 == (transpose m).0"
          @?= Right ["true"]
        evalText "let m = [1, 2, 3; 4, 5, 6] in m._.0 == (permute [1, 0] m).0"
          @?= Right ["true"]
        evalText "let m = [1, 2, 3; 4, 5, 6] in m._.1 == (permute [1, 0] m).1"
          @?= Right ["true"]
    , testCase "a rank-3 tensor sliced on axis 1 and on axis 2" $ do
        -- t[a][b][c] = 1 + 6a + 2b + c, shape [2, 3, 2]
        let t = "[[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]"
        evalText (t <> "._.2 == [[5, 6], [11, 12]]") @?= Right ["true"]
        evalText (t <> "._.0 == [[1, 2], [7, 8]]") @?= Right ["true"]
        evalText (t <> "._._.1 == [[2, 4, 6], [8, 10, 12]]") @?= Right ["true"]
        evalText (t <> "._._.0 == [[1, 3, 5], [7, 9, 11]]") @?= Right ["true"]
        typeOfText (t <> "._.2") @?= Right "Mat 2 2"
        typeOfText (t <> "._._.1") @?= Right "Mat 2 3"
    , testCase "the chain reads left to right: t._.0.1 is (slice 1 0 t).1" $ do
        let t = "[[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]"
        evalText (t <> "._.0.1") @?= Right ["[7, 8]"]
        evalText ("let t = " <> t <> " in t._.0.1 == (slice 1 0 t).1")
          @?= Right ["true"]
        evalText (t <> ".1._.1") @?= Right ["[8, 10, 12]"]
    , testCase "slice k i t written out is the same primitive" $ do
        evalText "let m = [1, 2; 3, 4] in slice 1 1 m == m._.1" @?= Right ["true"]
        evalText "let m = [1, 2; 3, 4] in slice 0 1 m == m.1" @?= Right ["true"]
        evalText "let col = slice 1 0 in col [1, 2; 3, 4]" @?= Right ["[1, 3]"]
    , testCase "a slice keeps the dimension and display unit" $ do
        evalText "([1, 2; 3, 4] m)._.0" @?= Right ["[1, 3] m"]
        typeOfText "([1, 2; 3, 4] m)._.0" @?= Right "Vec 2 m"
    , testCase "types are computed from the axis and position" $ do
        typeOfText "\\m -> m._.0"
          @?= Right "forall n m s d. Tensor (n : m + 1 : s) d -> Tensor (n : s) d"
        typeOfText "\\t -> t._._.2"
          @?= Right "forall n m k s d. Tensor (n : m : k + 3 : s) d -> Tensor (n : m : s) d"
        typeOfText "\\m -> m._.0 + m._.2"
          @?= Right "forall n m s d. Tensor (n : m + 3 : s) d -> Tensor (n : s) d"
    , testCase "range and rank are type errors" $ do
        let fails src needle = case runLines [src] of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        fails "[1, 2; 3, 4]._.2" "position 2 is out of range for axis 1 of length 2"
        fails "[[[1, 2]]]._._.2" "position 2 is out of range for axis 2 of length 2"
        fails "[1, 2, 3]._.0" "slice 1 0 needs a tensor of rank at least 2, got Vec 3"
        fails "slice 5 0 [1, 2; 3, 4]" "slice 5 0 needs a tensor of rank at least 6"
        fails "let col2 m = m._.2\ncol2 [1, 2; 3, 4]" "too short"
    , testCase "a wildcard needs a position; slice needs literals" $ do
        let fails src needle = case runLines [src] of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
        fails
          "[1, 2; 3, 4]._"
          "a wildcard ._ skips an axis and must be followed by a position"
        fails
          "[1, 2; 3, 4]._ + 1"
          "a wildcard ._ skips an axis and must be followed by a position"
        fails "[1, 2; 3, 4] ._.0" "a wildcard ._ must be attached to a tensor"
        fails
          "\\x -> slice x 0 [1, 2; 3, 4]"
          "the axis and position of slice must be literal natural numbers"
        fails
          "slice 1 0.5 [1, 2; 3, 4]"
          "the axis and position of slice must be literal natural numbers"
        fails
          "slice 1"
          "slice takes a literal axis and a literal position and then a tensor"
    , testCase "a slice gathers nudges without adding any" $ do
        evalText "bound (([1, 2; 3, 4] ± 0.1)._.0)" @?= Right ["[0.1, 0.1]"]
    , testCase ":view reads a slice back with wildcards" $ do
        runLines ["let col m = m._.0", ":view col", "col [1, 2; 3, 4]"]
          @?= Right ["col = \\m -> m._.0", "[1, 3]"]
        runLines ["let f t = (t._._.1).0", ":view f"]
          @?= Right ["f = \\t -> t._._.1.0"]
        runLines ["let g t = slice 0 1 t", ":view g"]
          @?= Right ["g = \\t -> slice 0 1 t"]
        runLines ["let h t = (neg t)._.0", ":view h"]
          @?= Right ["h = \\t -> (-t)._.0"]
    ]
