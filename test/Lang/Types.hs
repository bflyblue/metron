-- | Types, signatures, annotations, foralls, dimensions and roles.
module Lang.Types (
  typeTests,
  lintRegressionTests,
  annotationTests,
  forallTests,
  dimensionSyntaxTests,
  roleTests,
) where

import Control.Monad (forM_)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map (keys, lookup)
import Data.Text (Text)
import Data.Text qualified as T (
  breakOn,
  isInfixOf,
  isPrefixOf,
  length,
  pack,
  replicate,
  unpack,
 )
import Data.Text.IO qualified as TIO (readFile)
import Lang.Common (
  bool,
  editFileOf,
  edited,
  evalP,
  evalText,
  expectError,
  expecting,
  ifT,
  keyword',
  lastN,
  linesIn,
  multiline,
  num,
  persistLines,
  reload,
  replaceOnce,
  runLines,
  runLinesP,
  seeded,
  sessionOf,
  sessionP,
  startsWith,
  theSeed,
  timedForAll,
  type',
  typeOfText,
  typeOfTextP,
  unit',
  v0,
  v1,
  v2,
  withTempStore,
  (/.),
  (==.),
 )
import Metron.Codebase (Codebase (signatures))
import Metron.Core (Term (App, Cycle, Lam), Vec (VCons, VNil))
import Metron.Desugar (
  desugarClosed,
  noResolver,
  renderDesugarError,
 )
import Metron.Dimension (
  BaseDim,
  Dim,
  DimAtom (..),
  Spelling (..),
  dimAtoms,
  dimFromAtoms,
  dimOne,
  isDimOne,
  renderDimArgIn,
  renderDimIn,
 )
import Metron.Driver (
  EditScope (EditCodebase, EditName),
  Session (codebase, scope),
  exportSource,
  feed,
 )
import Metron.Hash (decodeTypeDef, encodeTypeDef)
import Metron.Infer (TypeError (..), elaborateClosed)
import Metron.Parser (parseExpr, parseType)
import Metron.Prelude (isLibraryPath)
import Metron.Repl qualified as R (
  Completion (replacement),
  complete,
  highlight,
  namesOf,
 )
import Metron.Store (openStore, sync)
import Metron.TCore (lintClosed)
import Metron.Type (
  Axis (AAnon),
  Kind (KAxis, KShape),
  Len (LRank),
  Scheme (Forall),
  Shape (SCons, SNil, SVar),
  Type (TFun, TTensor),
  TypeDef (TypeDef),
  freeVars,
  noLookup,
  renderScheme,
  renderType,
  structuralLabel,
 )
import Metron.Type.Syntax (queryScheme)
import System.FilePath ((</>))
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (
  Assertion,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )
import Test.Tasty.QuickCheck (
  Gen,
  checkCoverage,
  chooseInt,
  conjoin,
  counterexample,
  cover,
  elements,
  testProperty,
  vectorOf,
  (===),
 )

-- | Inference accepts a closed program, and lint gives its schemes back.
lintsAsInferred :: Text -> Assertion
lintsAsInferred src =
  case parseExpr src >>= first renderDesugarError . desugarClosed noResolver of
    Left err -> assertFailure (T.unpack err)
    Right (t, _) -> case elaborateClosed noLookup t of
      Left err -> assertFailure (T.unpack err.message)
      Right (schemes, typed) -> lintClosed noLookup typed @?= Right schemes

typeTests :: TestTree
typeTests =
  testGroup
    "types"
    [ testCase "literals and arithmetic" $ do
        typeOfText "1 + 2" @?= Right "Num"
        typeOfText "1 < 2" @?= Right "Bool"
    , testCase "identity is polymorphic"
        $ typeOfText "\\x -> x" @?= Right "forall a. a -> a"
    , testCase "higher-order"
        $ typeOfText "\\f x -> f (f x)" @?= Right "forall a. (a -> a) -> a -> a"
    , testCase "let-polymorphism"
        $ typeOfText "let id x = x in if id true then id 1 else 2" @?= Right "Num"
    , testCase "vector and matrix literals" $ do
        typeOfText "[1, 2, 3]" @?= Right "Vec 3"
        typeOfText "[[1, 2], [3, 4]]" @?= Right "Mat 2 2"
        typeOfText "[1, 2; 3, 4]" @?= Right "Mat 2 2"
        typeOfText "[1; 2]" @?= Right "Mat 2 1"
        typeOfText "[1, 2; 3, 4;; 5, 6; 7, 8]" @?= Right "Tensor [2, 2, 2]"
        evalText "[1, 2; 3, 4] · [1, 1]" @?= Right ["[3, 7]"]
        case evalText "[1, 2; 3]" of
          Left err -> T.isInfixOf "same shape" err @? T.unpack err
          Right v -> assertFailure (show v)
        typeOfText "[[1, 2], [3, 4]].1" @?= Right "Vec 2"
    , testCase "projection gives a lower bound on the length (design §4.1)" $ do
        typeOfText "\\v -> v.0"
          @?= Right "forall n s d. Tensor (n + 1 : s) d -> Tensor s d"
        typeOfText "\\v -> v.2 + v.0"
          @?= Right "forall n s d. Tensor (n + 3 : s) d -> Tensor s d"
        typeOfText "\\v -> v.0 + 1" @?= Right "forall n. Vec (n + 1) -> Num"
    , testCase "elementwise operators are shape-polymorphic (core.md)" $ do
        typeOfText "\\a b -> a + b"
          @?= Right "forall s d. Tensor s d -> Tensor s d -> Tensor s d"
        typeOfText "[1, 2] + [3, 4]" @?= Right "Vec 2"
        typeOfText "neg [[1, 2], [3, 4]]" @?= Right "Mat 2 2"
    , testCase "products have one type each (design §4.2)" $ do
        typeOfText "2 * [1, 2]" @?= Right "Vec 2"
        typeOfText "[1, 2] * 2" @?= Right "Vec 2"
        typeOfText "[1, 2] * [3, 4, 5]" @?= Right "Mat 2 3"
        typeOfText "[[1, 2], [3, 4]] @ [1, 1]" @?= Right "Vec 2"
        typeOfText "[1, 2] @ [3, 4]" @?= Right "Num"
        typeOfText "[[1, 2], [3, 4]] @ [[1, 0], [0, 1]]" @?= Right "Mat 2 2"
        typeOfText "[1, 2] .* [3, 4]" @?= Right "Vec 2"
        typeOfText "[2, 4] / 2" @?= Right "Vec 2"
    , testCase "an unknown-rank product operand defaults at generalisation" $ do
        -- Amounts: the left operand is a scalar, the right any tensor.
        typeOfText "\\k v -> (1 * k) * v"
          @?= Right "forall d s d1. Num d -> Tensor s d1 -> Tensor s (d1*d)"
        -- A role left open keeps both operands scalar, so that the role
        -- generalises (design §3.10, U9).
        typeOfText "\\k v -> k * v"
          @?= Right "forall d s d1. Num d -> Tensor s d1 -> Tensor s (d*d1)"
        typeOfText "\\a b -> a @ b"
          @?= Right "forall n d s d1. Vec n d -> Tensor (n : s) d1 -> Tensor s (d*d1)"
    , testCase "contraction requires matching inner lengths"
        $ case evalText "[[1, 2], [3, 4]] @ [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "mismatched lengths are a static error"
        $ case evalText "[1, 2] + [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "length-polymorphic primitives" $ do
        typeOfText "dot"
          @?= Right "forall n d s d1. Vec n d -> Tensor (n : s) d1 -> Tensor s (d*d1)"
        typeOfText "transpose" @?= Right "forall n m d. Mat n m d -> Mat m n d"
        typeOfTextP "cross"
          @?= Right "forall (a : 3) d d1. Vec a d -> Vec a d1 -> Vec a (d*d1)"
    , testCase "indices, vzipWith and vimap (design §3.3)" $ do
        typeOfText "indices" @?= Right "forall n d. Vec n d -> Vec n"
        typeOfText "vzipWith"
          @?= Right
            "forall d d1 d2 s. (Num d -> Num d1 -> Num d2) -> Tensor s d -> Tensor s d1 -> Tensor s d2"
        typeOfTextP "vimap"
          @?= Right "forall d d1 n. (Num -> Num d -> Num d1) -> Vec n d -> Vec n d1"
        typeOfText "indices ([1, 2] m)" @?= Right "Vec 2"
    , testCase "timap's index is a Vec (rank s) (design §4.1)" $ do
        typeOfText "timap"
          @?= Right
            "forall s d d1. (Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1"
        -- Projecting from the index asks for that many leading lengths.
        typeOfText "\\t -> timap (\\i x -> i.0 * x) t"
          @?= Right "forall n s d. Tensor (n : s) d -> Tensor (n : s) d"
        typeOfText "\\t -> timap (\\i x -> if i.0 == i.1 then x else 0) t"
          @?= Right "forall n m s. Tensor (n : m : s) -> Tensor (n : m : s)"
        -- A length-polymorphic function on the index leaves the rank open.
        typeOfText "\\t -> timap (\\i x -> dot i i * x) t"
          @?= Right "forall s d. Tensor s d -> Tensor s d"
        -- The function returns a number.
        case typeOfText "timap (\\i x -> i) [[1, 2], [3, 4]]" of
          Left err -> T.isInfixOf "expected Num d, got Vec (rank s)" err @? T.unpack err
          Right t -> assertFailure (T.unpack t)
        -- At a known shape the rank is a literal.
        typeOfText "timap (\\i x -> norm i) [[1, 2], [3, 4]]" @?= Right "Mat 2 2"
        -- Two shapes whose ranks must agree cannot be generalised.
        case typeOfText "\\f t u -> (timap f t, timap f u)" of
          Left err -> T.isInfixOf "must have the same rank" err @? T.unpack err
          Right t -> assertFailure (T.unpack t)
    , testCase "a definition over timap generalises with its index demands" $ do
        runLines
          [ "let diag t = timap (\\i x -> if i.0 == i.1 then x else 0) t"
          , ":type diag"
          , "diag [[1, 2, 3], [4, 5, 6], [7, 8, 9]]"
          ]
          @?= Right
            [ "forall n m s. Tensor (n : m : s) -> Tensor (n : m : s)"
            , "[1, 0, 0; 0, 5, 0; 0, 0, 9]"
            ]
        case runLines
          [ "let diag t = timap (\\i x -> if i.0 == i.1 then x else 0) t"
          , "diag [1, 2, 3]"
          ] of
          Left err ->
            T.isInfixOf
              "expected Tensor (n : m : s), got Vec 3: a tensor of rank at least 2 against a vector"
              err
              @? T.unpack err
          Right v -> assertFailure (show v)
        runLines
          [ "let scale2 t = timap (\\i x -> i.0 * x) t"
          , "scale2 [1, 2, 3]"
          , "scale2 [[1, 2], [3, 4]]"
          ]
          @?= Right ["[0, 2, 6]", "[0, 0; 3, 4]"]
        -- The rank stays inside the body: linted, and run at two ranks.
        runLines
          [ "let sq t = timap (\\i x -> dot i i * x) t"
          , "sq [[1, 1], [1, 1]]"
          , "sq [1, 1, 1]"
          , "sq 7"
          ]
          @?= Right ["[0, 1; 1, 2]", "[0, 1, 4]", "0"]
        -- A stored definition whose scheme shows the rank.
        runLines
          [ "let tm g t = timap g t"
          , ":add"
          , ":type tm"
          , "tm (\\i x -> i.1 * x) [[1, 2], [3, 4]]"
          ]
          @?= Right
            [ "added tm"
            , "forall s d d1. (Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1"
            , "[0, 2; 0, 4]"
            ]
        -- A rank in a type encodes under its own length tag and decodes back.
        let def =
              TypeDef
                [(0, KShape)]
                [[TTensor (SCons (LRank 0 1) AAnon (SVar 0)) dimOne]]
                structuralLabel
        decodeTypeDef (encodeTypeDef def) @?= Right def
    , testCase "recursive definitions get types"
        $ runLines ["let fact n = if n == 0 then 1 else n * fact (n - 1)", ":type fact"]
          @?= Right ["Num -> Num"]
    , testCase "mutually recursive definitions get types"
        $ runLines
          [ "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)"
          , ":type even"
          , ":type odd"
          ]
          @?= Right ["Num -> Bool", "Num -> Bool"]
    , testCase "codebase references are instantiated freshly"
        $ runLines ["let id x = x", ":add", ":type if id true then id 1 else 2"]
          @?= Right ["added id", "Num"]
    , testCase "Num plus Bool is a static error with an excerpt"
        $ case evalText "1 + true" of
          Left err -> do
            T.isInfixOf "error at 1:5" err @? T.unpack err
            T.isInfixOf "expected Num, got Bool" err @? T.unpack err
            T.isInfixOf "^^^^" err @? T.unpack err
          Right v -> assertFailure ("evaluated to " <> show v)
    , testCase "out-of-range projection is static"
        $ case evalText "[1, 2].2" of
          Left err ->
            T.isInfixOf "position 2 is out of range for a vector of length 2" err
              @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "too-short vector against a polymorphic projection is static"
        $ case evalText "let first v = v.0\nfirst []" of
          Left err -> T.isInfixOf "too short" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "if condition must be Bool"
        $ case evalText "if 1 then 2 else 3" of
          Left err -> T.isInfixOf "condition of `if` must be a Bool" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "applying a non-function"
        $ case evalText "true 2" of
          Left err -> T.isInfixOf "is not a function" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a type error in a definition names the definition"
        $ case evalText "let bad = 1 + true" of
          Left err -> T.isInfixOf "in `bad`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "well-typed programs never hit the evaluator's type checks"
        $ evalText "let twice f x = f (f x)\ntwice (\\n -> n * 2) 5" @?= Right ["20"]
    , testCase
        ":update leaves a dependent that no longer typechecks on the old version"
        $ expecting
          ( runLines
              [ "let f x = x + 1"
              , "let g = f 3"
              , ":add"
              , "let f = 7"
              , ":update"
              , "g"
              , ":view g"
              , ":todo"
              ]
          )
        $ \outs -> do
          any (startsWith "left g on") outs @? show outs
          case lastN 3 outs of
            [v, view, td] -> do
              v @?= "4"
              startsWith "g = f#" view @? T.unpack view
              startsWith "stale: g uses f#" td @? T.unpack td
            other -> assertFailure (show other)
    ]

roleTests :: TestTree
roleTests =
  testGroup
    "amount arithmetic"
    [ testCase "generic multiplication retains tensor polymorphism" $ do
        runLinesP
          [ "let mul a b = a * b"
          , "mul 2 [1,2,3]"
          , "let twice x = 2 * x"
          , "twice [1,2,3]"
          , "(* km) [1,2,3]"
          ]
          @?= Right ["[2, 4, 6]", "[2, 4, 6]", "[1, 2, 3] km"]
        runLinesP ["let sq x = x * x", "sq (3 m)", "let inv x = x^-1", "inv (2 s)"]
          @?= Right ["9 m^2", "0.5 s^-1"]
    , testCase "arithmetic types read back as signatures" $ do
        forM_ ["\\a b -> a * b", "\\a b -> a / b", "\\x -> x^2", "(* km)"] $ \body ->
          expecting (runLinesP ["let f = " <> body, ":type f"]) $ \case
            [ty] ->
              runLinesP [multiline ["f :: " <> ty, "let f = " <> body], ":type f"]
                @?= Right [ty]
            other -> assertFailure (show other)
    , testCase "implicit amounts survive edit, export and reload" $ withTempStore $ \dir -> do
        stored <-
          persistLines
            dir
            [ "unit speedUnit = km/h"
            , "let attach x = x * km"
            , "let perSecond x = x / s"
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        linesIn loaded ["attach [1,2]", "perSecond (3 m)", "5 speedUnit"]
          @?= Right ["[1, 2] km", "3 m s^-1", "5 speedUnit"]
        file <- editFileOf stored ["attach"]
        (_, outs) <- edited (EditName "attach") file stored
        outs @?= ["nothing changed"]
        source <- either (assertFailure . T.unpack) pure (exportSource stored Nothing)
        restored <- either (assertFailure . T.unpack) pure (sessionP [source, ":add"])
        linesIn restored ["attach [1,2]", "perSecond (3 m)", "5 speedUnit"]
          @?= linesIn loaded ["attach [1,2]", "perSecond (3 m)", "5 speedUnit"]
    ]

-- Regressions found by lint ------------------------------------------------------------

lintRegressionTests :: TestTree
lintRegressionTests =
  testGroup
    "lint regressions"
    [ -- Found by the property "evaluating a linted term never reports an
      -- internal error", which ran for an hour on this program from the
      -- type-directed generator. exp squared its halved argument back at
      -- the precision of the value before squaring, so a small result
      -- lost every digit (e^-200 was 0) and only a working precision of
      -- thousands of digits found it: e^-19683 took 20 s, and its
      -- reciprocal was refused as a division by zero.
      localOption (mkTimeout 5000000)
        $ testCase "exp of a large negative argument keeps its digits, quickly"
        $ do
          evalText "exp (-200)" @?= Right ["1.3838965267367375306…e-87"]
          evalText "exp (-19683) > 0" @?= Right ["true"]
          evalText "1 / exp (-19683) < 1" @?= Right ["false"]
          evalText
            "(((\\q -> [6, 9, 0] K ⊙ [5, 3, 2] K^-1) ([[-3]]._.0 - ([6] - [7])) ⊘ (if 0 > 1.5 then [5, 2, 8] ⊙ [2, 6, 1.5] else (\\x -> [9, 8, 5]) (\\y -> [0.5] m^-1 * kg^-1))).2 * (let g = 0.25 * (-0.5 mol * cd) / (2 * 0.5 mol) <= 3 mol^-1 * rad^-2 * (if true then -1 mol * cd * rad^2 else 5 mol * cd * rad^2) in [0.5] K * (4 kg / K) · ([[0]] rad^-1 ⊙ ([[3]] A * rad / kg)) ⊘ ((\\w -> [9] kg) g ⊙ ([4] * 9 kg^-1)))).0 ⊙ (-2 kg * A^-1 / (exp (((-3 to m / m) * (6 * 1.5))^3) ⊙ (\\f -> ([8, 1.5] kg).0) (vmap (\\z -> -2) (let x = [9] in [0, 8, 6; 1.5, 0, 8] K^2 / s))))"
            @?= Right ["0"]
    , testCase "instantiation renames quantified variables simultaneously" $ do
        typeOfTextP "\\a b -> a >< b"
          @?= Right "forall (a : 3) d d1. Vec a d -> Vec a d1 -> Vec a (d*d1)"
        evalP "[1, 0, 0] m >< ([0, 1, 0] m / s)" @?= Right ["[0, 0, 1] m^2 s^-1"]
        evalText "[1, 2] m ⊙ [3, 4] s" @?= Right ["[3, 8] m s"]
    , testCase "a stored polymorphic definition instantiates at several dimensions"
        $ runLines ["let sq x = x * x", ":add", "sq (3 m)", "sq (2 s)", ":type sq"]
          @?= Right
            ["added sq", "9 m^2", "4 s^2", "forall d. Num d -> Num (d^2)"]
    , -- Found while designing the type-directed generator, whose pinning
      -- rules lean on how pending constraints meet a let. `k * v` leaves a product
      -- constraint pending because `k` belongs to the enclosing lambda; the
      -- let used to generalise `v`'s shape and the result shape anyway, so
      -- `g [1, 2]` came out as `Tensor s` and inference accepted programs
      -- that lint then rejected.
      testCase
        "a let does not generalise variables a pending product constraint ties to the scope"
        $ do
          typeOfText "\\k -> let g = \\v -> k * v in g [1, 2]"
            @?= Right "forall d (a : 2). Num d -> Vec a d"
          case evalText "((\\k -> let g = \\v -> k * v in g [1, 2]) 3) + [1, 2, 3]" of
            Left err -> T.isInfixOf "lengths differ" err @? T.unpack err
            Right v -> assertFailure (show v)
          evalText "(\\k -> let g = \\v -> k * v in g [1, 2]) 3" @?= Right ["[3, 6]"]
    , -- Found by the type-directed generator. The default for a product's
      -- operand of unknown rank made the whole operand a scalar (for `*`)
      -- or a vector (for `@`), even one such as `[[x]]` that already had
      -- two lengths, so inference refused programs that check once `x`'s
      -- rank is known. The open part takes the least rank it can instead.
      testCase "an unknown-rank product operand keeps the lengths it has" $ do
        typeOfText "\\x -> [[x]] @ [2]"
          @?= Right "forall d (a : 1). Num d -> Vec a d"
        typeOfText "\\x -> [x] * [1]"
          @?= Right "forall d (a : 1) (b : 1). Num d -> Mat a b d"
        typeOfText "\\x -> [[x]] * [1]"
          @?= Right "forall d (a : 1) (b : 1) (c : 1). Num d -> Tensor [a, b, c] d"
        typeOfText "(\\x -> [[x]] @ [2]) 3" @?= Right "Vec 1"
        -- Dot's two constraints share their prefix; the result's two
        -- lengths make the left operand a matrix.
        typeOfText "\\x -> (x @ [[1, 2]]).0.1"
          @?= Right "forall n (a : 1) d. Mat (n + 1) a d -> Num d"
        -- The bare defaults are unchanged.
        typeOfText "\\x -> x @ [2]" @?= Right "forall (a : 1) d. Vec a d -> Num d"
        typeOfText "\\x -> x * [2]" @?= Right "forall d (a : 1). Num d -> Vec a d"
        mapM_
          lintsAsInferred
          [ "\\x -> [[x]] @ [2]"
          , "\\x -> [x] * [1]"
          , "\\x -> [[x]] * [1]"
          , "\\x -> (x @ [[1, 2]]).0.1"
          ]
    , -- Found by the type-directed generator. A let inside an operand of a
      -- product or of `==` settled the operator's own constraint, created
      -- outside the let, and defaulted its operand to a scalar.
      testCase "a let defaults only the constraints of its own right-hand side" $ do
        typeOfText "[1, 2] * (let y = 1 in [3])" @?= Right "Mat 2 1"
        typeOfText "(let y = 1 in [3]) * [1, 2]" @?= Right "Mat 1 2"
        typeOfText "[[1, 2]] @ (let y = 1 in [3, 4])" @?= Right "Vec 1"
        typeOfText "[1, 2] == (let y = 1 in [3, 4])" @?= Right "Bool"
        typeOfText "(\\x -> x * [1, 2]) (let y = 1 in [3, 4])" @?= Right "Mat 2 2"
        evalText "[1, 2] * (let y = 1 in [3])" @?= Right ["[3; 6]"]
    , -- Found by the type-directed generator: sections and composition bind
      -- names the desugarer makes up (`§s0`), which printed as they were
      -- and did not re-parse.
      testCase "printed Core never shows the desugarer's own binder names" $ do
        runLines ["let inc = (+ 1)", ":view inc"] @?= Right ["inc = \\x -> x + 1"]
        runLines ["let comp f g = f . g", ":view comp"]
          @?= Right ["comp = \\f -> \\g -> \\x -> f (g x)"]
        runLines ["let k = \\x -> (+ x)", ":view k"]
          @?= Right ["k = \\x -> \\x' -> x' + x"]
    , -- Found by the type-directed generator. Generalisation turned a
      -- dimension variable that only occurs inverted, `d^-1`, into `d` in the
      -- scheme but not in the elaborated term, so lint saw a let annotated
      -- `Num d -> Num d` bound to `Num [d^-1] -> Num [d^-1]`.
      testCase
        "a dimension variable flipped at generalisation is flipped in the term too"
        $ do
          typeOfText "\\x -> let k = \\w -> if true then x else 1 / w in x"
            @?= Right "forall d. Num d -> Num d"
          evalText
            "let g = \\x -> let k = \\w -> if true then x else 1 / w in x in g (2 m)"
            @?= Right ["2 m"]
    , -- The members of a cycle share one set of quantified variables, so a
      -- variable is flipped only when it is inverted in every member; flipping
      -- it member by member gave schemes that disagreed with lint's.
      testCase
        "a cycle's inferred schemes agree with lint's when a dimension is inverted"
        $ let
            -- Inside a member's lambda: v0 is its argument, v1 is f, v2 is g.
            f' = Lam "x" (ifT (v0 ==. v0) (bool True) (App v2 (num 1 /. v0)))
            g' = Lam "y" (ifT (v0 ==. v0) (bool True) (App v1 (num 1 /. v0)))
            cycle' = Cycle (VCons "f" (VCons "g" VNil)) (VCons f' (VCons g' VNil))
           in
            case elaborateClosed noLookup cycle' of
              Left err -> assertFailure (T.unpack err.message)
              Right (schemes, typed) -> do
                let closed (Forall vs t) = all ((`elem` map fst vs) . fst) (freeVars t)
                all closed schemes @? show schemes
                map renderScheme <$> lintClosed noLookup typed
                  @?= Right (map renderScheme schemes)
    , -- Found by the type-directed generator. `neg 0` (the primitive applied
      -- to a constant) printed as `-0`, which reads back as the constant
      -- zero: a different term with a different hash.
      testCase "the negation primitive applied to a constant prints as an application" $ do
        runLines ["let k = neg 3", ":view k"] @?= Right ["k = neg 3"]
        runLines ["let k = neg [1, -2]", ":view k"] @?= Right ["k = neg [1, -2]"]
        runLines ["let k = neg (-3)", ":view k"] @?= Right ["k = neg (-3)"]
        runLines ["let k = -3", ":view k"] @?= Right ["k = -3"]
        runLines ["let k x = -x", ":view k"] @?= Right ["k = \\x -> -x"]
    ]

-- Type annotations (design §4.8) ---------------------------------------------------

-- | A data type and a definition over it, for the signature tests.
shapeSetup :: Text
shapeSetup = "data Shape = Circle (Num m) | Rect (Num m) (Num m)"

areaDef :: Text
areaDef = "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"

-- | The output of lines after a setup, without the setup's.
afterSetup :: [Text] -> [Text] -> Either Text [Text]
afterSetup setup ls = do
  s <- sessionP setup
  linesIn s ls

annotationTests :: TestTree
annotationTests =
  testGroup
    "type annotations"
    [ testCase "a signature may come before its definition, in a later input" $ do
        runLinesP
          [ "f :: Num m -> Num m"
          , ":scratch"
          , "let f x = x"
          , ":type f"
          , ":add"
          , ":type f"
          ]
          @?= Right
            [ "pending: f :: Num m -> Num m"
            , "Num m -> Num m"
            , "added f"
            , "Num m -> Num m"
            ]
        case runLinesP ["f :: Num m -> Num m", ":add"] of
          Left err -> T.isInfixOf "has a signature but no definition" err @? T.unpack err
          Right v -> assertFailure (show v)
        runLinesP ["f :: Num m -> Num m", ":forget f", ":scratch"]
          @?= Right ["forgot `f`"]
    , testCase "a signature before or after its definition; :type and :ls print it" $ do
        forM_
          [ ["double :: Num m -> Num m", "let double x = x + x"]
          , ["let double x = x + x", "double :: Num m -> Num m"]
          ]
          $ \ls ->
            runLinesP [multiline ls, ":type double", ":ls double"]
              @?= Right ["Num m -> Num m", "double : Num m -> Num m"]
        -- Unsigned, the definition's own type, as before.
        runLinesP ["let double x = x + x", ":type double"]
          @?= Right ["forall s d. Tensor s d -> Tensor s d"]
        runLinesP
          [shapeSetup, multiline ["area :: Shape -> Num (m^2)", areaDef], ":type area"]
          @?= Right ["Shape -> Num (m^2)"]
        -- :ls : type matches the signature, the narrower type.
        afterSetup
          [ multiline ["double :: Num m -> Num m", "let double x = x + x"]
          , "let twice x = x + x"
          ]
          [ ":ls double : Num m -> Num m"
          , ":ls double : Num s -> Num s"
          , ":ls twice : Num s -> Num s"
          ]
          @?= Right
            [ "double : Num m -> Num m"
            , "nothing matches"
            , "twice : forall s d. Tensor s d -> Tensor s d"
            ]
    , testCase "the scratch lists a signature; :add stores it; :forget drops it" $ do
        let signed = multiline ["double :: Num m -> Num m", "let double x = x + x"]
        runLinesP [signed, ":scratch", ":todo"]
          @?= Right
            [ "pending: double :: Num m -> Num m"
            , "pending: double"
            , "pending: double :: Num m -> Num m (use :add or :update)"
            , "pending: double (use :add or :update)"
            ]
        runLinesP [signed, ":add", ":type double", ":scratch"]
          @?= Right ["added double", "Num m -> Num m"]
        -- A signature alone signs the stored definition.
        afterSetup
          ["let double x = x + x", ":add"]
          ["double :: Num m -> Num m", ":add", ":type double"]
          @?= Right ["signed double", "Num m -> Num m"]
        -- A later signature replaces a pending one.
        runLinesP [signed, "double :: Num s -> Num s", ":type double"]
          @?= Right ["replaced pending signature of `double`", "Num s -> Num s"]
        runLinesP [signed, ":forget double", ":scratch"] @?= Right ["forgot `double`"]
    , testCase
        "a signature narrows: uses see it, an unsigned name of the same hash does not"
        $ do
          let setup = [multiline ["f :: Num m -> Num m", "let f x = x"], "let g x = x"]
          afterSetup setup [":type f", ":type g", "g (3 s)", "f (3 m)"]
            @?= Right ["Num m -> Num m", "forall a. a -> a", "3 s", "3 m"]
          -- One hash, two names: the signature is the label's.
          case afterSetup setup [":hash f", ":hash g"] of
            Right [a, b] -> a @?= b
            other -> assertFailure (show other)
          expectError (afterSetup setup ["f (3 s)"]) "expected Num m, got Num s"
          -- A dependent keeps its Core's type; its own signature is checked
          -- against what its uses of f allow.
          afterSetup setup ["let h y = f y", ":type h", "h (3 s)"]
            @?= Right ["forall a. a -> a", "3 s"]
          afterSetup
            setup
            [multiline ["h :: Num m -> Num m", "let h y = f y"], ":type h"]
            @?= Right ["Num m -> Num m"]
          expectError
            (afterSetup setup [multiline ["h :: forall a. a -> a", "let h y = f y"]])
            "`h`'s definition has type `Num m -> Num m`, not as general as its signature `a -> a`"
          expectError
            (afterSetup setup ["let k = f (3 s)"])
            "expected Num m, got Num s"
    , testCase
        "a signature more general than its definition is refused, at the signature"
        $ do
          case runLinesP [multiline ["f :: forall a. a -> a", "let f x = 1"]] of
            Left err -> do
              ( "`f`'s definition has type `a -> Num`, not as general as its signature `a -> a`"
                  `T.isInfixOf` err
                )
                @? T.unpack err
              (("  f :: forall a. a -> a\n  " <> T.replicate 21 "^" <> "\n") `T.isInfixOf` err)
                @? T.unpack err
            Right outs -> assertFailure (show outs)
          expectError
            (runLinesP [shapeSetup, multiline ["area :: forall d. Shape -> Num d", areaDef]])
            "`area`'s definition has type `Shape -> Num (m^2)`, not as general as its signature `Shape -> Num d`"
    , testCase "an unknown type, a signature without a definition, two signatures" $ do
        expectError
          (runLinesP [multiline ["h :: Nope -> Num", "let h x = x"]])
          "unknown type `Nope`"
        expectError
          (runLinesP ["k :: Num", ":add"])
          "`k` has a signature but no definition"
        runLinesP ["k :: Num", ":scratch"] @?= Right ["pending: k :: Num"]
        expectError
          (runLinesP [multiline ["k :: Num", "k :: Num m", "let k = 1"]])
          "`k` has two signatures in the same group"
    , testCase
        "a redefinition is checked against the stored signature, unless the input gives one"
        $ do
          let setup = [multiline ["f :: forall a. a -> a", "let f x = x"], ":add"]
          expectError
            (afterSetup setup ["let f x = x + 1 m"])
            "`f`'s definition has type `Num m -> Num m`, not as general as its signature `a -> a`"
          afterSetup
            setup
            [multiline ["f :: Num m -> Num m", "let f x = x + 1 m"], ":type f"]
            @?= Right ["Num m -> Num m"]
          -- A redefinition the signature still holds of keeps it.
          afterSetup setup ["let f y = (\\z -> z) y", ":type f"]
            @?= Right ["forall a. a -> a"]
    , testCase
        "an upgrade a dependent's signature would not hold of leaves it on its version"
        $ do
          let setup =
                [ multiline
                    [ "let base x = x"
                    , "f :: forall a. a -> a"
                    , "let f x = base x"
                    , "let g x = (\\y -> y) (base x)"
                    ]
                , ":add"
                ]
          case afterSetup setup ["let base x = x + 1 m", ":update", ":type f", ":type g"] of
            Right outs -> do
              any ("left f on #" `T.isPrefixOf`) outs @? show outs
              any ("not as general as its signature a -> a" `T.isInfixOf`) outs @? show outs
              any ("upgraded g " `T.isPrefixOf`) outs @? show outs
              lastN 2 outs @?= ["forall a. a -> a", "Num m -> Num m"]
            Left err -> assertFailure (T.unpack err)
    , testCase ":rename of a namespace re-hashes its type, and the signature follows" $ do
        let setup =
              [ multiline
                  [ "namespace geo"
                  , "  data Shape = Circle (Num m) | Rect (Num m) (Num m)"
                  , "  area :: Shape -> Num (m^2)"
                  , "  " <> areaDef
                  ]
              , ":add"
              ]
        case afterSetup
          setup
          [":rename geo plane", ":type plane.area", "plane.area (plane.Rect (2 m) (3 m))"] of
          Right outs -> lastN 2 outs @?= ["plane.Shape -> Num (m^2)", "6 m^2"]
          Left err -> assertFailure (T.unpack err)
        s <- sessionOf (setup ++ [":rename geo plane"])
        userSignatures s.codebase @?= ["plane.area"]
    , testCase "signatures over tuples, lists and declared types"
        $ runLinesP
          [ "data Box a = Box a"
          , multiline
              [ "swap :: (Num m, Num s) -> (Num s, Num m)"
              , "let swap p = case p of (a, b) -> (b, a)"
              , "len :: {Num m} -> Num"
              , "let len xs = length xs"
              , "unbox :: Box (Num m) -> Num m"
              , "let unbox b = case b of Box x -> x"
              ]
          , ":type swap"
          , ":type len"
          , ":type unbox"
          ]
          @?= Right
            [ "(Num m, Num s) -> (Num s, Num m)"
            , "{Num m} -> Num"
            , "Box (Num m) -> Num m"
            ]
    , testCase "a cycle's member may be signed"
        $ runLinesP
          [ multiline
              [ "even :: Num -> Bool"
              , "let even n = if n == 0 then true else odd (n - 1)"
              , "let odd n = if n == 0 then false else even (n - 1)"
              ]
          , ":type even"
          , "even 4"
          ]
          @?= Right ["Num -> Bool", "true"]
    , testCase
        "a signature in a namespace block; :rename moves it, :alias does not copy it"
        $ do
          let setup =
                [ multiline
                    [ "namespace geo"
                    , "  double :: Num m -> Num m"
                    , "  let double x = x + x"
                    ]
                , ":add"
                ]
          s <- sessionOf (setup ++ [":rename geo.double twice"])
          afterSetup setup [":type geo.double", ":rename geo.double twice", ":type twice"]
            @?= Right
              ["Num m -> Num m", "renamed `geo.double` to `twice`", "Num m -> Num m"]
          userSignatures s.codebase @?= ["twice"]
          aliased <- sessionOf (setup ++ [":rename geo.double twice", ":alias d2 twice"])
          linesIn aliased [":type d2", ":type twice"]
            @?= Right ["forall s d. Tensor s d -> Tensor s d", "Num m -> Num m"]
          unnamed <- sessionOf (setup ++ [":unname geo.double"])
          null (userSignatures unnamed.codebase) @? "unname drops the signature"
    , testCase
        "variables are written back with plain names, unless the type prints that unit"
        $ do
          s <-
            sessionOf
              [ multiline
                  [ "same :: forall sh d. Tensor sh d -> Tensor sh d"
                  , "let same x = x + x"
                  , "keep :: forall n k. Mat n k -> Mat n k"
                  , "let keep a = a"
                  , "secs :: forall sh d. Tensor sh d -> Tensor sh (d*s)"
                  , "let secs x = 1 s * x"
                  ]
              , ":add"
              ]
          linesIn s [":type same", ":type keep", ":type secs"]
            @?= Right
              [ "forall s d. Tensor s d -> Tensor s d"
              , "forall n m. Mat n m -> Mat n m"
              , "forall s1 d. Tensor s1 d -> Tensor s1 (s*d)"
              ]
          source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
          ("keep :: forall n m. Mat n m -> Mat n m\nlet keep = " `T.isInfixOf` source)
            @? T.unpack source
          ("same :: forall s d. Tensor s d -> Tensor s d\nlet same = " `T.isInfixOf` source)
            @? T.unpack source
          ( "secs :: forall s1 d. Tensor s1 d -> Tensor s1 (s*d)\nlet secs = "
              `T.isInfixOf` source
            )
            @? T.unpack source
          reloaded <-
            either
              (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
              pure
              (sessionP [source, ":add"])
          reloaded.codebase.signatures @?= s.codebase.signatures
    , testCase ":export and :load round-trip a signature" $ do
        s <-
          sessionOf
            [shapeSetup, multiline ["area :: Shape -> Num (m^2)", areaDef], ":add"]
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        ("area :: Shape -> Num (m^2)\nlet area = " `T.isInfixOf` source)
          @? T.unpack source
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        reloaded.codebase.signatures @?= s.codebase.signatures
        linesIn reloaded [":type area"] @?= Right ["Shape -> Num (m^2)"]
    , testCase "a signature survives a reload; :unname writes it off" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ shapeSetup
            , multiline
                [ "area :: Shape -> Num (m^2)"
                , areaDef
                , "double :: Num m -> Num m"
                , "let double x = x + x"
                ]
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.signatures @?= s.codebase.signatures
        linesIn loaded [":type area", ":type double", ":ls double"]
          @?= Right
            ["Shape -> Num (m^2)", "Num m -> Num m", "double : Num m -> Num m"]
        logText <- TIO.readFile (dir </> "names.log")
        (" sig area .Shape -> Num (m^2)" `T.isInfixOf` logText) @? T.unpack logText
        st <- either (assertFailure . T.unpack) pure =<< openStore theSeed dir
        case feed loaded ":unname double" of
          Left err -> assertFailure (T.unpack err)
          Right (s', _) -> sync st loaded.codebase s'.codebase
        logText' <- TIO.readFile (dir </> "names.log")
        (" unsig double" `T.isInfixOf` logText') @? T.unpack logText'
        (reloaded2, notes') <- reload dir
        notes' @?= []
        userSignatures reloaded2.codebase @?= ["area"]
    , testCase ":edit --file adds and removes a signature" $ do
        s <- sessionOf ["let double x = x + x", ":add"]
        file <- editFileOf s []
        signedFile <-
          replaceOnce "let double = " "double :: Num m -> Num m\nlet double = " file
        (s1, outs1) <- edited EditCodebase signedFile s
        outs1 @?= ["signed double"]
        linesIn s1 [":type double"] @?= Right ["Num m -> Num m"]
        file1 <- editFileOf s1 []
        ("double :: Num m -> Num m\nlet double = " `T.isInfixOf` file1)
          @? T.unpack file1
        -- Unchanged, nothing changes.
        (_, same) <- edited EditCodebase file1 s1
        same @?= ["nothing changed"]
        unsignedFile <- replaceOnce "double :: Num m -> Num m\n" "" file1
        (s2, outs2) <- edited EditCodebase unsignedFile s1
        outs2 @?= ["unsigned double"]
        linesIn s2 [":type double"] @?= Right ["forall s d. Tensor s d -> Tensor s d"]
        -- :edit of one name pastes the signature with it.
        linesIn s1 [":edit double"]
          @?= Right ["double :: Num m -> Num m", "let double = \\x -> x + x"]
    , testCase
        "highlighting: :: plain, the type after it as a type; completion offers types"
        $ do
          let names = R.namesOf seeded
          R.highlight names "area :: Shape -> Num (m^2)"
            @?= "area :: Shape -> " <> type' "Num" <> " (" <> unit' "m" <> "^2)"
          R.highlight names "(x :: forall d. Num d)"
            @?= "(x :: " <> keyword' "forall" <> " d. " <> type' "Num" <> " d)"
          -- A bound s is the variable throughout, a product included; an
          -- unbound one the second.
          R.highlight names "f :: forall s. Tensor s (m/s) -> Num s"
            @?= "f :: "
              <> keyword' "forall"
              <> " s. "
              <> type' "Tensor"
              <> " s ("
              <> unit' "m"
              <> "/s) -> "
              <> type' "Num"
              <> " s"
          R.highlight names "len :: Num s"
            @?= "len :: " <> type' "Num" <> " " <> unit' "s"
          R.highlight names "(3 m :: Num m) + 1 m"
            @?= "(3 "
              <> unit' "m"
              <> " :: "
              <> type' "Num"
              <> " "
              <> unit' "m"
              <> ") + 1 "
              <> unit' "m"
          let completed line = maybe [] (map (.replacement) . snd) (R.complete seeded (reverse line, ""))
          completed "f :: Nu" @?= ["Num"]
          -- After the ascription's parenthesis closes, an expression again.
          ("length" `elem` completed "(3 m :: Num m) + lengt")
            @? show (completed "(3 m :: Num m) + lengt")
    , testCase
        ":edit of a type moves the signatures that name it, as it moves their definitions"
        $ do
          s <-
            sessionOf
              [ multiline
                  [ "data Shape = Circle (Num m)"
                  , "make :: Num m -> Shape"
                  , "let make r = Circle r"
                  , "same :: Shape -> Shape"
                  , "let same s = s"
                  ]
              , ":add"
              ]
          file <- editFileOf s ["Shape"]
          grown <-
            replaceOnce "Circle (Num m)" "Circle (Num m) | Square (Num m)" file
          (s1, outs) <- edited (EditName "Shape") grown s
          filter (\l -> "signed" `T.isInfixOf` l || "left" `T.isPrefixOf` l) outs @?= []
          linesIn
            s1
            [":type make", ":type same", "same (make (1 m))", "same (Square (2 m))"]
            @?= Right ["Num m -> Shape", "Shape -> Shape", "Circle (1 m)", "Square (2 m)"]
    , testCase "ascription: (e :: type) narrows the expression's type" $ do
        runLinesP
          [ "(1 :: Num)"
          , "(3 m :: Num m)"
          , "([1, 2, 3] m :: Vec 3 m)"
          , ":type (1 :: Num)"
          , ":type \\x -> (x :: forall d. Num d)"
          , ":type \\x -> x"
          , ":type \\v -> (v :: forall n. Vec n)"
          ]
          @?= Right
            [ "1"
            , "3 m"
            , "[1, 2, 3] m"
            , "Num"
            , "forall d. Num d -> Num d"
            , "forall a. a -> a"
            , "forall n. Vec n -> Vec n"
            ]
    , testCase "ascription never widens: (1 :: forall a. a) is 1, of type Num"
        $ runLinesP ["(1 :: forall a. a)", ":type (1 :: forall a. a)"]
          @?= Right ["1", "Num"]
    , testCase "an ascription narrows the node it is written on, wherever it is" $ do
        runLinesP
          [ "data Box a = Box {item :: a}"
          , ":type \\x y -> {x, (y :: Num m)}"
          , ":type \\x -> if true then (x :: Num m) else x"
          , ":type \\x -> if true then x else (x :: Num s)"
          , ":type \\f y -> case true of true -> f (y :: Num m); false -> f y"
          , ":type \\y -> Box {item = (y :: Num m)}"
          , ":type \\y -> (+ (y :: Num m))"
          , ":type \\v -> (v :: Vec 3).0"
          , "{1 m, (2 m :: Num m)}"
          ]
          @?= Right
            [ "Num m -> Num m -> {Num m}"
            , "Num m -> Num m"
            , "Num s -> Num s"
            , "forall a. (Num m -> a) -> Num m -> a"
            , "Num m -> Box (Num m)"
            , "Num m -> Num m -> Num m"
            , "Vec 3 -> Num"
            , "{1 m, 2 m}"
            ]
        expectError
          (runLinesP ["let f x = g (3 s) where g y = (y :: Num m)"])
          "expected Num m, got Num s"
        -- Each fails at its own ascription.
        forM_
          [ ("{1, (2 :: Bool)}", "(2 :: Bool)")
          , ("if true then (1 :: Bool) else 2", "(1 :: Bool)")
          , ("if true then 1 else (2 :: Bool)", "(2 :: Bool)")
          , ("case true of true -> sin (1 :: Num m); false -> 2", "(1 :: Num m)")
          ]
          $ \(src, part) -> case runLinesP [src] of
            Left err -> do
              ("the ascription: " `T.isInfixOf` err) @? T.unpack err
              let col = T.length (fst (T.breakOn part src))
                  carets = "\n  " <> T.replicate col " " <> T.replicate (T.length part) "^" <> "\n"
              (carets `T.isInfixOf` err) @? T.unpack err
            Right outs -> assertFailure (show outs)
        -- A literal position of contract may be ascribed.
        runLinesP ["contract (0 :: Num) 1 [1, 2; 3, 4]"]
          @?= runLinesP ["contract 0 1 [1, 2; 3, 4]"]
    , testCase "an ascription that does not unify is refused at the ascription" $ do
        case runLinesP ["(3 m :: Num kg)"] of
          Left err -> do
            ("the ascription: expected Num kg, got Num m" `T.isInfixOf` err)
              @? T.unpack err
            ("  (3 m :: Num kg)\n  ^^^^^^^^^^^^^^^" `T.isInfixOf` err) @? T.unpack err
          Right outs -> assertFailure (show outs)
        expectError (runLinesP ["(1 :: Bool)"]) "the ascription: "
        expectError (runLinesP ["(1 :: Nope)"]) "unknown type `Nope`"
        expectError
          (runLinesP ["let f x = x", "(f :: Num m -> Num m) (3 s)"])
          "expected Num m, got Num s"
        expectError
          (runLinesP ["let k = (3 m :: Num kg)"])
          "the ascription: expected Num kg, got Num m"
    , testCase
        "ascriptions inside definitions check, in a cycle too; :view shows the plain expression"
        $ do
          runLinesP
            [ "let f x = (x :: Num m) + 1 m"
            , ":view f"
            , "f (2 m)"
            , "let g x = (x :: Num m)"
            , ":type g"
            , ":view g"
            ]
            @?= Right ["f = \\x -> x + 1 m", "3 m", "forall a. a -> a", "g = \\x -> x"]
          expectError
            ( runLinesP
                [ multiline
                    [ "let even n = if n == 0 then true else odd (n - 1)"
                    , "let odd n = if (n :: Num m) == 0 then false else even (n - 1)"
                    ]
                ]
            )
            "in `odd`: expected Num m, got Num: dimensions differ by m"
          -- In a cycle member, an ascription that fails is reported at itself.
          case runLinesP
            [ multiline
                [ "let even n = if n == 0 then true else odd (n - 1)"
                , "let odd n = if n == 0 then false else (even (n - 1) :: Num)"
                ]
            ] of
            Left err -> do
              ("in `odd`: the ascription: " `T.isInfixOf` err) @? T.unpack err
              ("error at 2:39" `T.isInfixOf` err) @? T.unpack err
              (("\n  " <> T.replicate 38 " " <> T.replicate 21 "^" <> "\n") `T.isInfixOf` err)
                @? T.unpack err
            Right outs -> assertFailure (show outs)
          runLinesP
            [ multiline
                [ "let even n = if n == 0 then true else odd (n - 1)"
                , "let odd n = if (n :: Num) == 0 then false else even (n - 1)"
                ]
            , "even 4"
            ]
            @?= Right ["true"]
    ]

-- | Required @forall@ (design §3.9 decision 6, §4.8): stage 2a.
forallTests :: TestTree
forallTests =
  testGroup
    "forall"
    [ testCase "a variable must be bound: an unbound name is unknown" $ do
        case runLinesP [multiline ["f :: a -> a", "let f x = x"]] of
          Left err -> do
            ( "unknown name `a` in a type; bind it with forall if it is a variable"
                `T.isInfixOf` err
              )
              @? T.unpack err
            ("error at 1:6\n" `T.isInfixOf` err) @? T.unpack err
            ("  f :: a -> a\n       ^\n" `T.isInfixOf` err) @? T.unpack err
          Right outs -> assertFailure (show outs)
        expectError
          (runLinesP ["(1 :: a)"])
          "unknown name `a` in a type; bind it with forall if it is a variable"
        expectError
          (runLinesP [multiline ["g :: forall n. Vec n d -> Vec n d", "let g v = v"]])
          "unknown name `d` in a type"
        -- A body's ascription without a signature to bind its name.
        expectError
          (runLinesP ["let h x = (x :: a)"])
          "unknown name `a` in a type; bind it with forall if it is a variable"
        -- Units, base units and types are names, as before.
        runLinesP
          [ multiline ["g :: Num km -> Num m", "let g x = x"]
          , ":type g"
          ]
          @?= Right ["Num m -> Num m"]
        runLinesP ["j :: Num s -> Num s", ":scratch"]
          @?= Right ["pending: j :: Num s -> Num s"]
    , testCase "binders: the unicode spelling, and what a binder may not be" $ do
        runLinesP [multiline ["f :: ∀ a. a -> a", "let f x = x"], ":type f"]
          @?= Right ["forall a. a -> a"]
        expectError
          (runLinesP [multiline ["f :: forall a a. a -> a", "let f x = x"]])
          "`a` is bound twice"
        expectError
          (runLinesP [multiline ["f :: forall A. A -> A", "let f x = x"]])
          "`A` cannot be a type variable; a variable is a lowercase name"
        expectError
          (runLinesP ["data T = T (forall a. a)"])
          "unexpected forall"
        -- An unused binder binds nothing.
        runLinesP [multiline ["f :: forall a b. a -> a", "let f x = x"], ":type f"]
          @?= Right ["forall a. a -> a"]
    , testCase "a sized binder is that many axes: Vec 3 is accepted, Vec 2 refused" $ do
        let setup =
              [ multiline
                  ["keep :: forall (a : 3) d. Vec a d -> Vec a d", "let keep v = v"]
              ]
        afterSetup setup [":type keep", "keep ([1, 2, 3] m)"]
          @?= Right ["forall (a : 3) d. Vec a d -> Vec a d", "[1, 2, 3] m"]
        expectError (afterSetup setup ["keep [1, 2]"]) "lengths differ: 3 and 2"
        -- A sized binder prints sized (stage 2b), so :export and :load and
        -- an unchanged :edit keep its axes of their own (the sig log line
        -- across a reload is in storeTests).
        s <- sessionOf (setup ++ [":add"])
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        ("keep :: forall (a : 3) d. Vec a d -> Vec a d\n" `T.isInfixOf` source)
          @? T.unpack source
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        let axesOf sess = case Map.lookup "keep" sess.codebase.signatures of
              Just (Forall vs _) -> [v | (v, KAxis) <- vs]
              Nothing -> [-1]
        axesOf s @?= [0]
        axesOf reloaded @?= [0]
        reloaded.codebase.signatures @?= s.codebase.signatures
        expectError (linesIn reloaded ["keep [1, 2]"]) "lengths differ: 3 and 2"
        file <- editFileOf s []
        (edited', outs) <- edited EditCodebase file s
        outs @?= ["nothing changed"]
        edited'.codebase.signatures @?= s.codebase.signatures
        -- The size is a length, so the binder is not a type.
        expectError
          (runLinesP [multiline ["f :: forall (a : 3). a -> a", "let f x = x"]])
          "is used both as a length and as a type"
        -- A definition of another length does not hold of it.
        expectError
          ( runLinesP
              [ multiline
                  ["two :: forall (a : 3) d. Vec a d -> Vec a d", "let two v = v + [1, 2] m"]
              ]
          )
          "not as general as its signature"
    , testCase "a binder named like a unit shadows it within its type only" $ do
        -- s is the shape variable in the signature, the second in the body.
        let setup =
              [ multiline
                  [ "same :: forall s d. Tensor s d -> Tensor s d"
                  , "let same x = x + x"
                  , "secs :: Num s -> Num s"
                  , "let secs x = x + 1 s"
                  ]
              ]
        afterSetup setup [":type same", ":type secs", "same ([1, 2] s)", "secs (2 s)"]
          @?= Right
            [ "forall s d. Tensor s d -> Tensor s d"
            , "Num s -> Num s"
            , "[2, 4] s"
            , "3 s"
            ]
        -- Bound, the s in brackets is the variable, not the second.
        expectError
          ( runLinesP
              [multiline ["wrong :: forall s. Num s -> Num s", "let wrong x = x + 1 s"]]
          )
          "`wrong`'s definition has type `Num s -> Num s`, not as general as its signature `Num d -> Num d`"
        -- Both read back, through :export and :load.
        s <- sessionOf (setup ++ [":add"])
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        ("same :: forall s d. Tensor s d -> Tensor s d\n" `T.isInfixOf` source)
          @? T.unpack source
        ("secs :: Num s -> Num s\n" `T.isInfixOf` source) @? T.unpack source
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        reloaded.codebase.signatures @?= s.codebase.signatures
    , testCase "a signature's variables scope over its body's ascriptions" $ do
        -- The ascription's a is the signature's.
        runLinesP
          [ multiline ["f :: forall a. a -> a", "let f x = (x :: a)"]
          , ":type f"
          , "f (3 m)"
          , multiline
              ["v2 :: forall n d. Vec n d -> Vec n d", "let v2 x = (x :: Vec n d) + x"]
          , ":type v2"
          , multiline
              ["w :: forall (a : 3) d. Vec a d -> Vec a d", "let w x = (x :: Vec a d)"]
          , "w ([1, 2, 3] m)"
          ]
          @?= Right
            [ "forall a. a -> a"
            , "3 m"
            , "forall n d. Vec n d -> Vec n d"
            , "[1, 2, 3] m"
            ]
        -- Without the scope, (x :: b) only narrows; with it, b is the
        -- signature's b, so the definition's a and b would be one.
        expectError
          (runLinesP [multiline ["g :: forall a b. a -> b -> a", "let g x y = (x :: b)"]])
          "`g`'s definition has type `a -> a -> a`, not as general as its signature `a -> b -> a`"
        expectError
          ( runLinesP
              [multiline ["p :: forall a b. a -> b -> (a, b)", "let p x y = (x, (y :: a))"]]
          )
          "not as general as its signature `a -> b -> (a, b)`"
        -- An ascription's own forall shadows the signature's variable.
        runLinesP
          [ multiline ["q :: forall a b. a -> b -> b", "let q x y = (y :: forall a. a)"]
          , ":type q"
          ]
          @?= Right ["forall a b. a -> b -> b"]
        -- A variable at another kind than the signature's.
        expectError
          (runLinesP [multiline ["k :: forall a. a -> a", "let k x = (x :: Vec a)"]])
          "is used both as a type and as a length"
        -- In a cycle: pong's ascription makes its a and b one.
        expectError
          ( runLinesP
              [ multiline
                  [ "let ping x y = if true then (x, y) else pong x y"
                  , "pong :: forall a b. a -> b -> (a, b)"
                  , "let pong x y = ping x (y :: a)"
                  ]
              ]
          )
          "`pong`'s definition has type `a -> a -> (a, a)`"
        runLinesP
          [ multiline
              [ "let ping x y = if true then (x, y) else pong x y"
              , "pong :: forall a b. a -> b -> (a, b)"
              , "let pong x y = ping (x :: a) (y :: b)"
              ]
          , ":type pong"
          ]
          @?= Right ["forall a b. a -> b -> (a, b)"]
        -- The body checked against the signature: x is the signature's a,
        -- and a function of y besides.
        expectError
          (runLinesP [multiline ["f :: forall a. a -> a", "let f x y = (x :: a)"]])
          "in `f`: the signature: "
        -- Only a signature given with the definition scopes over it.
        expectError
          ( afterSetup
              [multiline ["f :: forall a. a -> a", "let f x = x"], ":add"]
              ["let f x = (x :: a)"]
          )
          "unknown name `a` in a type"
    , testCase ":type, :ls, :edit and :export print forall; :view shows the term" $ do
        s <-
          sessionOf
            [ multiline
                [ "let ident x = x"
                , "twin :: forall a b. a -> b -> (a, b)"
                , "let twin x y = (x, y)"
                ]
            , ":add"
            ]
        -- :view shows a definition's term, :edit its signature too.
        linesIn s [":type ident", ":ls ident", ":ls twin", ":view twin", ":edit twin"]
          @?= Right
            [ "forall a. a -> a"
            , "ident : forall a. a -> a"
            , "twin : forall a b. a -> b -> (a, b)"
            , "twin = \\x -> \\y -> (x, y)"
            , "twin :: forall a b. a -> b -> (a, b)"
            , "let twin = \\x -> \\y -> (x, y)"
            ]
        -- A type with no variables prints as before.
        linesIn s [":type 3 m", ":type \\x -> x + 1 m"]
          @?= Right ["Num m", "Num m -> Num m"]
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        ("twin :: forall a b. a -> b -> (a, b)\nlet twin = " `T.isInfixOf` source)
          @? T.unpack source
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        reloaded.codebase.signatures @?= s.codebase.signatures
        -- Errors print types as before.
        expectError
          (linesIn s ["twin 1 2 + 1"])
          "expected Tensor s d, got (Num, Num)"
    , testCase
        ":ls : type queries stay implicit: unknown lowercase names are variables"
        $ do
          let ls q = runLinesP [":ls --all : " <> q]
          ls "{a} -> Num" @?= Right ["std.length : forall a. {a} -> Num"]
          -- forall in a query binds, as in a signature.
          ls "forall a. {a} -> Num" @?= Right ["std.length : forall a. {a} -> Num"]
    , testCase
        "a sig line writes forall and reads back across a reload"
        $ withTempStore
        $ \dir -> do
          s <-
            persistLines
              dir
              [ multiline
                  [ "same :: forall s d. Tensor s d -> Tensor s d"
                  , "let same x = x + x"
                  , "pair :: forall a b. a -> b -> (a, b)"
                  , "let pair x y = (x, y)"
                  , "let ident x = x"
                  , "keep :: forall (a : 3) d. Vec a d -> Vec a d"
                  , "let keep v = v"
                  ]
              , ":add"
              ]
          logText <- TIO.readFile (dir </> "names.log")
          (" sig same forall s d. Tensor s d -> Tensor s d\n" `T.isInfixOf` logText)
            @? T.unpack logText
          -- A sized binder prints sized (design §3.9, decision 6).
          (" sig keep forall (a : 3) d. Vec a d -> Vec a d\n" `T.isInfixOf` logText)
            @? T.unpack logText
          (" sig pair forall a b. a -> b -> (a, b)\n" `T.isInfixOf` logText)
            @? T.unpack logText
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.signatures @?= s.codebase.signatures
          linesIn loaded [":type same", ":type pair"]
            @?= Right
              [ "forall s d. Tensor s d -> Tensor s d"
              , "forall a b. a -> b -> (a, b)"
              ]
          userSignatures loaded.codebase @?= ["keep", "pair", "same"]
    ]

-- | The signatures a user wrote: the library's own (`linalg.vimap`) left out.
userSignatures :: Codebase -> [Text]
userSignatures cb = filter (not . isLibraryPath) (Map.keys cb.signatures)

-- Dimension syntax (design §4.1) -------------------------------------------------

dimensionSyntaxTests :: TestTree
dimensionSyntaxTests =
  testGroup
    "dimension syntax"
    [ testProperty "a printed dimension reads back as itself, in both spellings"
        $ checkCoverage
        $ timedForAll genWrittenDim
        $ \d ->
          let atoms = dimAtoms d
              downs = [k | (_, k) <- atoms, k < 0]
           in cover 3 (isDimOne d) "dimensionless"
                $ cover
                  5
                  (not (null downs) && all (\(_, k) -> k < 0) atoms)
                  "only negative powers"
                $ cover 10 (length downs > 1) "several factors below"
                $ cover 20 (any (\(_, k) -> abs k > 1) atoms) "a power above one"
                $ cover 20 (any (\(a, _) -> isVar a) atoms) "a variable"
                $ conjoin
                  [ counterexample (T.unpack written) (dimensionOf written === Right d)
                  | spelling <- [Ascii, Unicode]
                  , written <-
                      [ renderDimArgIn spelling varName d
                      , "(" <> renderDimIn spelling varName d <> ")"
                      ]
                  ]
    , testCase "the written forms: powers, grouping, left to right, 1, units" $ do
        let written t = typeOfTextP ("\\x -> (x :: " <> t <> ")")
            readsAs t printed = written t @?= Right (printed <> " -> " <> printed)
        readsAs "Num (m*s^-2)" "Num (m/s^2)"
        readsAs "Num (m·s⁻²)" "Num (m/s^2)"
        readsAs "Num (m/s/s)" "Num (m/s^2)"
        readsAs "Num (m/s*kg)" "Num (kg*m/s)"
        readsAs "Num ((m/s)^2)" "Num (m^2/s^2)"
        readsAs "Num (m²/(s²·K))" "Num (m^2/(s^2*K))"
        readsAs "Num (1/s)" "Num (1/s)"
        readsAs "Num (1/(s*K))" "Num (1/(s*K))"
        readsAs "Num 1" "Num"
        readsAs "Num (kg/kg)" "Num"
        readsAs "Num (m)" "Num m"
        readsAs "Vec 3 (m/s)" "Vec 3 (m/s)"
        -- A unit means its dimension.
        readsAs "Num km" "Num m"
        readsAs "Num N" "Num (kg*m/s^2)"
        readsAs "Num (km/h)" "Num (m/s)"
        runLinesP [":set unicode on", ":type \\x -> (x :: Num (kg*m^2/s^2))"]
          @?= Right ["Num (kg·m²/s²) → Num (kg·m²/s²)"]
    , testCase "a dimension standing alone prints without parentheses" $ do
        expectError (runLinesP ["3 m + 2 s"]) "dimensions differ by m/s"
        expectError (runLinesP ["(3 m :: Num kg)"]) "dimensions differ by kg/m"
        expectError (runLinesP ["3 m + 2"]) "dimensions differ by m"
        expectError (runLinesP ["1 / (1 s) + 1 / (1 K)"]) "dimensions differ by K/s"
    , testCase "a forall-bound name is a variable, any other a unit" $ do
        runLinesP
          [multiline ["f :: forall m. Num m -> Num m", "let f x = x"], ":type f"]
          @?= Right ["forall d. Num d -> Num d"]
        runLinesP [multiline ["f :: Num m -> Num m", "let f x = x"], ":type f"]
          @?= Right ["Num m -> Num m"]
        -- In a query, an unknown lowercase name is a variable and a unit a unit.
        runLinesP
          [ multiline ["f :: forall d. Num d -> Num (d*m)", "let f x = x * 1 m"]
          , ":ls f : Num d -> Num (d*m)"
          ]
          @?= Right ["f : forall d. Num d -> Num (m*d)"]
    , testCase "juxtaposition and @ are refused in a dimension" $ do
        let hint = "a dimension's product is written with * or ·, not by juxtaposition: write "
        expectError (runLinesP ["\\x -> (x :: Num (m s))"]) (hint <> "m*s")
        expectError (runLinesP ["\\x -> (x :: Num (m^2 s))"]) (hint <> "m*s")
        expectError (runLinesP ["\\x -> (x :: Num (kg/m s))"]) (hint <> "m*s")
        expectError (runLinesP ["data W = W (Num (kg m))"]) (hint <> "kg*m")
        expectError
          (runLinesP ["\\x -> (x :: Num (m@s))"])
          "`@` is the matrix product; a dimension's product is * or ·"
        expectError
          (runLinesP ["\\x -> (x :: Num (m*s@kg))"])
          "`@` is the matrix product; a dimension's product is * or ·"
        -- At the value level `·` is still `@`.
        evalText "[1, 2] · [3, 4]" @?= evalText "[1, 2] @ [3, 4]"
    , testCase "brackets are shapes only" $ do
        typeOfTextP "\\x -> (x :: Tensor [2, 3] (m/s))"
          @?= Right "Mat 2 3 (m/s) -> Mat 2 3 (m/s)"
        typeOfTextP "\\x -> (x :: Tensor [2, 3, 4] m)"
          @?= Right "Tensor [2, 3, 4] m -> Tensor [2, 3, 4] m"
        expectError
          (runLinesP ["\\x -> (x :: Num [m])"])
          "a dimension is a unit, a variable, 1, or a product of them in parentheses"
        expectError
          (runLinesP ["\\x -> (x :: Num [m s^-2])"])
          "unexpected"
    , testCase "a point or chart takes a frame" $ do
        typeOfTextP "\\p -> (p :: Point degC)"
          @?= Right "Point degC -> Point degC"
        typeOfTextP "\\c -> (c :: Chart degC)"
          @?= Right "Chart degC -> Chart degC"
        typeOfTextP "\\p -> (p :: Diff degC)" @?= Right "Num K -> Num K"
        expectError
          (runLinesP ["(20 degC :: Point (Num K))"])
          "a point and a chart are typed by a frame, a chart's name or a variable, as in Point degC"
        expectError
          (runLinesP ["(20 degC :: Point ITS90)"])
          "`ITS90` is a space; a point is on a frame of it, as in Point degC"
        expectError
          (runLinesP ["(491.67 degR :: Point degR)"])
          "`degR` is a rescaling and shares the frame of its parent: write Point kelvin"
        -- As an argument of a declared type, parenthesised.
        runLinesP
          [ "data P = P {temp :: Point degC}"
          , "data Q a = Q a"
          , ":type P"
          , ":type \\x -> {(x :: Point kelvin)}"
          , ":type \\x -> Q (x :: Chart degC)"
          ]
          @?= Right
            [ "Point degC -> P"
            , "Point kelvin -> {Point kelvin}"
            , "Chart degC -> Q (Chart degC)"
            ]
    , testCase "an error names variables as :type does, never as a unit" $ do
        -- A length variable beside metres is not called m.
        expectError
          ( runLinesP
              [ multiline
                  [ "f :: forall n k. Mat n k -> Mat n k m"
                  , "let f a = a / 1 s"
                  ]
              ]
          )
          "`f`'s definition has type `Tensor s1 d -> Tensor s1 (d/s)`, not as general as its signature `Mat n k -> Mat n k m`"
    , testCase ":type's output reads back as a signature equal to itself" $ do
        let defs =
              [ ("covariance", [])
              , ("vimap", [])
              , ("secs", ["let secs x = x * 1 s"])
              , ("mm", ["let mm a b = (a @ b) * 1 m"])
              , ("rate", ["let rate x = 1 / (x * x * 1 K)"])
              , -- over frames and spaces (design §3.10, F1)
                ("place", ["let place c x = pointOn c x"])
              , ("rel", ["let rel p q = p .- q"])
              , ("rot", ["let rot c = rotationOf c"])
              , ("conv", ["let conv p c = (p to c) .- (p to c)"])
              , ("temp", ["let temp p = p .- 0 degC"])
              , ("shift", ["let shift q = q .+ [1, 0, 0] m"])
              , ("shiftScalar", ["let shiftScalar q = q .+ 1 K"])
              , ("shiftBy", ["let shiftBy x q = q .+ [x + 0, x + 0, x + 0] m"])
              , ("withAxes", [])
              , ("velocityIn", [":use astro"])
              , ("stateFrom", [":use astro"])
              ]
        forM_ [[], [":set unicode on"]] $ \unicode ->
          forM_ defs $ \(name, setup) -> do
            let typeOf' lines' = lastN 1 <$> runLinesP (unicode ++ setup ++ lines')
            case typeOf' [":type " <> name] of
              Right [printed] ->
                typeOf' [multiline ["rt :: " <> printed, "let rt = " <> name], ":type rt"]
                  @?= Right [printed]
              other -> assertFailure (show other)
    ]
 where
  varName v = if v == 0 then "d" else "d" <> T.pack (show v)
  isVar = \case
    DVar _ -> True
    Base _ -> False
  -- The dimension a written one means, as the last argument of a signature
  -- whose first three are its variables, d, d1 and d2 in order.
  dimensionOf :: Text -> Either Text Dim
  dimensionOf written = do
    t <- parseType ("forall d d1 d2. Num d -> Num d1 -> Num d2 -> Num " <> written)
    Forall _ ty <-
      first (T.pack . show) (queryScheme seeded.scope seeded.codebase t)
    case ty of
      TFun _ (TFun _ (TFun _ (TTensor SNil d))) -> Right d
      other -> Left (renderType other)

-- | A dimension of base units and the variables 0 to 2, with powers to 3.
genWrittenDim :: Gen Dim
genWrittenDim = do
  n <- chooseInt (0, 4)
  dimFromAtoms
    <$> vectorOf
      n
      ( (,)
          <$> elements (map Base [minBound .. maxBound :: BaseDim] ++ map DVar [0, 1, 2])
          <*> elements [-3, -2, -1, 1, 2, 3]
      )
