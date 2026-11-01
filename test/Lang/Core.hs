{-# LANGUAGE PatternSynonyms #-}

-- | Core, typed Core, the evaluator and hashing.
module Lang.Core (
  coreTests,
  evalTests,
  tcoreTests,
  hashTests,
) where

import Data.Bifunctor (first)
import Data.Set qualified as Set (fromList)
import Data.Text (Text)
import Data.Text qualified as T (
  head,
  isInfixOf,
  isPrefixOf,
  length,
  unpack,
 )
import Lang.Common (
  bool,
  h,
  ifT,
  num,
  prim2,
  run,
  v0,
  v1,
  v2,
  (*.),
  (+.),
  (-.),
  (/.),
  (<.),
  (==.),
 )
import Metron.Builtin (falseC, trueC, pattern BoolT)
import Metron.Core (
  Fin (FZ),
  Label (Owner),
  Lit (LTensor),
  Nat (S, Z),
  NudgeKind (Bound),
  Term (
    App,
    Cycle,
    Lam,
    Let,
    Pack,
    Pow,
    PrimApp,
    Proj,
    Ref,
    Uncertain
  ),
  Vec (VCons, VNil),
  alphaEq,
  primArity,
  refs,
  showHash,
 )
import Metron.Desugar (
  desugarClosed,
  noResolver,
  renderDesugarError,
 )
import Metron.Hash (encodeTerm, hashTerm, placeholderHash)
import Metron.Infer (TypeError (..), elaborateClosed)
import Metron.Parser (parseExpr)
import Metron.TCore (
  TTerm (TCon, TLam, TLet, TLit, TPrimApp, TTyApp, TVr),
  lintClosed,
  renderTTerm,
 )
import Metron.Type (
  Arg (AType),
  Axis (AAnon),
  Len (LLit),
  Scheme (Forall),
  Type (TFun),
  noLookup,
  numT,
  vecT,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (
  assertBool,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )

prim1 :: Text -> Term n -> Term n
prim1 p a = PrimApp p [a]

runClosed :: Term Z -> Either Text Text
runClosed = run []

-- Core -------------------------------------------------------------------

coreTests :: TestTree
coreTests =
  testGroup
    "core"
    [ testCase "alphaEq ignores hints"
        $ alphaEq (Lam "x" (v0 +. num 1)) (Lam "y" (v0 +. num 1) :: Term Z) @?= True
    , testCase "alphaEq distinguishes structure"
        $ alphaEq (Lam "x" (v0 +. num 1)) (Lam "x" (v0 +. num 2) :: Term Z) @?= False
    , testCase "alphaEq distinguishes indices"
        $ alphaEq (Lam "x" (Lam "y" v0)) (Lam "x" (Lam "y" v1) :: Term Z) @?= False
    , testCase "alphaEq compares projection positions"
        $ alphaEq (Proj (Pack [num 1]) 0) (Proj (Pack [num 1]) 1 :: Term Z) @?= False
    , testCase "alphaEq compares cycles by bodies"
        $ let c1 = Cycle (VCons "a" VNil) (VCons (num 1) VNil) :: Term Z
              c2 = Cycle (VCons "b" VNil) (VCons (num 1) VNil) :: Term Z
              c3 =
                Cycle (VCons "a" (VCons "b" VNil)) (VCons (num 1) (VCons (num 1) VNil)) ::
                  Term Z
           in do
                alphaEq c1 c2 @?= True
                alphaEq c1 c3 @?= False
    , testCase "refs collects hashes"
        $ refs
          ( Lam "f" (App v0 (Ref (h "abc") Nothing "") +. Ref (h "def") (Just 1) "") ::
              Term Z
          )
          @?= Set.fromList [h "abc", h "def"]
    , testCase "primitive arities" $ do
        primArity "add" @?= Just 2
        primArity "not" @?= Just 1
        primArity "frobnicate" @?= Nothing
    ]

-- Evaluation (through elaboration and lint) ---------------------------------------

evalTests :: TestTree
evalTests =
  testGroup
    "evaluation"
    [ testCase "arithmetic is exact"
        $ runClosed ((num 1 /. num 3) *. num 3) @?= Right "1"
    , testCase "rationals render as fractions"
        $ runClosed (num 1 /. num 3 +. num 1 /. num 6) @?= Right "1/2"
    , testCase "lambda application"
        $ runClosed (App (Lam "x" (v0 *. num 2)) (num 21)) @?= Right "42"
    , testCase "curried application"
        $ runClosed (App (App (Lam "x" (Lam "y" (v1 -. v0))) (num 10)) (num 3))
          @?= Right "7"
    , testCase "let binds and shadows by index"
        $ runClosed (Let "x" (num 1) (Let "y" (num 2) (v1 +. v0 *. num 10)))
          @?= Right "21"
    , testCase "higher-order functions"
        $ let twice = Lam "f" (Lam "x" (App v1 (App v1 v0)))
              inc = Lam "n" (v0 +. num 1)
           in runClosed (App (App twice inc) (num 5)) @?= Right "7"
    , testCase "polymorphic let used at two types"
        $ let idF = Lam "x" v0
           in runClosed (Let "id" idF (ifT (App v0 (bool True)) (App v0 (num 1)) (num 2)))
                @?= Right "1"
    , testCase "eta-expanded primitive as a value"
        $ let add = Lam "a" (Lam "b" (v1 +. v0))
              applyTwice = Lam "f" (Lam "x" (App (App v1 v0) v0))
           in runClosed (App (App applyTwice add) (num 4)) @?= Right "8"
    , testCase "if is lazy in the untaken branch"
        $ runClosed (ifT (bool True) (num 1) (num 1 /. num 0)) @?= Right "1"
    , testCase "let is call-by-need"
        $ runClosed (Let "boom" (num 1 /. num 0) (num 2)) @?= Right "2"
    , testCase "unused lambda argument is never forced"
        $ runClosed (App (Lam "_" (num 3)) (num 1 /. num 0)) @?= Right "3"
    , testCase "and is lazy on the right"
        $ runClosed (prim2 "and" (bool False) (num 1 /. num 0 ==. num 1))
          @?= Right "false"
    , testCase "division by zero"
        $ runClosed (num 1 /. num 0) @?= Left "DivideByZero"
    , testCase "integer power, negative exponent"
        $ runClosed (Pow (num 2) (-3)) @?= Right "1/8"
    , testCase "zero to a negative power"
        $ runClosed (Pow (num 0) (-1)) @?= Left "DivideByZero"
    , testCase "comparisons and booleans"
        $ runClosed (prim2 "or" (num 2 <. num 1) (prim1 "not" (num 3 ==. num 4)))
          @?= Right "true"
    , testCase "rounding primitives"
        $ runClosed
          ( Pack
              [ prim1 "floor" (num (-(3 / 2)))
              , prim1 "ceil" (num (3 / 2))
              , prim1 "round" (num (5 / 2))
              ]
          )
          @?= Right "[-2, 2, 2]"
    , testCase "an ill-typed term is rejected before evaluation"
        $ runClosed (num 1 +. bool True) @?= Left "type error: expected Num, got Bool"
    , testCase "an unsaturated primitive is rejected by inference"
        $ runClosed (PrimApp "add" [num 1])
          @?= Left "type error: primitive add expects 2 arguments, got 1"
    , testCase "vector and matrix literals"
        $ runClosed (Pack [Pack [num 1, num 0], Pack [num 0, num 1 /. num 2]])
          @?= Right "[[1, 0], [0, 1/2]]"
    , testCase "projection of a vector component"
        $ runClosed (Proj (Pack [num 1, num 2, num 3]) 1) @?= Right "2"
    , testCase "projection of a matrix row, then a component"
        $ let m = Pack [Pack [num 1, num 2], Pack [num 3, num 4]]
           in do
                runClosed (Proj m 1) @?= Right "[3, 4]"
                runClosed (Proj (Proj m 1) 0) @?= Right "3"
    , testCase "projection is lazy in the other components"
        $ runClosed (Proj (Pack [num 1 /. num 0, num 2]) 1) @?= Right "2"
    , testCase "projection out of range is a static error"
        $ runClosed (Proj (Pack [num 1, num 2]) 2)
          @?= Left "type error: position 2 is out of range for a vector of length 2"
    , testCase "ref to a plain definition"
        $ run [(h "k", num 5)] (Ref (h "k") Nothing "" +. num 1) @?= Right "6"
    , testCase "unknown ref"
        $ runClosed (Ref (h "nope") Nothing "")
          @?= Left "type error: reference to a definition with no stored type"
    , testCase "self-recursion through a cycle: factorial"
        $ let
            -- inside the body: v0 is n, v1 is fact (the cycle member)
            fact =
              Lam "n"
                $ ifT
                  (v0 ==. num 0)
                  (num 1)
                  (v0 *. App v1 (v0 -. num 1))
            defs = [(h "fact", Cycle (VCons "fact" VNil) (VCons fact VNil))]
           in
            run defs (App (Ref (h "fact") (Just 0) "") (num 10)) @?= Right "3628800"
    , testCase "mutual recursion through a cycle: even and odd"
        $ let
            -- members: 0 = even, 1 = odd. Inside a Lam, v0 is n, v1 is even,
            -- v2 is odd.
            even' = Lam "n" (ifT (v0 ==. num 0) (bool True) (App v2 (v0 -. num 1)))
            odd' = Lam "n" (ifT (v0 ==. num 0) (bool False) (App v1 (v0 -. num 1)))
            defs =
              [
                ( h "eo"
                , Cycle (VCons "even" (VCons "odd" VNil)) (VCons even' (VCons odd' VNil))
                )
              ]
           in
            do
              run defs (App (Ref (h "eo") (Just 0) "") (num 10)) @?= Right "true"
              run defs (App (Ref (h "eo") (Just 1) "") (num 10)) @?= Right "false"
    , testCase "bad cycle index is a static error"
        $ let defs = [(h "c", Cycle (VCons "a" VNil) (VCons (num 1) VNil))]
           in run defs (Ref (h "c") (Just 3) "")
                @?= Left "type error: reference to a cycle member that does not exist"
    , testCase "a zero-width ± is exact"
        $ runClosed (Uncertain Bound (Owner "") (num 1) (num 0)) @?= Right "1"
    ]

-- Typed Core ---------------------------------------------------------------------

elabText :: Text -> Either Text (TTerm Z)
elabText src = do
  e <- parseExpr src
  (t, _) <- either (Left . renderDesugarError) Right (desugarClosed noResolver e)
  (_, typed) <-
    first (("type error: " <>) . (.message)) (elaborateClosed noLookup t)
  _ <- first ("lint: " <>) (lintClosed noLookup typed)
  pure typed

showCore :: TTerm Z -> Text
showCore = renderTTerm (\_ _ _ -> "#ref") VNil

tcoreTests :: TestTree
tcoreTests =
  testGroup
    "typed core"
    [ testCase "a polymorphic function gets an explicit type abstraction"
        $ showCore <$> elabText "\\x -> x" @?= Right "Λt0. \\(x : t0) -> x"
    , testCase "a polymorphic let is instantiated explicitly at each use"
        $ showCore <$> elabText "let id x = x in if id true then id 1 else 2"
          @?= Right
            "let id : t0 -> t0 = Λt0. \\(x : t0) -> x in if id @Bool true then id @Num 1 else 2"
    , testCase "length polymorphism is explicit too"
        $ showCore <$> elabText "\\v -> v.0 + 1"
          @?= Right "Λn3. \\(v : Vec (n3 + 1)) -> add v.0 1"
    , testCase "shape polymorphism is explicit too"
        $ showCore <$> elabText "\\v -> v.0"
          @?= Right "Λn1. Λs2. Λd3. \\(v : Tensor (n1 + 1 : s2) d3) -> v.0"
    , testCase "primitives record the type they are used at"
        $ showCore <$> elabText "1 == 2" @?= Right "eq 1 2"
    , testCase "a slice's positions print as whole numbers, a fraction as a decimal" $ do
        -- They printed as `slice 1.0 0.0 t`.
        T.isInfixOf "-> slice 1 0 t" . showCore <$> elabText "\\t -> slice 1 0 t"
          @?= Right True
        showCore <$> elabText "0.5" @?= Right "0.5"
    , testCase "lint accepts everything elaboration produces"
        $ mapM_
          (either (assertFailure . T.unpack) (const (pure ())) . elabText)
          [ "\\f x -> f (f x)"
          , "let twice f x = f (f x) in twice (\\n -> n + 1) 0"
          , "[[1, 2], [3, 4]].1.0 + [1, 2, 3].2"
          , "if 1 < 2 then [1] else [2]"
          , "let first v = v.0 in first [1, 2] + first [3]"
          ]
    , testCase "lint rejects a badly annotated term"
        $ lintClosed
          noLookup
          ( TLam
              "x"
              BoolT
              ( TPrimApp
                  "add"
                  (TFun numT (TFun numT numT))
                  [TVr FZ, TLit (LTensor ([], [1])) []]
              )
          )
          @?= Left "argument of add has type Bool, expected Num"
    , testCase
        "lint rejects a primitive at a type that is not an instance of its scheme"
        $ lintClosed
          noLookup
          ( TPrimApp
              "add"
              (TFun BoolT (TFun BoolT BoolT))
              [TCon trueC BoolT [], TCon falseC BoolT []]
          )
          @?= Left
            "primitive add used at Bool -> Bool -> Bool, not an instance of Tensor s d -> Tensor s d -> Tensor s d"
    , testCase "lint rejects timap with an index shorter than the rank" $ do
        let at n =
              TPrimApp
                "timap"
                ( TFun
                    (TFun (vecT (LLit n)) (TFun numT numT))
                    (TFun (vecT (LLit 3)) (vecT (LLit 3)))
                )
                [ TLam "i" (vecT (LLit n)) (TLam "x" numT (TVr FZ))
                , TLit (LTensor ([3], [1, 2, 3])) [AAnon]
                ]
        lintClosed noLookup (at 1) @?= Right [Forall [] (vecT (LLit 3))]
        case lintClosed noLookup (at 2) of
          Left err -> T.isInfixOf "not an instance of" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a mismatched let annotation"
        $ case lintClosed
          noLookup
          (TLet "x" (Forall [] BoolT) (TLit (LTensor ([], [1])) []) (TVr FZ)) of
          Left err -> T.isPrefixOf "let binder annotated" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a type application without an abstraction"
        $ lintClosed noLookup (TTyApp (TLit (LTensor ([], [1])) []) (AType BoolT))
          @?= Left "type application to a term with no type abstraction"
    ]

-- Hashing ---------------------------------------------------------------------

hashTests :: TestTree
hashTests =
  testGroup
    "hash"
    [ testCase "alpha-equivalent terms hash equal"
        $ hashTerm (Lam "x" (v0 +. num 1)) @?= hashTerm (Lam "y" (v0 +. num 1))
    , testCase "different terms hash differently"
        $ assertBool "collision" (hashTerm (num 5) /= hashTerm (num 2 +. num 3))
    , testCase "rationals in lowest terms share an encoding"
        $ encodeTerm (num (2 / 4)) @?= encodeTerm (num (1 / 2))
    , testCase "short hash form" $ do
        let s = showHash (hashTerm (num 1))
        T.length s @?= 6
        T.head s @?= '#'
    , testCase "placeholder hash ignores which cycle variable is used"
        $ let a = App v0 (num 1) :: Term (S (S Z))
              b = App v1 (num 1) :: Term (S (S Z))
           in placeholderHash a @?= placeholderHash b
    , testCase "placeholder hash still sees structure"
        $ let a = App v0 (num 1) :: Term (S Z)
              b = App v0 (num 2) :: Term (S Z)
           in assertBool "collision" (placeholderHash a /= placeholderHash b)
    ]
