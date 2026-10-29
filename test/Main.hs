module Main (main) where

import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Desugar
import Eval.Driver
import Eval.Eval
import Eval.Hash
import Eval.Infer (TypeError (..), elaborateClosed)
import Eval.TCore
import Eval.Type
import Eval.Lexer hiding (TNum, TProj)
import Eval.Lexer qualified as L
import Eval.Parser
import Eval.Prelude (preludeNames)
import Eval.Pretty
import Eval.Syntax qualified as S
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main =
  defaultMain
    (testGroup "eval" [coreTests, evalTests, tcoreTests, lexerTests, parserTests, desugarTests, hashTests, prettyTests, endToEndTests, codebaseTests, typeTests, soundnessTests, productTests, propertyTests, unitTests, lintRegressionTests, preludeTests, displayTests])

-- Term-building helpers -------------------------------------------------

num :: Rational -> Term n
num r = Lit (LTensor [] [r])

bool :: Bool -> Term n
bool = Lit . LBool

prim2 :: Text -> Term n -> Term n -> Term n
prim2 p a b = PrimApp p [a, b]

prim1 :: Text -> Term n -> Term n
prim1 p a = PrimApp p [a]

(+.), (-.), (*.), (/.), (==.), (<.) :: Term n -> Term n -> Term n
(+.) = prim2 "add"
(-.) = prim2 "sub"
(*.) = prim2 "outer"
(/.) = prim2 "div"
(==.) = prim2 "eq"
(<.) = prim2 "lt"
infixl 6 +., -.
infixl 7 *., /.
infix 4 ==., <.

v0 :: Term (S n)
v0 = Var FZ

v1 :: Term (S (S n))
v1 = Var (FS FZ)

v2 :: Term (S (S (S n)))
v2 = Var (FS (FS FZ))
-- Codebase stand-in: hashes are just labels here. Definitions are elaborated
-- in order, so later ones may reference earlier ones.
h :: ByteString -> Hash
h = Hash

type Defs = [(Hash, Term Z)]

elaborateDefs :: Defs -> Either Text [(Hash, ([Scheme], TTerm Z))]
elaborateDefs = go []
  where
    go acc [] = Right (reverse acc)
    go acc ((k, t) : rest) = do
      (schemes, typed) <- first (("type error: " <>) . (.message)) (elaborateClosed (typesIn acc) t)
      _ <- first ("lint: " <>) (lintClosed (typesIn acc) typed)
      go ((k, (schemes, typed)) : acc) rest
    typesIn acc k = fst <$> lookup k acc

-- | Elaborate, lint, evaluate and render a closed term against some
-- definitions. Type errors, lint failures and evaluation errors all come
-- back as text.
run :: Defs -> Term Z -> Either Text Text
run defs t = do
  elaborated <- elaborateDefs defs
  let typesOf k = fst <$> lookup k elaborated
      typedOf k = snd <$> lookup k elaborated
  (_, typed) <- first (("type error: " <>) . (.message)) (elaborateClosed typesOf t)
  _ <- first ("lint: " <>) (lintClosed typesOf typed)
  v <- first (T.pack . show) (evalClosed defaultConfig (Runtime typedOf (\_ _ -> False)) typed)
  first (T.pack . show) (render v)

runClosed :: Term Z -> Either Text Text
runClosed = run []

-- Core -------------------------------------------------------------------

coreTests :: TestTree
coreTests =
  testGroup
    "core"
    [ testCase "alphaEq ignores hints" $
        alphaEq (Lam "x" (v0 +. num 1)) (Lam "y" (v0 +. num 1) :: Term Z) @?= True
    , testCase "alphaEq distinguishes structure" $
        alphaEq (Lam "x" (v0 +. num 1)) (Lam "x" (v0 +. num 2) :: Term Z) @?= False
    , testCase "alphaEq distinguishes indices" $
        alphaEq (Lam "x" (Lam "y" v0)) (Lam "x" (Lam "y" v1) :: Term Z) @?= False
    , testCase "alphaEq compares projection positions" $
        alphaEq (Proj (Pack [num 1]) 0) (Proj (Pack [num 1]) 1 :: Term Z) @?= False
    , testCase "alphaEq compares cycles by bodies" $
        let c1 = Cycle (VCons "a" VNil) (VCons (num 1) VNil) :: Term Z
            c2 = Cycle (VCons "b" VNil) (VCons (num 1) VNil) :: Term Z
            c3 = Cycle (VCons "a" (VCons "b" VNil)) (VCons (num 1) (VCons (num 1) VNil)) :: Term Z
         in do
              alphaEq c1 c2 @?= True
              alphaEq c1 c3 @?= False
    , testCase "refs collects hashes" $
        refs (Lam "f" (App v0 (Ref (h "abc") Nothing) +. Ref (h "def") (Just 1)) :: Term Z)
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
    "eval"
    [ testCase "arithmetic is exact" $
        runClosed ((num 1 /. num 3) *. num 3) @?= Right "1"
    , testCase "rationals render as fractions" $
        runClosed (num 1 /. num 3 +. num 1 /. num 6) @?= Right "1/2"
    , testCase "lambda application" $
        runClosed (App (Lam "x" (v0 *. num 2)) (num 21)) @?= Right "42"
    , testCase "curried application" $
        runClosed (App (App (Lam "x" (Lam "y" (v1 -. v0))) (num 10)) (num 3)) @?= Right "7"
    , testCase "let binds and shadows by index" $
        runClosed (Let "x" (num 1) (Let "y" (num 2) (v1 +. v0 *. num 10))) @?= Right "21"
    , testCase "higher-order functions" $
        let twice = Lam "f" (Lam "x" (App v1 (App v1 v0)))
            inc = Lam "n" (v0 +. num 1)
         in runClosed (App (App twice inc) (num 5)) @?= Right "7"
    , testCase "polymorphic let used at two types" $
        let idF = Lam "x" v0
         in runClosed (Let "id" idF (If (App v0 (bool True)) (App v0 (num 1)) (num 2))) @?= Right "1"
    , testCase "eta-expanded primitive as a value" $
        let add = Lam "a" (Lam "b" (v1 +. v0))
            applyTwice = Lam "f" (Lam "x" (App (App v1 v0) v0))
         in runClosed (App (App applyTwice add) (num 4)) @?= Right "8"
    , testCase "if is lazy in the untaken branch" $
        runClosed (If (bool True) (num 1) (num 1 /. num 0)) @?= Right "1"
    , testCase "let is call-by-need" $
        runClosed (Let "boom" (num 1 /. num 0) (num 2)) @?= Right "2"
    , testCase "unused lambda argument is never forced" $
        runClosed (App (Lam "_" (num 3)) (num 1 /. num 0)) @?= Right "3"
    , testCase "and is lazy on the right" $
        runClosed (prim2 "and" (bool False) (num 1 /. num 0 ==. num 1)) @?= Right "false"
    , testCase "division by zero" $
        runClosed (num 1 /. num 0) @?= Left "DivideByZero"
    , testCase "integer power, negative exponent" $
        runClosed (Pow (num 2) (-3)) @?= Right "1/8"
    , testCase "zero to a negative power" $
        runClosed (Pow (num 0) (-1)) @?= Left "DivideByZero"
    , testCase "comparisons and booleans" $
        runClosed (prim2 "or" (num 2 <. num 1) (prim1 "not" (num 3 ==. num 4))) @?= Right "true"
    , testCase "rounding primitives" $
        runClosed (Pack [prim1 "floor" (num (-3 / 2)), prim1 "ceil" (num (3 / 2)), prim1 "round" (num (5 / 2))])
          @?= Right "[-2, 2, 2]"
    , testCase "an ill-typed term is rejected before evaluation" $
        runClosed (num 1 +. bool True) @?= Left "type error: expected Num, got Bool"
    , testCase "an unsaturated primitive is rejected by inference" $
        runClosed (PrimApp "add" [num 1]) @?= Left "type error: primitive add expects 2 arguments, got 1"
    , testCase "vector and matrix literals" $
        runClosed (Pack [Pack [num 1, num 0], Pack [num 0, num 1 /. num 2]]) @?= Right "[[1, 0], [0, 1/2]]"
    , testCase "projection of a vector component" $
        runClosed (Proj (Pack [num 1, num 2, num 3]) 1) @?= Right "2"
    , testCase "projection of a matrix row, then a component" $
        let m = Pack [Pack [num 1, num 2], Pack [num 3, num 4]]
         in do
              runClosed (Proj m 1) @?= Right "[3, 4]"
              runClosed (Proj (Proj m 1) 0) @?= Right "3"
    , testCase "projection is lazy in the other components" $
        runClosed (Proj (Pack [num 1 /. num 0, num 2]) 1) @?= Right "2"
    , testCase "projection out of range is a static error" $
        runClosed (Proj (Pack [num 1, num 2]) 2) @?= Left "type error: position 2 is out of range for a vector of length 2"
    , testCase "ref to a plain definition" $
        run [(h "k", num 5)] (Ref (h "k") Nothing +. num 1) @?= Right "6"
    , testCase "unknown ref" $
        runClosed (Ref (h "nope") Nothing) @?= Left "type error: reference to a definition with no stored type"
    , testCase "self-recursion through a cycle: factorial" $
        let -- inside the body: v0 is n, v1 is fact (the cycle member)
            fact =
              Lam "n" $
                If
                  (v0 ==. num 0)
                  (num 1)
                  (v0 *. App v1 (v0 -. num 1))
            defs = [(h "fact", Cycle (VCons "fact" VNil) (VCons fact VNil))]
         in run defs (App (Ref (h "fact") (Just 0)) (num 10)) @?= Right "3628800"
    , testCase "mutual recursion through a cycle: even and odd" $
        let -- members: 0 = even, 1 = odd. Inside a Lam, v0 is n, v1 is even,
            -- v2 is odd.
            even' = Lam "n" (If (v0 ==. num 0) (bool True) (App v2 (v0 -. num 1)))
            odd' = Lam "n" (If (v0 ==. num 0) (bool False) (App v1 (v0 -. num 1)))
            defs = [(h "eo", Cycle (VCons "even" (VCons "odd" VNil)) (VCons even' (VCons odd' VNil)))]
         in do
              run defs (App (Ref (h "eo") (Just 0)) (num 10)) @?= Right "true"
              run defs (App (Ref (h "eo") (Just 1)) (num 10)) @?= Right "false"
    , testCase "bad cycle index is a static error" $
        let defs = [(h "c", Cycle (VCons "a" VNil) (VCons (num 1) VNil))]
         in run defs (Ref (h "c") (Just 3)) @?= Left "type error: reference to a cycle member that does not exist"
    , testCase "affine constructs are not yet supported" $
        runClosed (Uncertain Bound (num 1) (num 0)) @?= Left "Unsupported \"\\177: affine arithmetic is not implemented yet\""
    ]

-- Typed Core ---------------------------------------------------------------------

elabText :: Text -> Either Text (TTerm Z)
elabText src = do
  e <- parseExpr src
  (t, _) <- either (Left . renderDesugarError) Right (desugarClosed noResolver e)
  (_, typed) <- first (("type error: " <>) . (.message)) (elaborateClosed (const Nothing) t)
  _ <- first ("lint: " <>) (lintClosed (const Nothing) typed)
  pure typed

showCore :: TTerm Z -> Text
showCore = renderTTerm (\_ _ -> "#ref") VNil

tcoreTests :: TestTree
tcoreTests =
  testGroup
    "typed core"
    [ testCase "a polymorphic function gets an explicit type abstraction" $
        showCore <$> elabText "\\x -> x" @?= Right "Λt0. \\(x : t0) -> x"
    , testCase "a polymorphic let is instantiated explicitly at each use" $
        showCore <$> elabText "let id x = x in if id true then id 1 else 2"
          @?= Right "let id : t0 -> t0 = Λt0. \\(x : t0) -> x in if id @Bool true then id @Num 1.0 else 2.0"
    , testCase "length polymorphism is explicit too" $
        showCore <$> elabText "\\v -> v.0 + 1" @?= Right "Λn3. \\(v : Vec (n3 + 1)) -> add v.0 1.0"
    , testCase "shape polymorphism is explicit too" $
        showCore <$> elabText "\\v -> v.0" @?= Right "Λn1. Λs2. Λd3. \\(v : Tensor (n1 + 1 : s2) d3) -> v.0"
    , testCase "primitives record the type they are used at" $
        showCore <$> elabText "1 == 2" @?= Right "eq 1.0 2.0"
    , testCase "lint accepts everything elaboration produces" $
        mapM_
          (\src -> either (assertFailure . T.unpack) (const (pure ())) (elabText src))
          [ "\\f x -> f (f x)"
          , "let twice f x = f (f x) in twice (\\n -> n + 1) 0"
          , "[[1, 2], [3, 4]].1.0 + [1, 2, 3].2"
          , "if 1 < 2 then [1] else [2]"
          , "let first v = v.0 in first [1, 2] + first [3]"
          ]
    , testCase "lint rejects a badly annotated term" $
        lintClosed (const Nothing) (TLam "x" TBool (TPrimApp "add" (TFun numT (TFun numT numT)) [TVr FZ, TLit (LTensor [] [1])]))
          @?= Left "argument of add has type Bool, expected Num"
    , testCase "lint rejects a primitive at a type that is not an instance of its scheme" $
        lintClosed (const Nothing) (TPrimApp "add" (TFun TBool (TFun TBool TBool)) [TLit (LBool True), TLit (LBool False)])
          @?= Left "primitive add used at Bool -> Bool -> Bool, not an instance of Tensor s d -> Tensor s d -> Tensor s d"
    , testCase "lint rejects a mismatched let annotation" $
        case lintClosed (const Nothing) (TLet "x" (Forall [] TBool) (TLit (LTensor [] [1])) (TVr FZ)) of
          Left err -> T.isPrefixOf "let binder annotated" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a type application without an abstraction" $
        lintClosed (const Nothing) (TTyApp (TLit (LTensor [] [1])) (AType TBool))
          @?= Left "type application to a term with no type abstraction"
    ]


-- Lexer ----------------------------------------------------------------------

toks :: Text -> Either Text [Token]
toks src = map (.value) <$> tokenize src

lexerTests :: TestTree
lexerTests =
  testGroup
    "lexer"
    [ testCase "numbers are exact rationals" $
        toks "9.81 1e-3 1_000 2E2" @?= Right [L.TNum (981 / 100), L.TNum (1 / 1000), L.TNum 1000, L.TNum 200]
    , testCase "keywords and identifiers" $
        toks "let x' = true in x'" @?= Right [TKw KLet, TIdent "x'", TEquals, TKw KTrue, TKw KIn, TIdent "x'"]
    , testCase "unicode operators map to canonical tokens" $
        toks "λx → x ⊗ 2 ÷ 3 ≤ 4 && ¬false"
          @?= Right [TLambda, TIdent "x", TArrow, TIdent "x", TOp "*", L.TNum 2, TOp "/", L.TNum 3, TOp "<=", L.TNum 4, TOp "&&", TIdent "not", TKw KFalse]
    , testCase "plus-minus spellings" $
        toks "a ± 1 ±σ 2 +- 3 +-s 4"
          @?= Right [TIdent "a", TPlusMinus Bound, L.TNum 1, TPlusMinus Stat, L.TNum 2, TPlusMinus Bound, L.TNum 3, TPlusMinus Stat, L.TNum 4]
    , testCase "glued superscripts" $
        toks "m² s⁻² x³" @?= Right [TIdent "m", TSup 2, TIdent "s", TSup (-2), TIdent "x", TSup 3]
    , testCase "superscript must be glued" $
        either (const True) (const False) (toks "m ²") @? "expected an error"
    , testCase "projections" $
        toks "v.0 m.1.2 r.12" @?= Right [TIdent "v", L.TProj 0, TIdent "m", L.TProj 1, L.TProj 2, TIdent "r", L.TProj 12]
    , testCase "a dot followed by letters is composition, not a projection" $
        toks "r.x" @?= Right [TIdent "r", TOp ".", TIdent "x"]
    , testCase "dot with spaces is composition, .xs is not a projection" $
        toks "f . g" @?= Right [TIdent "f", TOp ".", TIdent "g"]
    , testCase "projection must be glued to an atom" $
        either (const True) (const False) (toks "v .0") @? "expected an error"
    , testCase "degree and primes are unit identifiers" $
        toks "45° 30′ 15″ π" @?= Right [L.TNum 45, TIdent "deg", L.TNum 30, TIdent "arcmin", L.TNum 15, TIdent "arcsec", TIdent "pi"]
    , testCase "confusables fold: micro sign and ohm sign" $
        toks "\x00B5m \x2126" @?= Right [TIdent "\x03BCm", TIdent "\x03A9"]
    , testCase "NFC: a decomposed accent becomes one character" $
        toks "caf\x0065\x0301" @?= Right [TIdent "caf\x00E9"]
    , testCase "comments; a token after a comment on a new line is a continuation" $
        toks "1 -- one\n{- block {- nested -} -} 2" @?= Right [L.TNum 1, L.TNum 2]
    , testCase "a comment line between statements" $
        toks "1\n-- note\n2" @?= Right [L.TNum 1, TSep, L.TNum 2]
    , testCase "layout: column-zero newlines separate statements" $
        toks "let x = 1\nx\n  + 1\n;y" @?= Right [TKw KLet, TIdent "x", TEquals, L.TNum 1, TSep, TIdent "x", TOp "+", L.TNum 1, TSep, TIdent "y"]
    , testCase "layout: where block" $
        toks "let f x = k where\n  k = 2\n  j = 3\nf 1"
          @?= Right
            [ TKw KLet, TIdent "f", TIdent "x", TEquals, TIdent "k", TKw KWhere
            , TIdent "k", TEquals, L.TNum 2, TSep, TIdent "j", TEquals, L.TNum 3, TBlockEnd
            , TSep, TIdent "f", L.TNum 1
            ]
    ]

-- Parser ---------------------------------------------------------------------

-- | Parse and strip spans so that structure can be compared.
parseShape :: Text -> Either Text Tree
parseShape src = shape <$> parseExpr src

data Tree
  = N Rational
  | B Bool
  | V Text
  | L [Text] Tree
  | A Tree Tree
  | Lt Text [Text] Tree Tree
  | I Tree Tree Tree
  | O S.Op Tree Tree
  | Ng Tree
  | P Tree Integer
  | SL S.Op Tree
  | SR Tree S.Op
  | Vc [Tree]
  | Pj Tree Int
  deriving stock (Eq, Show)

shape :: S.Expr -> Tree
shape e = case e.node of
  S.Num r -> N r
  S.Bool b -> B b
  S.Var x -> V x
  S.Lam ns b -> L (map (.text) ns) (shape b)
  S.App f a -> A (shape f) (shape a)
  S.Let n ps r b -> Lt n.text (map (.text) ps) (shape r) (shape b)
  S.If c t f -> I (shape c) (shape t) (shape f)
  S.BinOp o a b -> O o (shape a) (shape b)
  S.Neg a -> Ng (shape a)
  S.Pow a n -> P (shape a) n
  S.SectionL o a -> SL o (shape a)
  S.SectionR a o -> SR (shape a) o
  S.Vec es -> Vc (map shape es)
  S.Proj a i -> Pj (shape a) i

parserTests :: TestTree
parserTests =
  testGroup
    "parser"
    [ testCase "precedence: * over +" $
        parseShape "1 + 2 * 3" @?= Right (O S.Add (N 1) (O S.Outer (N 2) (N 3)))
    , testCase "left associativity of -" $
        parseShape "10 - 3 - 2" @?= Right (O S.Sub (O S.Sub (N 10) (N 3)) (N 2))
    , testCase "application binds tighter than operators" $
        parseShape "f x + g y" @?= Right (O S.Add (A (V "f") (V "x")) (A (V "g") (V "y")))
    , testCase "power binds tighter than unary minus and application looser than power" $
        parseShape "-f x ^ 2" @?= Right (Ng (P (A (V "f") (V "x")) 2))
    , testCase "negative literal exponent and superscript" $
        parseShape "x ^ -2 + y²" @?= Right (O S.Add (P (V "x") (-2)) (P (V "y") 2))
    , testCase "quantity rule: 9.81 m/s^2" $
        parseShape "9.81 m/s^2" @?= Right (O S.Div (O S.Outer (N (981 / 100)) (V "m")) (P (V "s") 2))
    , testCase "quantity rule: 3 m^2 kg and superscripts" $
        parseShape "3 m² kg" @?= Right (O S.Outer (O S.Outer (N 3) (P (V "m") 2)) (V "kg"))
    , testCase "quantity rule: 5 km/h" $
        parseShape "5 km/h" @?= Right (O S.Div (O S.Outer (N 5) (V "km")) (V "h"))
    , testCase "quantity rule: 3 f x is a product, 3 (f x) too" $ do
        parseShape "3 f x" @?= Right (O S.Outer (O S.Outer (N 3) (V "f")) (V "x"))
        parseShape "3 (f x)" @?= Right (O S.Outer (N 3) (A (V "f") (V "x")))
    , testCase "vector literal with units" $
        parseShape "[1, 0, 0] km" @?= Right (O S.Outer (Vc [N 1, N 0, N 0]) (V "km"))
    , testCase "degree sign" $
        parseShape "45°" @?= Right (O S.Outer (N 45) (V "deg"))
    , testCase "lambda with several parameters extends right" $
        parseShape "\\x y -> x + y" @?= Right (L ["x", "y"] (O S.Add (V "x") (V "y")))
    , testCase "let in" $
        parseShape "let f x = x * 2 in f 3" @?= Right (Lt "f" ["x"] (O S.Outer (V "x") (N 2)) (A (V "f") (N 3)))
    , testCase "if then else" $
        parseShape "if a < b then a else b" @?= Right (I (O S.Lt (V "a") (V "b")) (V "a") (V "b"))
    , testCase "comparison is non-associative" $
        either (const True) (const False) (parseShape "1 < 2 < 3") @? "expected an error"
    , testCase "sections" $ do
        parseShape "(+ 1)" @?= Right (SL S.Add (N 1))
        parseShape "(2 *)" @?= Right (SR (N 2) S.Outer)
        parseShape "(- 1)" @?= Right (Ng (N 1))
    , testCase "backtick infix and composition" $ do
        parseShape "a `dot` b" @?= Right (O (S.Infix "dot") (V "a") (V "b"))
        parseShape "f . g" @?= Right (O S.Compose (V "f") (V "g"))
    , testCase "projections" $
        parseShape "m.1.2 + v.0" @?= Right (O S.Add (Pj (Pj (V "m") 1) 2) (Pj (V "v") 0))
    , testCase "matrix literal" $
        parseShape "[[1, 0], [0, 1]]" @?= Right (Vc [Vc [N 1, N 0], Vc [N 0, N 1]])
    , testCase "a ragged literal parses; the type checker rejects it" $ do
        either (const False) (const True) (parseShape "[[1, 0], [1]]") @? "expected a parse"
        case evalText "[[1, 0], [1]]" of
          Left err -> T.isInfixOf "same shape" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "sqrt prefix and ± operators" $
        parseShape "√x ± 1" @?= Right (O (S.PlusMinus Bound) (A (V "sqrt") (V "x")) (N 1))
    , testCase "to has the lowest precedence" $
        parseShape "5 km / h to m / s" @?= Right (O S.To (O S.Div (O S.Outer (N 5) (V "km")) (V "h")) (O S.Div (V "m") (V "s")))
    , testCase "statements with where" $
        case parseProgram "let f x = x * k where k = 2\nf 3" of
          Right [S.SLet b, S.SExpr e] -> do
            b.name.text @?= "f"
            shape b.body @?= Lt "k" [] (N 2) (O S.Outer (V "x") (V "k"))
            shape e @?= A (V "f") (N 3)
          other -> assertFailure ("unexpected parse: " <> show other)
    ]

-- Desugar ---------------------------------------------------------------------

desugarText :: Text -> Either Text (Term Z)
desugarText src = do
  e <- parseExpr src
  either (Left . renderDesugarError) (Right . fst) (desugarClosed noResolver e)

-- | Core has no 'Eq' (hints are not part of its meaning), so compare up to
-- alpha-equivalence.
desugarsTo :: Text -> Term Z -> Assertion
desugarsTo src expected = case desugarText src of
  Left err -> assertFailure (T.unpack err)
  Right t -> assertBool ("expected " <> show expected <> "\n but got  " <> show t) (alphaEq t expected)

desugarFails :: Text -> Text -> Assertion
desugarFails src expected = case desugarText src of
  Left err -> err @?= expected
  Right t -> assertFailure ("expected an error, got " <> show t)

desugarTests :: TestTree
desugarTests =
  testGroup
    "desugar"
    [ testCase "operators become saturated primitives" $
        desugarsTo "1 + 2 * 3" (num 1 +. num 2 *. num 3)
    , testCase "bound variables become indices" $
        desugarsTo "\\x y -> x - y" (Lam "x" (Lam "y" (v1 -. v0)))
    , testCase "shadowing picks the innermost binder" $
        desugarsTo "\\x -> \\x -> x" (Lam "x" (Lam "x" v0))
    , testCase "let with parameters becomes a lambda" $
        desugarsTo "let f x = x in f" (Let "f" (Lam "x" v0) v0)
    , testCase "partial primitive is eta-expanded" $
        desugarsTo "(+ 1)" (Lam "x" (v0 +. num 1))
    , testCase "bare primitive is eta-expanded to its arity" $
        desugarsTo "sqrt" (Lam "x" (PrimApp "sqrt" [v0]))
    , testCase "over-applied primitive is applied further" $
        desugarsTo "not true 1" (App (PrimApp "not" [bool True]) (num 1))
    , testCase "zero-arity primitive" $
        desugarsTo "pi" (PrimApp "pi" [])
    , testCase "unknown name" $
        desugarFails "x + 1" "1:1: unknown name `x`"
    , testCase "composition" $
        desugarsTo "\\f g -> f . g" (Lam "f" (Lam "g" (Lam "x" (App v2 (App v1 v0)))))
    , testCase "provenance records the root span" $
        case parseExpr "1 + 2" >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
          Right (_, prov) -> Map.lookup [] prov @?= Just (S.Span (S.Pos 1 1) (S.Pos 1 6))
          Left err -> assertFailure (T.unpack err)
    , testCase "provenance records children by path" $
        case parseExpr "1 + 20" >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
          Right (_, prov) -> Map.lookup [1] prov @?= Just (S.Span (S.Pos 1 5) (S.Pos 1 7))
          Left err -> assertFailure (T.unpack err)
    , testCase "a resolver turns free names into references" $
        let resolver n = if n == "k" then Just (h "kay", Nothing) else Nothing
         in case parseExpr "k + 1" >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
              Right (t, _) -> assertBool (show t) (alphaEq t (Ref (h "kay") Nothing +. num 1 :: Term Z))
              Left err -> assertFailure (T.unpack err)
    , testCase "codebase names shadow primitives" $
        let resolver n = if n == "sqrt" then Just (h "mine", Nothing) else Nothing
         in case parseExpr "sqrt 4" >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
              Right (t, _) -> assertBool (show t) (alphaEq t (App (Ref (h "mine") Nothing) (num 4) :: Term Z))
              Left err -> assertFailure (T.unpack err)
    ]

-- Hashing ---------------------------------------------------------------------

hashTests :: TestTree
hashTests =
  testGroup
    "hash"
    [ testCase "alpha-equivalent terms hash equal" $
        hashTerm (Lam "x" (v0 +. num 1)) @?= hashTerm (Lam "y" (v0 +. num 1))
    , testCase "different terms hash differently" $
        assertBool "collision" (hashTerm (num 5) /= hashTerm (num 2 +. num 3))
    , testCase "rationals in lowest terms share an encoding" $
        encodeTerm (num (2 / 4)) @?= encodeTerm (num (1 / 2))
    , testCase "short hash form" $ do
        let s = showHash (hashTerm (num 1))
        T.length s @?= 6
        T.head s @?= '#'
    , testCase "placeholder hash ignores which cycle variable is used" $
        let a = App v0 (num 1) :: Term (S (S Z))
            b = App v1 (num 1) :: Term (S (S Z))
         in placeholderHash a @?= placeholderHash b
    , testCase "placeholder hash still sees structure" $
        let a = App v0 (num 1) :: Term (S Z)
            b = App v0 (num 2) :: Term (S Z)
         in assertBool "collision" (placeholderHash a /= placeholderHash b)
    ]

-- Pretty ----------------------------------------------------------------------

prettyTests :: TestTree
prettyTests =
  testGroup
    "pretty"
    [ testCase "integers" $ renderRational 20 42 @?= "42"
    , testCase "terminating decimals print in full" $ renderRational 20 (11 / 2) @?= "5.5"
    , testCase "repeating decimals are truncated with an ellipsis" $
        renderRational 5 (1 / 3) @?= "0.33333…"
    , testCase "negative" $ renderRational 20 (-1 / 4) @?= "-0.25"
    , testCase "scale zero" $ renderRational 0 (1 / 3) @?= "0…"
    ]

-- End to end ------------------------------------------------------------------

evalText :: Text -> Either Text [Text]
evalText src = snd <$> feed defaultConfig emptySession src

endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end to end"
    [ testCase "1 + 4.5 is exact" $ evalText "1 + 4.5" @?= Right ["5.5"]
    , testCase "exact thirds" $ evalText "1/3 * 3" @?= Right ["1"]
    , testCase "repeating decimal" $ evalText "2/3" @?= Right ["0.66666666666666666666…"]
    , testCase "lambda" $ evalText "(\\x y -> x * y + 1) 3 4" @?= Right ["13"]
    , testCase "unicode lambda and operators" $ evalText "(λx → x ⊗ 2) 21" @?= Right ["42"]
    , testCase "if with booleans" $ evalText "if 1 < 2 && ¬false then 10 else 20" @?= Right ["10"]
    , testCase "superscript power" $ evalText "2³ + 2⁻¹" @?= Right ["8.5"]
    , testCase "section" $ evalText "(+ 1) 41" @?= Right ["42"]
    , testCase "projection" $ evalText "[1, 2, 3].1 + [[1, 2], [3, 4]].1.0" @?= Right ["5"]
    , testCase "elementwise arithmetic on tensors" $ do
        evalText "[1, 2] + [3, 4]" @?= Right ["[4, 6]"]
        evalText "-[[1, 2], [3, 4]]" @?= Right ["[[-1, -2], [-3, -4]]"]
        evalText "[[1, 2], [3, 4]] == [[1, 2], [3, 4]]" @?= Right ["true"]
    , testCase "tensor primitives" $ do
        evalText "dot [1, 2, 3] [4, 5, 6]" @?= Right ["32"]
        evalP "cross [1, 0, 0] [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalText "transpose [[1, 2], [3, 4]]" @?= Right ["[[1, 3], [2, 4]]"]
        evalText "vmap (\\x -> x * 2) [[1, 2], [3, 4]]" @?= Right ["[[2, 4], [6, 8]]"]
    , testCase "a rank-three tensor" $
        evalText "[[[1, 2], [3, 4]], [[5, 6], [7, 8]]].1.0.1" @?= Right ["6"]
    , testCase "constant literals fold into one node, constructions do not" $
        case (desugarText "[[1, 2], [3, 4]]", desugarText "\\x -> [x, 2]") of
          (Right (Lit (LTensor [2, 2] [1, 2, 3, 4])), Right (Lam _ (Pack [Var FZ, Lit (LTensor [] [2])]))) -> pure ()
          other -> assertFailure (show other)
    , testCase "a name defined twice in one group is an error" $
        case evalText "let x = 5\nlet x = 6" of
          Left err -> T.isInfixOf "defined twice" err @? T.unpack err
          Right _ -> assertFailure "expected an error"
    , testCase "statements in a group may refer to each other in any order" $
        evalText "y\nlet y = x + 1\nlet x = 5" @?= Right ["6"]
    , testCase "where" $ evalText "let f x = x * k where k = 2\nf 21" @?= Right ["42"]
    , testCase "function definitions" $
        evalText "let twice f x = f (f x)\nlet inc = (+ 1)\ntwice inc 5" @?= Right ["7"]
    , testCase "division by zero is a runtime error" $
        evalText "1 / 0" @?= Left "error: division by zero"
    , testCase "an unknown unit is an unknown name" $
        case evalText "3 furlongs" of
          Left err -> T.isInfixOf "unknown name `furlongs`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "recursion" $
        evalText "let fact n = if n == 0 then 1 else n * fact (n - 1)\nfact 10" @?= Right ["3628800"]
    , testCase "mutual recursion in one group" $
        evalText "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)\neven 10\nodd 7"
          @?= Right ["true", "true"]
    , testCase "recursion through a codebase reference across inputs" $
        runLines ["let fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)", "fib 20"] @?= Right ["6765"]
    , testCase "transcendentals are known but unimplemented" $
        evalText "sqrt 2" @?= Left "not implemented: sqrt: not implemented yet"
    , testCase "parse error mentions the position" $
        case evalText "1 +" of
          Left err -> T.isInfixOf "1:4" err @? T.unpack err
          Right _ -> assertFailure "expected an error"
    ]

-- Codebase, scratch and versioning -------------------------------------------------

-- | Feed inputs one at a time, as REPL lines, collecting all output.
runLines :: [Text] -> Either Text [Text]
runLines = go emptySession []
  where
    go _ acc [] = Right (concat (reverse acc))
    go s acc (l : ls) = do
      (s', outs) <- feed defaultConfig s l
      go s' (outs : acc) ls

-- | Run lines and keep only outputs matching a predicate.
outputsWhere :: (Text -> Bool) -> [Text] -> Either Text [Text]
outputsWhere p ls = filter p <$> runLines ls

startsWith :: Text -> Text -> Bool
startsWith = T.isPrefixOf

-- | Fail on an error, otherwise continue with the outputs.
expecting :: Either Text [Text] -> ([Text] -> Assertion) -> Assertion
expecting r k = either (assertFailure . T.unpack) k r

lastN :: Int -> [a] -> [a]
lastN n xs = drop (length xs - n) xs

codebaseTests :: TestTree
codebaseTests =
  testGroup
    "codebase"
    [ testCase "scratch definitions are usable before :add" $
        runLines ["let x = 5", "x + 1"] @?= Right ["6"]
    , testCase "redefining a pending name replaces it with a notice" $
        runLines ["let x = 5", "let x = 6", "x"] @?= Right ["replaced pending definition of `x`", "6"]
    , testCase ":add stores new names and clears the scratch" $
        runLines ["let x = 5", ":add", ":scratch", ":hash x"] @?= Right ["added x", "#" <> T.drop 1 (hashText 5)]
    , testCase ":add refuses a changed existing name" $
        case runLines ["let x = 5", ":add", "let x = 6", ":add"] of
          Left err -> T.isInfixOf "use :update" err @? T.unpack err
          Right _ -> assertFailure "expected a conflict"
    , testCase ":add of an identical definition is fine" $
        runLines ["let x = 5", ":add", "let x = 5", ":add"] @?= Right ["added x", "added x"]
    , testCase ":update rebinds and upgrades dependents (design §7.5)" $
        expecting (runLines ["let x = 5", "let y = x + 1", ":add", "let x = 6", ":update", "y", ":view y"]) $ \outs -> do
          any (startsWith "updated x") outs @? show outs
          any (startsWith "upgraded y") outs @? show outs
          lastN 2 outs @?= ["7", "y = x + 1"]
    , testCase ":update --no-upgrade leaves dependents on the old version" $
        expecting (runLines ["let x = 5", "let y = x + 1", ":add", "let x = 6", ":update --no-upgrade", "y", ":view y", ":todo"]) $ \outs -> do
          any (startsWith "dependents left on old versions: y") outs @? show outs
          case lastN 3 outs of
            [v, view, td] -> do
              v @?= "6"
              startsWith "y = x#" view @? T.unpack view
              startsWith "stale: y uses x#" td @? T.unpack td
            other -> assertFailure (show other)
    , testCase ":upgrade moves stale dependents to the current version" $
        expecting (runLines ["let x = 5", "let y = x + 1", ":add", "let x = 6", ":update --no-upgrade", ":upgrade x", "y", ":view y", ":todo"]) $ \outs -> do
          any (startsWith "upgraded y") outs @? show outs
          lastN 3 outs @?= ["7", "y = x + 1", "nothing to do"]
    , testCase "upgrading propagates transitively and through cycles" $
        case runLines
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
    , testCase ":history lists refs newest first after an update" $
        case runLines ["let x = 5", ":add", "let x = 6", ":update", ":history x"] of
          Right outs -> case lastN 2 outs of
            [cur, old] -> do
              T.isSuffixOf "  (current)" cur @? T.unpack cur
              assertBool "distinct" (T.takeWhile (/= ' ') cur /= old)
            other -> assertFailure (show other)
          Left err -> assertFailure (T.unpack err)
    , testCase "alpha-equivalent definitions share a hash" $
        expecting (outputsWhere (startsWith "#") ["let f x = x + 1", "let g y = y + 1", ":hash f", ":hash g"]) $ \case
          [a, b] -> a @?= b
          other -> assertFailure (show other)
    , testCase ":names finds every label of a hash" $
        case runLines ["let x = 5", "let five = 5", ":add", ":hash x"] of
          Right outs -> runLines ["let x = 5", "let five = 5", ":add", ":names " <> last outs] @?= Right ["added x", "added five", last outs <> " five x"]
          Left err -> assertFailure (T.unpack err)
    , testCase ":dependents lists definitions that mention the current ref" $
        expecting (runLines ["let x = 5", "let y = x + 1", "let z = x * 2", "let w = 7", ":add", ":dependents x"]) $ \outs ->
          drop 4 outs @?= ["y", "z"]
    , testCase ":view shows current references by name and prints with minimal parentheses" $
        runLines ["let f a b = (a + b) * -a", ":view f"] @?= Right ["f = \\a -> \\b -> (a + b) * -a"]
    , testCase ":view of a cycle member names the other members" $
        runLines
          [ "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)"
          , ":view odd"
          ]
          @?= Right ["odd = \\n -> if n == 0 then false else even (n - 1)"]
    , testCase "cycle hash is independent of the order members are entered" $
        let evenDef = "let even n = if n == 0 then true else odd (n - 1)"
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
    , testCase "a self-recursive definition is a one-member cycle" $
        case runLines ["let fact n = if n == 0 then 1 else n * fact (n - 1)", ":hash fact", ":view fact"] of
          Right [hf, view] -> do
            T.isSuffixOf ".0" hf @? T.unpack hf
            view @?= "fact = \\n -> if n == 0 then 1 else n * fact (n - 1)"
          other -> assertFailure (show other)
    , testCase ":edit prints a definition as source" $
        runLines ["let double x = x * 2", ":add", ":edit double"] @?= Right ["added double", "let double = \\x -> x * 2"]
    , testCase ":alias and :unname manage labels only" $
        case runLines ["let x = 5", ":add", ":alias five x", ":unname x", "five", ":history x"] of
          Right outs -> do
            drop 3 outs !! 0 @?= "5"
            length (drop 4 outs) @?= 1
          Left err -> assertFailure (T.unpack err)
    , testCase ":forget drops a pending definition" $
        case runLines ["let x = 5", ":forget x", "x"] of
          Left err -> T.isInfixOf "unknown name" err @? T.unpack err
          Right outs -> assertFailure (show outs)
    , testCase ":todo reports pending and clean states" $ do
        runLines ["let x = 5", ":todo"] @?= Right ["pending: x (use :add or :update)"]
        runLines [":todo"] @?= Right ["nothing to do"]
    , testCase "unknown name in a command" $
        runLines [":view nope"] @?= Left "unknown name `nope`"
    ]
  where
    hashText :: Rational -> Text
    hashText r = showHash (hashTerm (num r))

-- Types -------------------------------------------------------------------------

typeOfText :: Text -> Either Text Text
typeOfText src = runLines [":type " <> src] >>= \case
  [t] -> Right t
  other -> Left (T.pack (show other))

typeTests :: TestTree
typeTests =
  testGroup
    "types"
    [ testCase "literals and arithmetic" $ do
        typeOfText "1 + 2" @?= Right "Num"
        typeOfText "1 < 2" @?= Right "Bool"
    , testCase "identity is polymorphic" $ typeOfText "\\x -> x" @?= Right "a -> a"
    , testCase "higher-order" $ typeOfText "\\f x -> f (f x)" @?= Right "(a -> a) -> a -> a"
    , testCase "let-polymorphism" $
        typeOfText "let id x = x in if id true then id 1 else 2" @?= Right "Num"
    , testCase "vector and matrix literals" $ do
        typeOfText "[1, 2, 3]" @?= Right "Vec 3"
        typeOfText "[[1, 2], [3, 4]]" @?= Right "Mat 2 2"
        typeOfText "[[1, 2], [3, 4]].1" @?= Right "Vec 2"
    , testCase "projection gives a lower bound on the length (design §4.1)" $ do
        typeOfText "\\v -> v.0" @?= Right "Tensor (n + 1 : s) d -> Tensor s d"
        typeOfText "\\v -> v.2 + v.0" @?= Right "Tensor (n + 3 : s) d -> Tensor s d"
        typeOfText "\\v -> v.0 + 1" @?= Right "Vec (n + 1) -> Num"
    , testCase "elementwise operators are shape-polymorphic (core.md)" $ do
        typeOfText "\\a b -> a + b" @?= Right "Tensor s d -> Tensor s d -> Tensor s d"
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
        typeOfText "\\k v -> k * v" @?= Right "Num d -> Tensor s d1 -> Tensor s [d d1]"
        typeOfText "\\a b -> a @ b" @?= Right "Vec n d -> Tensor (n : s) d1 -> Tensor s [d d1]"
    , testCase "contraction requires matching inner lengths" $
        case evalText "[[1, 2], [3, 4]] @ [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "mismatched lengths are a static error" $
        case evalText "[1, 2] + [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "length-polymorphic primitives" $ do
        typeOfText "dot" @?= Right "Vec n d -> Tensor (n : s) d1 -> Tensor s [d d1]"
        typeOfText "transpose" @?= Right "Mat n m d -> Mat m n d"
        typeOfTextP "cross" @?= Right "Vec 3 d -> Vec 3 d1 -> Vec 3 [d d1]"
    , testCase "recursive definitions get types" $
        runLines ["let fact n = if n == 0 then 1 else n * fact (n - 1)", ":type fact"] @?= Right ["Num -> Num"]
    , testCase "mutually recursive definitions get types" $
        runLines
          [ "let even n = if n == 0 then true else odd (n - 1)\nlet odd n = if n == 0 then false else even (n - 1)"
          , ":type even"
          , ":type odd"
          ]
          @?= Right ["Num -> Bool", "Num -> Bool"]
    , testCase "codebase references are instantiated freshly" $
        runLines ["let id x = x", ":add", ":type if id true then id 1 else 2"] @?= Right ["added id", "Num"]
    , testCase "Num plus Bool is a static error with an excerpt" $
        case evalText "1 + true" of
          Left err -> do
            T.isInfixOf "error at 1:5" err @? T.unpack err
            T.isInfixOf "expected Num, got Bool" err @? T.unpack err
            T.isInfixOf "^^^^" err @? T.unpack err
          Right v -> assertFailure ("evaluated to " <> show v)
    , testCase "out-of-range projection is static" $
        case evalText "[1, 2].2" of
          Left err -> T.isInfixOf "position 2 is out of range for a vector of length 2" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "too-short vector against a polymorphic projection is static" $
        case evalText "let first v = v.0\nfirst []" of
          Left err -> T.isInfixOf "too short" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "if condition must be Bool" $
        case evalText "if 1 then 2 else 3" of
          Left err -> T.isInfixOf "condition of `if` must be a Bool" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "applying a non-function" $
        case evalText "true 2" of
          Left err -> T.isInfixOf "is not a function" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a type error in a definition names the definition" $
        case evalText "let bad = 1 + true" of
          Left err -> T.isInfixOf "in `bad`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "well-typed programs never hit the evaluator's type checks" $
        evalText "let twice f x = f (f x)\ntwice (\\n -> n * 2) 5" @?= Right ["20"]
    , testCase ":update leaves a dependent that no longer typechecks on the old version" $
        expecting (runLines ["let f x = x + 1", "let g = f 3", ":add", "let f = 7", ":update", "g", ":view g", ":todo"]) $ \outs -> do
          any (startsWith "left g on") outs @? show outs
          case lastN 3 outs of
            [v, view, td] -> do
              v @?= "4"
              startsWith "g = f#" view @? T.unpack view
              startsWith "stale: g uses f#" td @? T.unpack td
            other -> assertFailure (show other)
    ]

-- Closing the lint promise ---------------------------------------------------------

soundnessTests :: TestTree
soundnessTests =
  testGroup
    "soundness"
    [ testCase "functions cannot be compared" $
        case evalText "(\\x -> x) == (\\x -> x)" of
          Left err -> T.isInfixOf "no equality on" err @? T.unpack err
          Right v -> assertFailure ("compared functions: " <> show v)
    , testCase "booleans compare through the equality instance" $ do
        evalText "true == false" @?= Right ["false"]
        evalText "(1 < 2) == true" @?= Right ["true"]
    , testCase "an unknown equality type defaults to Num" $
        typeOfText "\\a b -> a == b" @?= Right "Num -> Num -> Bool"
    , testCase "equality is shape-polymorphic on tensors" $ do
        evalText "[1, 2] == [1, 2]" @?= Right ["true"]
        evalText "[[1, 2], [3, 4]] /= [[1, 2], [3, 5]]" @?= Right ["true"]
        evalText "3 == 3" @?= Right ["true"]
    , testCase "comparing tensors of different shapes is a static error" $
        case evalText "[1, 2] == [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ" err @? T.unpack err
          Right v -> assertFailure (show v)
    ]

-- Products ------------------------------------------------------------------------

productTests :: TestTree
productTests =
  testGroup
    "products"
    [ testCase "tensor product covers scaling and plain multiplication" $ do
        evalText "2 * 3" @?= Right ["6"]
        evalText "2 * [1, 2]" @?= Right ["[2, 4]"]
        evalText "[1, 2] * 2" @?= Right ["[2, 4]"]
        evalText "[1, 2] ⊗ [3, 4]" @?= Right ["[[3, 4], [6, 8]]"]
    , testCase "contracting product is dot, matrix-vector and matrix-matrix" $ do
        evalText "[1, 2, 3] · [4, 5, 6]" @?= Right ["32"]
        evalText "[[1, 2], [3, 4]] @ [1, 1]" @?= Right ["[3, 7]"]
        evalText "[[1, 2], [3, 4]] @ [[0, 1], [1, 0]]" @?= Right ["[[2, 1], [4, 3]]"]
        evalText "[[[1, 2], [3, 4]], [[5, 6], [7, 8]]] @ [1, 0]" @?= Right ["[[1, 3], [5, 7]]"]
    , testCase "cross product, both spellings" $ do
        evalP "[1, 0, 0] × [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalP "[1, 0, 0] >< [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        evalP "cross [0, 1, 0] [1, 0, 0]" @?= Right ["[0, 0, -1]"]
    , testCase "elementwise product and division" $ do
        evalText "[1, 2] ⊙ [3, 4]" @?= Right ["[3, 8]"]
        evalText "[1, 2] .* [3, 4]" @?= Right ["[3, 8]"]
        evalText "[1, 2] ⊘ [2, 4]" @?= Right ["[0.5, 0.5]"]
        evalText "[1, 2] ./ [2, 4]" @?= Right ["[0.5, 0.5]"]
    , testCase "scalar division" $
        evalText "[2, 4] / 2 + [[1, 2], [3, 4]].0 / 1" @?= Right ["[2, 4]"]
    , testCase "elementwise division by zero fails only for that element" $ do
        evalText "([1, 2] ./ [0, 2]).1" @?= Right ["1"]
        evalText "([1, 2] ./ [0, 2]).0" @?= Left "error: division by zero"
    , testCase "quantity rule is a tensor product" $
        runLines ["let m = 1", "3 m"] @?= Right ["3"]
    , testCase "names work prefix and infix" $ do
        evalText "outer 2 [1, 2]" @?= Right ["[2, 4]"]
        evalText "[1, 2] `dot` [3, 4]" @?= Right ["11"]
        evalText "within 5 1 == (5 ± 1)" @?= Left "not implemented: ±: affine arithmetic is not implemented yet"
    ]

-- Properties ----------------------------------------------------------------------
--
-- Random surface programs are pushed through the whole pipeline. These pin
-- the invariants of core.md §9: whatever inference accepts, lint accepts;
-- printed Core re-parses to an alpha-equivalent term; hashes ignore hints;
-- evaluation of a linted term never reports an internal error.

noSpan :: S.Span
noSpan = S.Span (S.Pos 1 1) (S.Pos 1 1)

mk :: S.Node -> S.Expr
mk = S.Expr noSpan

-- | A random expression over a scope of bound names. Literals are small
-- integers and halves so that printed numbers re-parse exactly.
genExpr :: [Text] -> Int -> Gen S.Expr
genExpr scope size
  | size <= 0 = leaf
  | otherwise =
      frequency
        [ (3, leaf)
        , (3, binary)
        , (2, do
             n <- name
             b <- genExpr (n : scope) (size - 1)
             pure (mk (S.Lam [S.Name noSpan n] b)))
        , (2, mk <$> (S.App <$> sub <*> sub))
        , (2, do
             n <- name
             e <- sub
             b <- genExpr (n : scope) (size - 1)
             pure (mk (S.Let (S.Name noSpan n) [] e b)))
        , (1, mk <$> (S.If <$> sub <*> sub <*> sub))
        , (1, mk . S.Neg <$> sub)
        , (1, do
             k <- choose (2, 3)
             mk . S.Vec <$> vectorOf k sub)
        , (1, do
             k <- choose (2, 3)
             i <- choose (0, k - 1)
             es <- vectorOf k sub
             pure (mk (S.Proj (mk (S.Vec es)) i)))
        , (1, (\e n -> mk (S.Pow e n)) <$> sub <*> choose (0, 3))
        ]
  where
    sub = genExpr scope (size `div` 2)
    name = elements ["x", "y", "z", "f", "g"]
    leaf =
      frequency $
        [ (4, mk . S.Num . fromInteger <$> choose (-3, 9))
        , (1, mk . S.Num <$> elements [1 / 2, 3 / 2, 1 / 4])
        , (1, mk . S.Bool <$> arbitrary)
        ]
          ++ [(3, mk . S.Var <$> elements scope) | not (null scope)]
    binary = do
      op <-
        elements
          [S.Add, S.Sub, S.Outer, S.Dot, S.EMul, S.EDiv, S.Div, S.Eq, S.Ne, S.Lt, S.Le, S.Gt, S.Ge, S.And, S.Or, S.PlusMinus Bound]
      mk <$> (S.BinOp op <$> sub <*> sub)

-- | Every hint replaced by a fixed one: alpha-equivalent to the input.
blankHints :: Term n -> Term n
blankHints = go
  where
    go :: Term m -> Term m
    go = \case
      Var i -> Var i
      Ref hh i -> Ref hh i
      PrimApp p as -> PrimApp p (map go as)
      Lit l -> Lit l
      Lam _ b -> Lam "q" (go b)
      App f a -> App (go f) (go a)
      Let _ e b -> Let "q" (go e) (go b)
      If c t e -> If (go c) (go t) (go e)
      Pow t n -> Pow (go t) n
      Noise k n -> Noise k n
      Uncertain k x e -> Uncertain k (go x) (go e)
      Pack ts -> Pack (map go ts)
      Proj t i -> Proj (go t) i
      Cycle hs bs -> Cycle (vecMap (const "q") hs) (vecMap go bs)

-- | The Core of an expression that desugars and typechecks.
wellTyped :: S.Expr -> Maybe (Term Z)
wellTyped e = case desugarClosed noResolver e of
  Left _ -> Nothing
  Right (t, _) -> case elaborateClosed (const Nothing) t of
    Left _ -> Nothing
    Right _ -> Just t

propertyTests :: TestTree
propertyTests =
  testGroup
    "properties"
    [ testProperty "whatever inference accepts, lint accepts with the same type" $
        forAll (genExpr [] 5) $ \e ->
          case desugarClosed noResolver e of
            Left _ -> discard
            Right (t, _) -> case elaborateClosed (const Nothing) t of
              Left _ -> discard
              Right (schemes, typed) -> lintClosed (const Nothing) typed === Right schemes
    , -- Only well-typed terms: an ill-typed one such as a number applied to
      -- a number has no surface spelling because of the quantity rule, and
      -- `:view` only ever prints stored, checked definitions.
      testProperty "printed Core re-parses to an alpha-equivalent term" $
        forAll (genExpr [] 5) $ \e ->
          case wellTyped e of
            Nothing -> discard
            Just t ->
              let printed = renderTerm (\_ _ -> "#") VNil t
               in counterexample (T.unpack printed) $
                    case parseExpr printed >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
                      Left err -> counterexample (T.unpack err) False
                      Right (t', _) -> counterexample (show t') (alphaEq t t')
    , testProperty "hashes ignore hints" $
        forAll (genExpr [] 5) $ \e ->
          case desugarClosed noResolver e of
            Left _ -> discard
            Right (t, _) -> hashTerm (blankHints t) === hashTerm t
    , testProperty "the hash is stable across printing" $
        forAll (genExpr [] 5) $ \e ->
          case wellTyped e of
            Nothing -> discard
            Just t ->
              case parseExpr (renderTerm (\_ _ -> "#") VNil t) >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
                Left _ -> property False
                Right (t', _) -> hashTerm t' === hashTerm t
    , testProperty "evaluating a linted term never reports an internal error" $
        forAll (genExpr [] 5) $ \e ->
          case desugarClosed noResolver e of
            Left _ -> discard
            Right (t, _) -> case elaborateClosed (const Nothing) t of
              Left _ -> discard
              Right (_, typed) -> case evalClosed defaultConfig (Runtime (const Nothing) (\_ _ -> False)) typed >>= render of
                Left (Internal msg) -> counterexample (T.unpack msg) False
                Left (UnknownRef _) -> property False
                Left (BadCycleIndex _) -> property False
                _ -> property True
    , testProperty "inference is deterministic" $
        forAll (genExpr [] 5) $ \e ->
          case desugarClosed noResolver e of
            Left _ -> discard
            Right (t, _) -> fmap fst (elaborateClosed (const Nothing) t) === fmap fst (elaborateClosed (const Nothing) t)
    ]

-- Units and dimensions --------------------------------------------------------------

unitTests :: TestTree
unitTests =
  testGroup
    "units"
    [ testCase "base units are primitives" $ do
        evalText "3 m" @?= Right ["3 m"]
        typeOfText "3 m" @?= Right "Num [m]"
    , testCase "quantity rule with powers" $ do
        evalText "9.81 m / s^2" @?= Right ["9.81 m s^-2"]
        typeOfText "9.81 m/s^2" @?= Right "Num [m s^-2]"
    , testCase "dimensions multiply and divide" $ do
        evalText "(2 m) * (3 s)" @?= Right ["6 m s"]
        evalText "(6 m) / (2 s)" @?= Right ["3 m s^-1"]
        evalText "(3 m)^2" @?= Right ["9 m^2"]
        evalText "[1, 2] m" @?= Right ["[1, 2] m"]
        evalText "2 kg * 3 m / s^2 == 6 kg * m / s^2" @?= Right ["true"]
    , testCase "adding different dimensions is a static error" $
        case evalText "1 m + 1 s" of
          Left err -> T.isInfixOf "dimensions differ by [m s^-1]" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "transcendentals need dimensionless arguments" $
        case evalText "sin (1 m)" of
          Left err -> T.isInfixOf "expected Num, got Num [m]" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "tensor literals need one dimension" $
        case evalText "[1 m, 2 s]" of
          Left err -> T.isInfixOf "same shape" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "dimension polymorphism" $ do
        typeOfText "\\r -> r^2" @?= Right "Num d -> Num [d^2]"
        typeOfText "\\x -> sqrt x" @?= Right "Num [d^2] -> Num d"
        typeOfText "\\x -> sqrt (x * x)" @?= Right "Num d -> Num d"
        typeOfText "\\a b -> atan2 a b" @?= Right "Num d -> Num d -> Num"
        typeOfText "\\x y -> x < y" @?= Right "Num d -> Num d -> Bool"
    , testCase "Kennedy's Euclid step: non-divisible exponents" $
        typeOfText "\\f -> sqrt (f * f * f)" @?= Right "Num [d^2] -> Num [d^3]"
    , testCase "an uncertainty must share the value's dimension" $
        case evalText "3 m ± 1 s" of
          Left err -> T.isInfixOf "dimension of the value" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "to keeps the value for now" $
        evalText "(3 m) to m" @?= Right ["3 m"]
    , testCase "a definition carries its dimension through the codebase" $
        runLines ["let g = 9.81 m / s^2", "let fall t = g * t^2 / 2", ":add", ":type fall", "fall (3 s)"]
          @?= Right ["added g", "added fall", "Num d -> Num [m d^2 s^-2]", "44.145 m"]
    ]

-- Regressions found by lint ------------------------------------------------------------

lintRegressionTests :: TestTree
lintRegressionTests =
  testGroup
    "lint regressions"
    [ testCase "instantiation renames quantified variables simultaneously" $ do
        typeOfTextP "\\a b -> a >< b" @?= Right "Vec 3 d -> Vec 3 d1 -> Vec 3 [d d1]"
        evalP "[1, 0, 0] m >< ([0, 1, 0] m / s)" @?= Right ["[0, 0, 1] m^2 s^-1"]
        evalText "[1, 2] m ⊙ [3, 4] s" @?= Right ["[3, 8] m s"]
    , testCase "a stored polymorphic definition instantiates at several dimensions" $
        runLines ["let sq x = x * x", ":add", "sq (3 m)", "sq (2 s)", ":type sq"]
          @?= Right ["added sq", "9 m^2", "4 s^2", "Num d -> Num [d^2]"]
    ]

-- Prelude ----------------------------------------------------------------------------

withPrelude :: Session
withPrelude = either (error . T.unpack) id preludeSession

evalP :: Text -> Either Text [Text]
evalP src = snd <$> feed defaultConfig withPrelude src

runLinesP :: [Text] -> Either Text [Text]
runLinesP = go withPrelude []
  where
    go _ acc [] = Right (concat (reverse acc))
    go s acc (l : ls) = do
      (s', outs) <- feed defaultConfig s l
      go s' (outs : acc) ls

typeOfTextP :: Text -> Either Text Text
typeOfTextP src = runLinesP [":type " <> src] >>= \case
  [t] -> Right t
  other -> Left (T.pack (show other))

preludeTests :: TestTree
preludeTests =
  testGroup
    "prelude"
    [ testCase "the prelude loads and defines its names" $
        length preludeNames > 600 @? "prelude is unexpectedly small"
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
        evalP "3 h + 30 min" @?= Right ["3.5 h"]
        evalP "30 min + 3 h" @?= Right ["210 min"]
        evalP "1 L to m^3" @?= Right ["0.001 m^3"]
        evalP "1 AU / c to s" @?= Right ["499.00478383615641191347… s"]
    , testCase "constants are exact where SI defines them so" $
        evalP "c" @?= Right ["299792458 m s^-1"]
    , testCase "cross is the Hodge dual of the wedge" $ do
        runLinesP [":view cross"] @?= Right ["cross = \\a -> \\b -> star (a ∧ b)"]
        evalP "[1, 2, 3] × [4, 5, 6] == star ([1, 2, 3] ∧ [4, 5, 6])" @?= Right ["true"]
        -- Contracting ε's last index first gives b × a, so the arguments swap.
        evalP "(ε @ [0, 1, 0]) @ [1, 0, 0]" @?= Right ["[0, 0, 1]"]
    , testCase "wedge works in any dimension" $ do
        typeOfTextP "\\a b -> a /\\ b" @?= Right "Vec n d -> Vec n d1 -> Mat n n [d d1]"
        evalP "[1, 0] ∧ [0, 1]" @?= Right ["[[0, 1], [-1, 0]]"]
    , testCase "an orbital calculation with units end to end" $
        runLinesP
          [ "let r = [7000, 0, 0] km"
          , "let v = [0, 7.5, 0] km / s"
          , ":type r × v"
          , "(r × v).2"
          ]
          @?= Right ["Vec 3 [m^2 s^-1]", "52500 km^2 s^-1"]
    ]

-- Display units ----------------------------------------------------------------------

displayTests :: TestTree
displayTests =
  testGroup
    "display units"
    [ testCase "a quantity prints in the unit it was written in" $ do
        evalP "5 km / h" @?= Right ["5 km h^-1"]
        evalP "(2 km)^2" @?= Right ["4 km^2"]
        evalP "[1, 2] km" @?= Right ["[1, 2] km"]
    , testCase "a sum keeps the left operand's unit" $ do
        evalP "5 km + 3 m" @?= Right ["5.003 km"]
        evalP "3 m + 5 km" @?= Right ["5003 m"]
    , testCase "to converts for display" $ do
        evalP "5 km / h to m / s" @?= Right ["1.38888888888888888888… m s^-1"]
        evalP "1 AU / c to min" @?= Right ["8.31674639726927353189… min"]
        evalP "90 min to h" @?= Right ["1.5 h"]
    , testCase "a user-declared unit" $
        runLinesP ["unit furlong = 201.168 * m", "1 km to furlong", "8 furlong to km"]
          @?= Right ["4.97096953789867175693… furlong", "1.609344 km"]
    , testCase "let-bound quantities are not units, their components are" $
        runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2"] @?= Right ["39.24 m"]
    , testCase "the display unit must match the dimension or base units are used" $
        evalP "sqrt (4 km^2)" @?= Left "not implemented: sqrt: not implemented yet"
    , testCase "units are codebase metadata: a renamed unit prints under its current name" $
        runLinesP ["unit fathom = 1.8288 * m", ":add", "2 fathom", ":alias fm fathom", ":unname fathom", "2 fm"]
          @?= Right ["added fathom", "2 fathom", "`fm` now also names " <> hashOfFathom, "removed the label `fathom`", "2 fm"]
    ]
  where
    hashOfFathom = either (const "?") (T.concat . drop 1) (runLinesP ["unit fathom = 1.8288 * m", ":add", ":hash fathom"])
