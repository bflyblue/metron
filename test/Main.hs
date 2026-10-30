module Main (main) where

import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Affine hiding (DivideByZero)
import Eval.Codebase (Codebase (..))
import Eval.Core
import Eval.Desugar
import Eval.Dimension (DimAtom (..), dimAtoms, isDimOne)
import Eval.Driver
import Eval.Eval
import Eval.Hash
import Eval.Infer (TypeError (..), elaborateClosed)
import Eval.Lexer hiding (TNum, TProj)
import Eval.Lexer qualified as L
import Eval.Parser
import Eval.Prelude (preludeNames)
import Eval.Pretty
import Eval.Store
import Eval.Syntax qualified as S
import Eval.TCore
import Eval.Type
import Gen (exprDepth, genProgram, instanceOf)
import System.Directory (
  createDirectoryIfMissing,
  getTemporaryDirectory,
  removePathForcibly,
 )
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main =
  defaultMain
    ( testGroup
        "eval"
        [ coreTests
        , evalTests
        , tcoreTests
        , lexerTests
        , parserTests
        , desugarTests
        , hashTests
        , prettyTests
        , endToEndTests
        , codebaseTests
        , typeTests
        , soundnessTests
        , productTests
        , propertyTests
        , unitTests
        , lintRegressionTests
        , preludeTests
        , displayTests
        , affineTests
        , storeTests
        , dataTests
        ]
    )

-- Term-building helpers -------------------------------------------------

num :: Rational -> Term n
num r = Lit (LTensor ([], [r]))

bool :: Bool -> Term n
bool b = Con (if b then "True" else "False") []

-- | An if, as the desugarer writes it: a case on Bool in canonical order.
ifT :: Term n -> Term n -> Term n -> Term n
ifT c t e = Case c [Alt "False" VNil e, Alt "True" VNil t]

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
    (schemes, typed) <-
      first (("type error: " <>) . (.message)) (elaborateClosed (typesIn acc) t)
    _ <- first ("lint: " <>) (lintClosed (typesIn acc) typed)
    go ((k, (schemes, typed)) : acc) rest
  typesIn acc k = fst <$> lookup k acc

{- | Elaborate, lint, evaluate and render a closed term against some
definitions. Type errors, lint failures and evaluation errors all come
back as text.
-}
run :: Defs -> Term Z -> Either Text Text
run defs t = do
  elaborated <- elaborateDefs defs
  let typesOf k = fst <$> lookup k elaborated
      typedOf k = snd <$> lookup k elaborated
  (_, typed) <-
    first (("type error: " <>) . (.message)) (elaborateClosed typesOf t)
  _ <- first ("lint: " <>) (lintClosed typesOf typed)
  v <-
    first
      (T.pack . show)
      ( evalClosed
          defaultConfig
          (Runtime typedOf (\_ _ _ -> Nothing) (\_ _ _ -> Nothing))
          typed
      )
  first (T.pack . show) (render v)

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
    "eval"
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
              [ prim1 "floor" (num (-3 / 2))
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
    first (("type error: " <>) . (.message)) (elaborateClosed (const Nothing) t)
  _ <- first ("lint: " <>) (lintClosed (const Nothing) typed)
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
            "let id : t0 -> t0 = Λt0. \\(x : t0) -> x in if id @Bool true then id @Num 1.0 else 2.0"
    , testCase "length polymorphism is explicit too"
        $ showCore <$> elabText "\\v -> v.0 + 1"
          @?= Right "Λn3. \\(v : Vec (n3 + 1)) -> add v.0 1.0"
    , testCase "shape polymorphism is explicit too"
        $ showCore <$> elabText "\\v -> v.0"
          @?= Right "Λn1. Λs2. Λd3. \\(v : Tensor (n1 + 1 : s2) d3) -> v.0"
    , testCase "primitives record the type they are used at"
        $ showCore <$> elabText "1 == 2" @?= Right "eq 1.0 2.0"
    , testCase "lint accepts everything elaboration produces"
        $ mapM_
          (\src -> either (assertFailure . T.unpack) (const (pure ())) (elabText src))
          [ "\\f x -> f (f x)"
          , "let twice f x = f (f x) in twice (\\n -> n + 1) 0"
          , "[[1, 2], [3, 4]].1.0 + [1, 2, 3].2"
          , "if 1 < 2 then [1] else [2]"
          , "let first v = v.0 in first [1, 2] + first [3]"
          ]
    , testCase "lint rejects a badly annotated term"
        $ lintClosed
          (const Nothing)
          ( TLam
              "x"
              TBool
              (TPrimApp "add" (TFun numT (TFun numT numT)) [TVr FZ, TLit (LTensor ([], [1]))])
          )
          @?= Left "argument of add has type Bool, expected Num"
    , testCase
        "lint rejects a primitive at a type that is not an instance of its scheme"
        $ lintClosed
          (const Nothing)
          ( TPrimApp
              "add"
              (TFun TBool (TFun TBool TBool))
              [TCon "True" TBool [], TCon "False" TBool []]
          )
          @?= Left
            "primitive add used at Bool -> Bool -> Bool, not an instance of Tensor s d -> Tensor s d -> Tensor s d"
    , testCase "lint rejects a mismatched let annotation"
        $ case lintClosed
          (const Nothing)
          (TLet "x" (Forall [] TBool) (TLit (LTensor ([], [1]))) (TVr FZ)) of
          Left err -> T.isPrefixOf "let binder annotated" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a type application without an abstraction"
        $ lintClosed (const Nothing) (TTyApp (TLit (LTensor ([], [1]))) (AType TBool))
          @?= Left "type application to a term with no type abstraction"
    ]

-- Lexer ----------------------------------------------------------------------

toks :: Text -> Either Text [Token]
toks src = map (.value) <$> tokenize src

lexerTests :: TestTree
lexerTests =
  testGroup
    "lexer"
    [ testCase "numbers are exact rationals"
        $ toks "9.81 1e-3 1_000 2E2"
          @?= Right [L.TNum (981 / 100), L.TNum (1 / 1000), L.TNum 1000, L.TNum 200]
    , testCase "keywords and identifiers"
        $ toks "let x' = true in x'"
          @?= Right [TKw KLet, TIdent "x'", TEquals, TKw KTrue, TKw KIn, TIdent "x'"]
    , testCase "unicode operators map to canonical tokens"
        $ toks "λx → x ⊗ 2 ÷ 3 ≤ 4 && ¬false"
          @?= Right
            [ TLambda
            , TIdent "x"
            , TArrow
            , TIdent "x"
            , TOp "*"
            , L.TNum 2
            , TOp "/"
            , L.TNum 3
            , TOp "<="
            , L.TNum 4
            , TOp "&&"
            , TIdent "not"
            , TKw KFalse
            ]
    , testCase "plus-minus spellings"
        $ toks "a ± 1 ±σ 2 +- 3 +-s 4"
          @?= Right
            [ TIdent "a"
            , TPlusMinus Bound
            , L.TNum 1
            , TPlusMinus Stat
            , L.TNum 2
            , TPlusMinus Bound
            , L.TNum 3
            , TPlusMinus Stat
            , L.TNum 4
            ]
    , testCase "glued superscripts"
        $ toks "m² s⁻² x³"
          @?= Right [TIdent "m", TSup 2, TIdent "s", TSup (-2), TIdent "x", TSup 3]
    , testCase "superscript must be glued"
        $ either (const True) (const False) (toks "m ²") @? "expected an error"
    , testCase "projections"
        $ toks "v.0 m.1.2 r.12"
          @?= Right
            [ TIdent "v"
            , L.TProj 0
            , TIdent "m"
            , L.TProj 1
            , L.TProj 2
            , TIdent "r"
            , L.TProj 12
            ]
    , testCase "a dot followed by letters is composition, not a projection"
        $ toks "r.x" @?= Right [TIdent "r", TOp ".", TIdent "x"]
    , testCase "dot with spaces is composition, .xs is not a projection"
        $ toks "f . g" @?= Right [TIdent "f", TOp ".", TIdent "g"]
    , testCase "projection must be glued to an atom"
        $ either (const True) (const False) (toks "v .0") @? "expected an error"
    , testCase "degree and primes are unit identifiers"
        $ toks "45° 30′ 15″ π"
          @?= Right
            [ L.TNum 45
            , TIdent "deg"
            , L.TNum 30
            , TIdent "arcmin"
            , L.TNum 15
            , TIdent "arcsec"
            , TIdent "pi"
            ]
    , testCase "confusables fold: micro sign and ohm sign"
        $ toks "\x00B5m \x2126" @?= Right [TIdent "\x03BCm", TIdent "\x03A9"]
    , testCase "NFC: a decomposed accent becomes one character"
        $ toks "caf\x0065\x0301" @?= Right [TIdent "caf\x00E9"]
    , testCase "comments; a token after a comment on a new line is a continuation"
        $ toks "1 -- one\n{- block {- nested -} -} 2" @?= Right [L.TNum 1, L.TNum 2]
    , testCase "a comment line between statements"
        $ toks "1\n-- note\n2" @?= Right [L.TNum 1, TSep, L.TNum 2]
    , testCase "layout: column-zero newlines separate statements"
        $ toks "let x = 1\nx\n  + 1\n;y"
          @?= Right
            [ TKw KLet
            , TIdent "x"
            , TEquals
            , L.TNum 1
            , TSep
            , TIdent "x"
            , TOp "+"
            , L.TNum 1
            , TSep
            , TIdent "y"
            ]
    , testCase "layout: where block"
        $ toks "let f x = k where\n  k = 2\n  j = 3\nf 1"
          @?= Right
            [ TKw KLet
            , TIdent "f"
            , TIdent "x"
            , TEquals
            , TIdent "k"
            , TKw KWhere
            , TIdent "k"
            , TEquals
            , L.TNum 2
            , TSep
            , TIdent "j"
            , TEquals
            , L.TNum 3
            , TBlockEnd
            , TSep
            , TIdent "f"
            , L.TNum 1
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
  | Lb Text Tree
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
  S.Labelled l a -> Lb l (shape a)
  S.Tuple es -> Vc (map shape es)
  S.List es -> Vc (map shape es)
  S.CaseOf s _ -> shape s
  S.Proj a i -> Pj (shape a) i

parserTests :: TestTree
parserTests =
  testGroup
    "parser"
    [ testCase "precedence: * over +"
        $ parseShape "1 + 2 * 3" @?= Right (O S.Add (N 1) (O S.Outer (N 2) (N 3)))
    , testCase "left associativity of -"
        $ parseShape "10 - 3 - 2" @?= Right (O S.Sub (O S.Sub (N 10) (N 3)) (N 2))
    , testCase "application binds tighter than operators"
        $ parseShape "f x + g y"
          @?= Right (O S.Add (A (V "f") (V "x")) (A (V "g") (V "y")))
    , testCase
        "power binds tighter than unary minus and application looser than power"
        $ parseShape "-f x ^ 2" @?= Right (Ng (P (A (V "f") (V "x")) 2))
    , testCase "negative literal exponent and superscript"
        $ parseShape "x ^ -2 + y²" @?= Right (O S.Add (P (V "x") (-2)) (P (V "y") 2))
    , testCase "quantity rule: 9.81 m/s^2"
        $ parseShape "9.81 m/s^2"
          @?= Right (O S.Div (O S.Scale (N (981 / 100)) (V "m")) (P (V "s") 2))
    , testCase "quantity rule: 3 m^2 kg and superscripts"
        $ parseShape "3 m² kg"
          @?= Right (O S.Scale (O S.Scale (N 3) (P (V "m") 2)) (V "kg"))
    , testCase "quantity rule: 5 km/h"
        $ parseShape "5 km/h" @?= Right (O S.Div (O S.Scale (N 5) (V "km")) (V "h"))
    , testCase "quantity rule: 3 f x is a product, 3 (f x) too" $ do
        parseShape "3 f x" @?= Right (O S.Scale (O S.Scale (N 3) (V "f")) (V "x"))
        parseShape "3 (f x)" @?= Right (O S.Scale (N 3) (A (V "f") (V "x")))
    , testCase "a literal next to a literal is an error, not a product" $ do
        case parseShape "5 4 3" of
          Left err ->
            T.isInfixOf "write the multiplication" err && T.isInfixOf "1:3" err
              @? T.unpack err
          Right t -> assertFailure (show t)
        case parseShape "2 [1, 2]" of
          Left err -> T.isInfixOf "write the multiplication" err @? T.unpack err
          Right t -> assertFailure (show t)
        parseShape "2 pi" @?= Right (O S.Scale (N 2) (V "pi"))
        parseShape "3 (m/s)" @?= Right (O S.Scale (N 3) (O S.Div (V "m") (V "s")))
    , testCase "rows with ; and planes with ;;" $ do
        parseShape "[1, 2; 3, 4]" @?= Right (Vc [Vc [N 1, N 2], Vc [N 3, N 4]])
        parseShape "[1; 2]" @?= Right (Vc [Vc [N 1], Vc [N 2]])
        parseShape "[1, 2; 3, 4;; 5, 6; 7, 8]"
          @?= Right
            (Vc [Vc [Vc [N 1, N 2], Vc [N 3, N 4]], Vc [Vc [N 5, N 6], Vc [N 7, N 8]]])
        parseShape "[1, 2;; 3, 4]"
          @?= Right (Vc [Vc [Vc [N 1, N 2]], Vc [Vc [N 3, N 4]]])
        parseShape "[f x; g y]"
          @?= Right (Vc [Vc [A (V "f") (V "x")], Vc [A (V "g") (V "y")]])
    , testCase "vector literal with units"
        $ parseShape "[1, 0, 0] km" @?= Right (O S.Scale (Vc [N 1, N 0, N 0]) (V "km"))
    , testCase "degree sign"
        $ parseShape "45°" @?= Right (O S.Scale (N 45) (V "deg"))
    , testCase "lambda with several parameters extends right"
        $ parseShape "\\x y -> x + y" @?= Right (L ["x", "y"] (O S.Add (V "x") (V "y")))
    , testCase "let in"
        $ parseShape "let f x = x * 2 in f 3"
          @?= Right (Lt "f" ["x"] (O S.Outer (V "x") (N 2)) (A (V "f") (N 3)))
    , testCase "if then else"
        $ parseShape "if a < b then a else b"
          @?= Right (I (O S.Lt (V "a") (V "b")) (V "a") (V "b"))
    , testCase "comparison is non-associative"
        $ either (const True) (const False) (parseShape "1 < 2 < 3")
          @? "expected an error"
    , testCase "sections" $ do
        parseShape "(+ 1)" @?= Right (SL S.Add (N 1))
        parseShape "(2 *)" @?= Right (SR (N 2) S.Outer)
        parseShape "(- 1)" @?= Right (Ng (N 1))
    , testCase "backtick infix and composition" $ do
        parseShape "a `dot` b" @?= Right (O (S.Infix "dot") (V "a") (V "b"))
        parseShape "f . g" @?= Right (O S.Compose (V "f") (V "g"))
    , testCase "projections"
        $ parseShape "m.1.2 + v.0"
          @?= Right (O S.Add (Pj (Pj (V "m") 1) 2) (Pj (V "v") 0))
    , testCase "matrix literal"
        $ parseShape "[[1, 0], [0, 1]]" @?= Right (Vc [Vc [N 1, N 0], Vc [N 0, N 1]])
    , testCase "a ragged literal parses; the type checker rejects it" $ do
        either (const False) (const True) (parseShape "[[1, 0], [1]]")
          @? "expected a parse"
        case evalText "[[1, 0], [1]]" of
          Left err -> T.isInfixOf "same shape" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "sqrt prefix and ± operators"
        $ parseShape "√x ± 1"
          @?= Right (O (S.PlusMinus Bound) (A (V "sqrt") (V "x")) (N 1))
    , testCase "to has the lowest precedence"
        $ parseShape "5 km / h to m / s"
          @?= Right
            (O S.To (O S.Div (O S.Scale (N 5) (V "km")) (V "h")) (O S.Div (V "m") (V "s")))
    , testCase "statements with where"
        $ case parseProgram "let f x = x * k where k = 2\nf 3" of
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

{- | Core has no 'Eq' (hints are not part of its meaning), so compare up to
alpha-equivalence.
-}
desugarsTo :: Text -> Term Z -> Assertion
desugarsTo src expected = case desugarText src of
  Left err -> assertFailure (T.unpack err)
  Right t ->
    assertBool
      ("expected " <> show expected <> "\n but got  " <> show t)
      (alphaEq t expected)

desugarFails :: Text -> Text -> Assertion
desugarFails src expected = case desugarText src of
  Left err -> err @?= expected
  Right t -> assertFailure ("expected an error, got " <> show t)

desugarTests :: TestTree
desugarTests =
  testGroup
    "desugar"
    [ testCase "operators become saturated primitives"
        $ desugarsTo "1 + 2 * 3" (num 1 +. num 2 *. num 3)
    , testCase "bound variables become indices"
        $ desugarsTo "\\x y -> x - y" (Lam "x" (Lam "y" (v1 -. v0)))
    , testCase "shadowing picks the innermost binder"
        $ desugarsTo "\\x -> \\x -> x" (Lam "x" (Lam "x" v0))
    , testCase "let with parameters becomes a lambda"
        $ desugarsTo "let f x = x in f" (Let "f" (Lam "x" v0) v0)
    , testCase "partial primitive is eta-expanded"
        $ desugarsTo "(+ 1)" (Lam "x" (v0 +. num 1))
    , testCase "bare primitive is eta-expanded to its arity"
        $ desugarsTo "sqrt" (Lam "x" (PrimApp "sqrt" [v0]))
    , testCase "over-applied primitive is applied further"
        $ desugarsTo "not true 1" (App (PrimApp "not" [bool True]) (num 1))
    , testCase "zero-arity primitive"
        $ desugarsTo "pi" (PrimApp "pi" [])
    , testCase "unknown name"
        $ desugarFails "x + 1" "1:1: unknown name `x`"
    , testCase "composition"
        $ desugarsTo "\\f g -> f . g" (Lam "f" (Lam "g" (Lam "x" (App v2 (App v1 v0)))))
    , testCase "provenance records the root span"
        $ case parseExpr "1 + 2"
          >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
          Right (_, prov) -> Map.lookup [] prov @?= Just (S.Span (S.Pos 1 1) (S.Pos 1 6))
          Left err -> assertFailure (T.unpack err)
    , testCase "provenance records children by path"
        $ case parseExpr "1 + 20"
          >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
          Right (_, prov) -> Map.lookup [1] prov @?= Just (S.Span (S.Pos 1 5) (S.Pos 1 7))
          Left err -> assertFailure (T.unpack err)
    , testCase "a resolver turns free names into references"
        $ let resolver n =
                if n == "k" then Just (Resolution (h "kay", Nothing) False False) else Nothing
           in case parseExpr "k + 1"
                >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
                Right (t, _) ->
                  assertBool (show t) (alphaEq t (Ref (h "kay") Nothing "" +. num 1 :: Term Z))
                Left err -> assertFailure (T.unpack err)
    , testCase "codebase names shadow primitives"
        $ let resolver n =
                if n == "sqrt"
                  then Just (Resolution (h "mine", Nothing) False False)
                  else Nothing
           in case parseExpr "sqrt 4"
                >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
                Right (t, _) ->
                  assertBool
                    (show t)
                    (alphaEq t (App (Ref (h "mine") Nothing "") (num 4) :: Term Z))
                Left err -> assertFailure (T.unpack err)
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

-- Pretty ----------------------------------------------------------------------

prettyTests :: TestTree
prettyTests =
  testGroup
    "pretty"
    [ testCase "integers" $ renderRational 20 42 @?= "42"
    , testCase "terminating decimals print in full"
        $ renderRational 20 (11 / 2) @?= "5.5"
    , testCase "repeating decimals are truncated with an ellipsis"
        $ renderRational 5 (1 / 3) @?= "0.33333…"
    , testCase "negative" $ renderRational 20 (-1 / 4) @?= "-0.25"
    , testCase "scale zero" $ renderRational 0 (1 / 3) @?= "0…"
    ]

-- End to end ------------------------------------------------------------------

evalText :: Text -> Either Text [Text]
evalText src = snd <$> feed emptySession src

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
    ]

-- Codebase, scratch and versioning -------------------------------------------------

-- | Feed inputs one at a time, as REPL lines, collecting all output.
runLines :: [Text] -> Either Text [Text]
runLines = go emptySession []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
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
    [ testCase "scratch definitions are usable before :add"
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
            drop 3 outs !! 0 @?= "5"
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

-- Types -------------------------------------------------------------------------

typeOfText :: Text -> Either Text Text
typeOfText src =
  runLines [":type " <> src] >>= \case
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
    , testCase "higher-order"
        $ typeOfText "\\f x -> f (f x)" @?= Right "(a -> a) -> a -> a"
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
        typeOfText "\\a b -> a @ b"
          @?= Right "Vec n d -> Tensor (n : s) d1 -> Tensor s [d d1]"
    , testCase "contraction requires matching inner lengths"
        $ case evalText "[[1, 2], [3, 4]] @ [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "mismatched lengths are a static error"
        $ case evalText "[1, 2] + [1, 2, 3]" of
          Left err -> T.isInfixOf "lengths differ: 2 and 3" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "length-polymorphic primitives" $ do
        typeOfText "dot" @?= Right "Vec n d -> Tensor (n : s) d1 -> Tensor s [d d1]"
        typeOfText "transpose" @?= Right "Mat n m d -> Mat m n d"
        typeOfTextP "cross" @?= Right "Vec 3 d -> Vec 3 d1 -> Vec 3 [d d1]"
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
    , testCase "quantity rule multiplies a literal by a declared unit"
        $ runLines ["unit dozen = 12", "3 dozen", "3 dozen to 1"]
          @?= Right ["3 dozen", "36"]
    , testCase "juxtaposition is for units only" $ do
        evalP "5 g" @?= Right ["5 g"]
        evalP "3 (m/s)" @?= Right ["3 m s^-1"]
        evalP "90 deg to rad" @?= Right ["1.5707963267948966192… rad"]
        case runLinesP ["let a = [1, 2; 3, 4]", "5 a"] of
          Left err -> T.isInfixOf "`a` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "2 pi" of
          Left err -> T.isInfixOf "`pi` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "\\m -> 5 m" of
          Left err -> T.isInfixOf "`m` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "let f x = x in 3 f" of
          Left err -> T.isInfixOf "`f` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "3 (f x)" of
          Left err -> T.isInfixOf "not a unit expression" err @? T.unpack err
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

{- | A random expression over a scope of bound names. Literals are small
integers and halves so that printed numbers re-parse exactly.
-}
genExpr :: [Text] -> Int -> Gen S.Expr
genExpr scope size
  | size <= 0 = leaf
  | otherwise =
      frequency
        [ (3, leaf)
        , (3, binary)
        ,
          ( 2
          , do
              n <- name
              b <- genExpr (n : scope) (size - 1)
              pure (mk (S.Lam [S.Name noSpan n] b))
          )
        , (2, mk <$> (S.App <$> sub <*> sub))
        ,
          ( 2
          , do
              n <- name
              e <- sub
              b <- genExpr (n : scope) (size - 1)
              pure (mk (S.Let (S.Name noSpan n) [] e b))
          )
        , (1, mk <$> (S.If <$> sub <*> sub <*> sub))
        , (1, mk . S.Neg <$> sub)
        ,
          ( 1
          , do
              k <- choose (2, 3)
              mk . S.Vec <$> vectorOf k sub
          )
        ,
          ( 1
          , do
              k <- choose (2, 3)
              i <- choose (0, k - 1)
              es <- vectorOf k sub
              pure (mk (S.Proj (mk (S.Vec es)) i))
          )
        , (1, (\e n -> mk (S.Pow e n)) <$> sub <*> choose (0, 3))
        ]
 where
  sub = genExpr scope (size `div` 2)
  name = elements ["x", "y", "z", "f", "g"]
  leaf =
    frequency
      $ [ (4, mk . S.Num . fromInteger <$> choose (-3, 9))
        , (1, mk . S.Num <$> elements [1 / 2, 3 / 2, 1 / 4])
        , (1, mk . S.Bool <$> arbitrary)
        ]
        ++ [(3, mk . S.Var <$> elements scope) | not (null scope)]
  binary = do
    op <-
      elements
        [ S.Add
        , S.Sub
        , S.Outer
        , S.Dot
        , S.EMul
        , S.EDiv
        , S.Div
        , S.Eq
        , S.Ne
        , S.Lt
        , S.Le
        , S.Gt
        , S.Ge
        , S.And
        , S.Or
        , S.PlusMinus Bound
        ]
    mk <$> (S.BinOp op <$> sub <*> sub)

-- | Every hint replaced by a fixed one: alpha-equivalent to the input.
blankHints :: Term n -> Term n
blankHints = go
 where
  go :: Term m -> Term m
  go = \case
    Var i -> Var i
    Ref hh i hint -> Ref hh i hint
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam _ b -> Lam "q" (go b)
    App f a -> App (go f) (go a)
    Let _ e b -> Let "q" (go e) (go b)
    Con c as -> Con c (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt c hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k l n
    Uncertain k l x e -> Uncertain k l (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle (vecMap (const "q") hs) (vecMap go bs)

{- | Where property-test programs come from, and what to do with one that
does not typecheck: the blind generator's are discarded, the typed
generator's are failures.
-}
data Source = Source
  { programs :: Gen S.Expr
  , rejected :: String -> Property
  }

blindSource :: Source
blindSource = Source (genExpr [] 5) (const discard)

typedSource :: Source
typedSource = Source (snd <$> genProgram) (`counterexample` False)

-- | A program as printed Core, for counterexamples.
showProgram :: S.Expr -> String
showProgram e = case desugarClosed noResolver e of
  Left err -> T.unpack (renderDesugarError err) <> "\n" <> show e
  Right (t, _) -> T.unpack (renderTerm (\_ _ _ -> "#") VNil t)

-- | Desugar and elaborate, handing failures to the source.
withElaborated ::
  Source -> S.Expr -> (Term Z -> ([Scheme], TTerm Z) -> Property) -> Property
withElaborated src e k = case desugarClosed noResolver e of
  Left err -> src.rejected (T.unpack (renderDesugarError err))
  Right (t, _) -> case elaborateClosed (const Nothing) t of
    Left err -> src.rejected ("type error: " <> T.unpack err.message)
    Right r -> k t r

forProgram :: Source -> (S.Expr -> Property) -> Property
forProgram src = forAllShow src.programs showProgram

-- | The invariants of core.md §9 over programs from one source.
pipelineProperties :: Source -> [TestTree]
pipelineProperties src =
  [ testProperty "whatever inference accepts, lint accepts with the same type"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \_ (schemes, typed) -> lintClosed (const Nothing) typed === Right schemes
  , -- Only well-typed terms: an ill-typed one such as a number applied to
    -- a number has no surface spelling because of the quantity rule, and
    -- `:view` only ever prints stored, checked definitions.
    testProperty "printed Core re-parses to an alpha-equivalent term"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          let printed = renderTerm (\_ _ _ -> "#") VNil t
           in counterexample (T.unpack printed)
                $ case parseExpr printed
                  >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
                  Left err -> counterexample (T.unpack err) False
                  Right (t', _) -> counterexample (fromMaybe "" (firstDifference t t')) (alphaEq t t')
  , testProperty "hashes ignore hints"
      $ forProgram src
      $ \e ->
        case desugarClosed noResolver e of
          Left err -> src.rejected (T.unpack (renderDesugarError err))
          Right (t, _) -> hashTerm (blankHints t) === hashTerm t
  , testProperty "the hash is stable across printing"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          case parseExpr (renderTerm (\_ _ _ -> "#") VNil t)
            >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
            Left err -> counterexample (T.unpack err) False
            Right (t', _) ->
              counterexample
                (fromMaybe "" (firstDifference t t'))
                (hashTerm t' === hashTerm t)
  , testProperty "evaluating a linted term never reports an internal error"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \_ (_, typed) ->
          case evalClosed
            defaultConfig
            (Runtime (const Nothing) (\_ _ _ -> Nothing) (\_ _ _ -> Nothing))
            typed
            >>= render of
            Left (Internal msg) -> counterexample (T.unpack msg) False
            Left (UnknownRef _) -> property False
            Left (BadCycleIndex _) -> property False
            Left err -> label (evalOutcome err) True
            Right _ -> label "value" True
  , testProperty "inference is deterministic"
      $ forProgram src
      $ \e ->
        case desugarClosed noResolver e of
          Left err -> src.rejected (T.unpack (renderDesugarError err))
          Right (t, _) ->
            fmap fst (elaborateClosed (const Nothing) t)
              === fmap fst (elaborateClosed (const Nothing) t)
  ]
 where
  evalOutcome = \case
    DivideByZero -> "division by zero"
    Unsupported _ -> "not implemented"
    _ -> "other error"

propertyTests :: TestTree
propertyTests =
  testGroup
    "properties"
    [ testGroup "blind programs" (pipelineProperties blindSource)
    , testGroup
        "typed programs"
        ( testProperty
            "the generator's programs have the type they were built for"
            generatorProperty
            : pipelineProperties typedSource
        )
    ]

{- | The typed generator checks itself: inference succeeds on every program
and the type it was built for is an instance of the inferred scheme.
Coverage is tabulated from the elaborated term, so it reports what
inference saw, not what the generator meant.
-}
generatorProperty :: Property
generatorProperty =
  forAllShow
    genProgram
    (\(ty, e) -> T.unpack (renderType ty) <> "\n" <> showProgram e)
    $ \(ty, e) ->
      withElaborated typedSource e $ \_ (schemes, typed) ->
        case schemes of
          [sc] ->
            tabulate "target" [targetKind ty]
              . tabulate "depth" [bucket (exprDepth e)]
              . foldr (\(name, present) k -> classify present name . k) id (features typed)
              $ counterexample
                ( "built for "
                    <> T.unpack (renderType ty)
                    <> ", inferred "
                    <> T.unpack (renderScheme sc)
                )
                (instanceOf sc ty)
          _ -> counterexample "more than one scheme" False
 where
  bucket d
    | d < 5 = "1-4"
    | d < 10 = "5-9"
    | d < 15 = "10-14"
    | d < 20 = "15-19"
    | otherwise = "20+"
  targetKind = \case
    TBool -> "Bool"
    TFun _ _ -> "function"
    TPoint _ _ -> "Point"
    TScale _ _ -> "Scale"
    TTuple _ -> "tuple"
    TList _ -> "list"
    TTensor sh d ->
      ( case rankOf sh of
          0 -> "Num"
          1 -> "Vec"
          2 -> "Mat"
          _ -> "rank 3"
      )
        <> (if isDimOne d then "" else " with a dimension")
    TVar _ -> "variable"

rankOf :: Shape -> Int
rankOf = \case
  SNil -> 0
  SCons _ rest -> 1 + rankOf rest
  SVar _ -> 0

{- | What an elaborated program exercises: polymorphic lets, dimensioned
tensors, higher ranks, higher-order functions.
-}
features :: TTerm Z -> [(String, Bool)]
features typed =
  [ ("polymorphic let", polyLets typed > 0)
  , ("dimensioned tensor of rank >= 1", any dimensionedTensor tys)
  , ("dimensioned value", any dimensioned tys)
  , ("rank >= 2", any ((>= 2) . tensorRank) tys)
  , ("higher-order function", any higherOrder tys)
  ]
 where
  tys = annotations typed
  dimensioned = \case
    TTensor _ d -> any isBase (dimAtoms d)
    TFun a b -> dimensioned a || dimensioned b
    _ -> False
  dimensionedTensor = \case
    TTensor (SCons _ _) d -> any isBase (dimAtoms d)
    TFun a b -> dimensionedTensor a || dimensionedTensor b
    _ -> False
  isBase = \case
    (Base _, _) -> True
    _ -> False
  tensorRank = \case
    TTensor sh _ -> rankOf sh
    TFun a b -> max (tensorRank a) (tensorRank b)
    _ -> 0
  higherOrder = \case
    TFun (TFun _ _) _ -> True
    TFun _ b -> higherOrder b
    _ -> False

-- | Let binders generalised over at least one variable.
polyLets :: TTerm n -> Int
polyLets = \case
  TLet _ (Forall vs _) e b -> (if null vs then 0 else 1) + polyLets e + polyLets b
  TLam _ _ b -> polyLets b
  TApp f a -> polyLets f + polyLets a
  TCon _ _ as -> sum (map polyLets as)
  TCase s _ alts -> polyLets s + sum [polyLets b | TAlt _ _ b <- alts]
  TPrimApp _ _ as -> sum (map polyLets as)
  TPow b _ -> polyLets b
  TUncertain _ _ x e -> polyLets x + polyLets e
  TPack ts -> sum (map polyLets ts)
  TProj t _ -> polyLets t
  TTyLam _ _ b -> polyLets b
  TTyApp b _ -> polyLets b
  _ -> 0

-- | Every type annotation in an elaborated term.
annotations :: TTerm n -> [Type]
annotations = \case
  TPrimApp _ ty as -> ty : concatMap annotations as
  TLam _ ty b -> ty : annotations b
  TApp f a -> annotations f ++ annotations a
  TLet _ (Forall _ ty) e b -> ty : annotations e ++ annotations b
  TCon _ ty as -> ty : concatMap annotations as
  TCase s ty alts ->
    ty
      : annotations s
      ++ concat [map snd (vecToList bs) ++ annotations b | TAlt _ bs b <- alts]
  TPow b _ -> annotations b
  TUncertain _ _ x e -> annotations x ++ annotations e
  TPack ts -> concatMap annotations ts
  TProj t _ -> annotations t
  TTyLam _ _ b -> annotations b
  TTyApp b arg -> (case arg of AType t -> [t]; _ -> []) ++ annotations b
  _ -> []

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
    , testCase "adding different dimensions is a static error"
        $ case evalText "1 m + 1 s" of
          Left err -> T.isInfixOf "dimensions differ by [m s^-1]" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "the circular functions take an angle"
        $ case evalText "sin (1 m)" of
          Left err ->
            T.isInfixOf "sin takes an angle" err && T.isInfixOf "got Num [m]" err
              @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "tensor literals need one dimension"
        $ case evalText "[1 m, 2 s]" of
          Left err -> T.isInfixOf "same shape" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "dimension polymorphism" $ do
        typeOfText "\\r -> r^2" @?= Right "Num d -> Num [d^2]"
        typeOfText "\\x -> sqrt x" @?= Right "Num [d^2] -> Num d"
        typeOfText "\\x -> sqrt (x * x)" @?= Right "Num d -> Num d"
        typeOfText "\\a b -> atan2 a b" @?= Right "Num d -> Num d -> Num [rad]"
        typeOfText "\\x y -> x < y" @?= Right "Num d -> Num d -> Bool"
    , testCase "Kennedy's Euclid step: non-divisible exponents"
        $ typeOfText "\\f -> sqrt (f * f * f)" @?= Right "Num [d^2] -> Num [d^3]"
    , -- `d^2 = m` has no solution; the Euclid step used to substitute
      -- `d := d'` forever. Found while checking how the type-directed
      -- generator's negative powers print.
      localOption (mkTimeout 5000000)
        $ testCase "a dimension equation with no integer solution is an error, not a loop"
        $ do
          case evalText "sqrt (1 m)" of
            Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalText "let f x = x^2 + 1 m" of
            Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalText "\\x -> x ^ -2 * [1, 2] to s" of
            Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "an uncertainty must share the value's dimension"
        $ case evalText "3 m ± 1 s" of
          Left err -> T.isInfixOf "dimension of the value" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "to keeps the value for now"
        $ evalText "(3 m) to m" @?= Right ["3 m"]
    , testCase "a definition carries its dimension through the codebase"
        $ runLines
          [ "let g = 9.81 m / s^2"
          , "let fall t = g * t^2 / 2"
          , ":add"
          , ":type fall"
          , "fall (3 s)"
          ]
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
    , testCase "a stored polymorphic definition instantiates at several dimensions"
        $ runLines ["let sq x = x * x", ":add", "sq (3 m)", "sq (2 s)", ":type sq"]
          @?= Right ["added sq", "9 m^2", "4 s^2", "Num d -> Num [d^2]"]
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
            @?= Right "Num d -> Vec 2 d"
          case evalText "((\\k -> let g = \\v -> k * v in g [1, 2]) 3) + [1, 2, 3]" of
            Left err -> T.isInfixOf "lengths differ" err @? T.unpack err
            Right v -> assertFailure (show v)
          evalText "(\\k -> let g = \\v -> k * v in g [1, 2]) 3" @?= Right ["[3, 6]"]
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
            @?= Right "Num d -> Num d"
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
            case elaborateClosed (const Nothing) cycle' of
              Left err -> assertFailure (T.unpack err.message)
              Right (schemes, typed) -> do
                let closed (Forall vs t) = all ((`elem` map fst vs) . fst) (freeVars t)
                all closed schemes @? show schemes
                map renderScheme <$> lintClosed (const Nothing) typed
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

-- Prelude ----------------------------------------------------------------------------

withPrelude :: Session
withPrelude = either (error . T.unpack) id preludeSession

evalP :: Text -> Either Text [Text]
evalP src = snd <$> feed withPrelude src

runLinesP :: [Text] -> Either Text [Text]
runLinesP = go withPrelude []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

typeOfTextP :: Text -> Either Text Text
typeOfTextP src =
  runLinesP [":type " <> src] >>= \case
    [t] -> Right t
    other -> Left (T.pack (show other))

preludeTests :: TestTree
preludeTests =
  testGroup
    "prelude"
    [ testCase "the prelude loads and defines its names"
        $ length preludeNames > 600 @? "prelude is unexpectedly small"
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
        evalP "1 AU / c to s" @?= Right ["499.00478383615641191… s"]
    , testCase "constants are exact where SI defines them so"
        $ evalP "c" @?= Right ["299792458 m s^-1"]
    , testCase "cross is the Hodge dual of the wedge" $ do
        runLinesP [":view cross"] @?= Right ["cross = \\a -> \\b -> star (a ∧ b)"]
        evalP "[1, 2, 3] × [4, 5, 6] == star ([1, 2, 3] ∧ [4, 5, 6])" @?= Right ["true"]
        -- Contracting ε's last index first gives b × a, so the arguments swap.
        evalP "(ε @ [0, 1, 0]) @ [1, 0, 0]" @?= Right ["[0, 0, 1]"]
    , testCase "wedge works in any dimension" $ do
        typeOfTextP "\\a b -> a /\\ b" @?= Right "Vec n d -> Vec n d1 -> Mat n n [d d1]"
        evalP "[1, 0] ∧ [0, 1]" @?= Right ["[0, 1; -1, 0]"]
    , testCase "an orbital calculation with units end to end"
        $ runLinesP
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
    , testCase "a sum takes the smaller unit, whichever side it is on" $ do
        evalP "5 km + 3 m" @?= Right ["5003 m"]
        evalP "3 m + 5 km" @?= Right ["5003 m"]
        evalP "3 h + 30 min" @?= Right ["210 min"]
        evalP "3 h + 30 min to h" @?= Right ["3.5 h"]
    , testCase "to converts for display" $ do
        evalP "5 km / h to m / s" @?= Right ["1.3888888888888888888… m s^-1"]
        evalP "1 AU / c to min" @?= Right ["8.3167463972692735318… min"]
        evalP "90 min to h" @?= Right ["1.5 h"]
    , testCase "a user-declared unit"
        $ runLinesP ["unit furlong = 201.168 * m", "1 km to furlong", "8 furlong to km"]
          @?= Right ["4.9709695378986717569… furlong", "1.609344 km"]
    , testCase "let-bound quantities are not units, their components are"
        $ runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2"] @?= Right ["39.24 m"]
    , testCase "the display unit must match the dimension or base units are used"
        $ evalP "sqrt (4 km^2)" @?= Right ["2000 m"]
    , testCase
        "units are codebase metadata: a renamed unit prints under its current name"
        $ runLinesP
          [ "unit fathom = 1.8288 * m"
          , ":add"
          , "2 fathom"
          , ":alias fm fathom"
          , ":unname fathom"
          , "2 fm"
          ]
          @?= Right
            [ "added fathom"
            , "2 fathom"
            , "`fm` now also names " <> hashOfFathom
            , "removed the label `fathom`"
            , "2 fm"
            ]
    ]
 where
  hashOfFathom =
    either
      (const "?")
      (T.concat . drop 1)
      (runLinesP ["unit fathom = 1.8288 * m", ":add", ":hash fathom"])

-- Affine arithmetic -----------------------------------------------------------------
--
-- Design §3.2: exact values stay exact, approximations carry rigorous
-- enclosures, declared uncertainty keeps its identity, and printing never
-- shows a digit that is not certain.

affineTests :: TestTree
affineTests =
  testGroup
    "affine"
    [ testCase "exact values print in full or with an ellipsis" $ do
        evalText "1/3" @?= Right ["0.33333333333333333333…"]
        evalText "sqrt 16" @?= Right ["4"]
        evalText "6.62607015e-34" @?= Right ["6.62607015e-34"]
    , testCase "certain digits of approximations end in an ellipsis, zeros included" $ do
        evalText "sin (1 rad)" @?= Right ["0.84147098480789650665…"]
        evalText "pi" @?= Right ["3.1415926535897932384…"]
        evalText "exp 1" @?= Right ["2.7182818284590452353…"]
        evalText "log 2" @?= Right ["0.69314718055994530941…"]
        evalText "tan (pi/4 * rad)" @?= Right ["1.0000000000000000000…"]
        evalText "sqrt 2 * sqrt 2" @?= Right ["2.0000000000000000000…"]
        evalText "exp (-80)" @?= Right ["1.8048513878454151723…e-35"]
        evalText "sinh 1e-20" @?= Right ["1.0000000000000000000…e-20"]
    , testCase "the same operation twice gives the same nudge, so it cancels" $ do
        evalText "sin (1 rad) - sin (1 rad)" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x - x" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x + 2 * x - 3 * x" @?= Right ["0"]
        evalText "let y = 1 ± 0.1 in y / y" @?= Right ["1"]
    , testCase "declared bounds print as mid ± r" $ do
        evalText "5 ± 0.1" @?= Right ["5.0 ± 0.1"]
        evalText "(5 ± 0.1) * (5 ± 0.1)" @?= Right ["25 ± 1"]
        evalText "(2 ± 0.1) ^ 3" @?= Right ["8.0 ± 1.3"]
        evalText "1e-30 * (1 ± 0.5)" @?= Right ["1.0e-30 ± 5e-31"]
    , testCase "a shared nudge squares into a one-sided range" $ do
        evalText "let n = noise 1 in n.0 * n.0" @?= Right ["0.5 ± 0.5"]
        evalText "let x = 5 ± 0.1 in x * x" @?= Right ["25 ± 1"]
    , testCase
        "standard uncertainties keep the σ marker and show a bound when it matters"
        $ do
          evalText "6.67430e-11 ±σ 1.5e-15" @?= Right ["6.67430e-11 ±σ 1.5e-15"]
          evalText "(6.67430e-11 ±σ 1.5e-15) * (2 ± 0.1)"
            @?= Right ["1.335e-10 ±σ 3e-15 (bound 6.7e-12)"]
          evalText "(1 ±σ 0.1) * (1 ±σ 0.1)" @?= Right ["1.00 ±σ 0.14 (bound 0.01)"]
    , testCase "noise and gauss are vectors of unit nudges" $ do
        evalText "noise 2" @?= Right ["[0 ± 1, 0 ± 1]"]
        evalText "gauss 1" @?= Right ["[0 ±σ 1]"]
        evalText "noise 2 · noise 2" @?= Right ["0 ± 2"]
        case evalText "noise x" of
          Left err -> T.isInfixOf "literal natural number" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testCase "tiny magnitudes keep their significant digits" $ do
        evalText "sqrt (1e-68 * (1 ± 1e-10))" @?= Right ["1.00000000000e-34 ± 5e-45"]
        evalText "sin (1e-20 rad)" @?= Right ["1.0000000000000000000…e-20"]
    , testCase "comparisons are decided only when the enclosures separate" $ do
        evalText "5 ± 0.1 < 6" @?= Right ["true"]
        evalText "let x = 5 ± 0.1 in x == x" @?= Right ["true"]
        evalText "5 ± 0.1 < 5.05"
          @?= Left
            "error: cannot decide comparison at sigma 3: the difference is -5.0e-2 ± 0.1"
        evalText "5 ±σ 0.1 < 5.4" @?= Right ["true"]
        evalText "5 ±σ 0.1 < 5.2"
          @?= Left
            "error: cannot decide comparison at sigma 3: the difference is -0.2 ± 0.0 ±σ 0.1"
        evalText "abs (sqrt 2 * sqrt 2 - 2) < 1e-9" @?= Right ["true"]
    , testCase ":set sigma widens the margin for statistical nudges only" $ do
        runLines [":set sigma 1", "5 ±σ 0.1 < 5.2"] @?= Right ["true"]
        runLines [":set sigma 1", "5 ± 0.1 < 5.05"]
          @?= Left
            "error: cannot decide comparison at sigma 1: the difference is -5.0e-2 ± 0.1"
    , testCase "integer rounding needs an enclosure inside one step" $ do
        evalText "floor (2.5 ± 0.1)" @?= Right ["2"]
        evalText "floor (2.5 ± 0.6)"
          @?= Left
            "error: cannot decide floor of an enclosure that straddles a rounding boundary"
    , testCase "domain errors name the problem" $ do
        evalText "sqrt (0 ± 1)" @?= Left "error: sqrt of a value that may be negative"
        evalText "log 0" @?= Left "error: log of a value that may be zero or negative"
        evalText "1 / (1 ± 2)" @?= Left "error: division by zero"
        evalText "asin 1" @?= Right ["1.5707963267948966192… rad"]
    , testCase "abs, atan2 and the hyperbolics" $ do
        evalText "abs (0 ± 1)" @?= Right ["0.5 ± 0.5"]
        evalText "abs ((5 ± 0.1) - 7)" @?= Right ["2.0 ± 0.1"]
        evalText "atan2 1 1" @?= Right ["0.78539816339744830961… rad"]
        evalText "atan2 (-1) (-1)" @?= Right ["-2.3561944901923449288… rad"]
        evalText "acos 0" @?= Right ["1.5707963267948966192… rad"]
        evalText "cosh 0" @?= Right ["1"]
        evalText "tanh 1" @?= Right ["0.76159415595576488811…"]
    , testCase "linear algebra over enclosures" $ do
        evalText "det [[1, 2], [3, 4]]" @?= Right ["-2"]
        evalText "det [[1 ± 0.01, 2], [3, 4]]" @?= Right ["-2.00 ± 0.04"]
        evalText "inverse [[1, 2], [3, 4]]" @?= Right ["[-2, 1; 1.5, -0.5]"]
        evalText "inverse [[1, 2], [3, 4]] · [[1, 2], [3, 4]]"
          @?= Right ["[1, 0; 0, 1]"]
        evalText "inverse [[1, 1], [1, 1]]"
          @?= Left "error: inverse of a singular matrix"
        evalText "inverse [[1 ± 1, 2], [3, 4]]"
          @?= Left "error: cannot decide inverse of a matrix whose enclosure may be singular"
        evalText "det [[0, 0], [0, 0]]" @?= Right ["0"]
        evalText "norm [3, 4]" @?= Right ["5"]
        evalText "norm [1, 1, 1]" @?= Right ["1.7320508075688772935…"]
    , testCase ":set precision changes the digits printed and the working precision" $ do
        runLines [":set precision 5", "pi", "1/3", "5 ± 0.1"]
          @?= Right ["3.1415…", "0.33333…", "5.0 ± 0.1"]
        runLines [":set precision 40", "pi"]
          @?= Right ["3.141592653589793238462643383279502884197…"]
    , testCase ":exact shows the midpoint, the nudges and their origins" $ do
        evalText ":exact 2 ± 0.1" @?= Right ["2 + 0.1·e[bound, input]"]
        runLines ["let x = 5 ± 0.1", ":exact x"] @?= Right ["5 + 0.1·e[bound, x]"]
        case evalText ":exact sin (1 rad)" of
          Right [out] ->
            T.isPrefixOf "0.84147098480789650665… + " out
              && T.isInfixOf "·e[bound, sin]" out
              @? T.unpack out
          other -> assertFailure (show other)
    , testCase ":budget lists nudges by kind, source and share"
        $ runLines ["let f x = sqrt x ± 1e-9", ":budget f 2"]
          @?= Right
            [ "1.4142135624 ± 1.4e-9"
            , "  kind   source  contribution  share"
            , "  bound  f @0    1e-9          100% of bound"
            , "  bound  sqrt    1e-26         0% of bound"
            ]
    , testCase "the prelude's G carries its σ and the derived masses inherit it" $ do
        evalP "G" @?= Right ["6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
        evalP "M_earth" @?= Right ["5.97217e24 ±σ 1.3e20 kg"]
        case evalP ":budget M_earth" of
          Right (_ : _ : row : _) -> T.isInfixOf "σ      G" row && T.isInfixOf "100% of σ²" row @? T.unpack row
          other -> assertFailure (show other)
    , testCase "a unit is a name: a quantity sharing its hash is not one" $ do
        runLinesP ["let x = 1", "x + 2"] @?= Right ["3"]
        runLinesP
          [ "unit dozen = 12"
          , "let eggs = 12"
          , "3 dozen"
          , "eggs + 1"
          , ":hash dozen"
          , ":hash eggs"
          ]
          @?= Right ["3 dozen", "13", "#" <> dozenHash, "#" <> dozenHash]
        case runLinesP ["let x = 1", "5 x"] of
          Left err -> T.isInfixOf "`x` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
        -- Bq and Hz are one definition and two units; each prints as written.
        runLinesP ["5 Bq", "5 Hz", "1 Bq == 1 Hz"] @?= Right ["5 Bq", "5 Hz", "true"]
    , testCase "a let that rebinds a unit name makes it a quantity"
        $ runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2", "2 g"]
          @?= Left
            "error at 1:3\n  2 g\n    ^\n  `g` is not a unit: a value next to a literal must be a unit (5 km, 3 (m/s)); write the `*`"
    , testCase
        "an alias of a unit is a unit, and a renamed unit prints under its new name"
        $ runLinesP
          [ ":alias klick km"
          , "5 klick"
          , "let d = 5 km"
          , ":add"
          , ":unname km"
          , "d"
          , ":view d"
          ]
          @?= Right
            [ "`klick` now also names #" <> kmHash
            , "5 klick"
            , "added d"
            , "removed the label `km`"
            , "5 klick"
            , "d = 5 * klick"
            ]
    , testCase ":prefer sets a display unit per dimension; to still wins; it persists" $ do
        runLinesP
          [ ":prefer km/h"
          , "5 m/s"
          , "100 km / (2 h)"
          , "5 m/s to m/s"
          , "3 m + 2 m"
          , ":prefer m/s"
          , ":prefer"
          , "5 km/h"
          , ":unprefer m/s"
          , "5 km/h"
          ]
          @?= Right
            [ "values of dimension [m s^-1] print in km/h"
            , "18 km h^-1"
            , "50 km h^-1"
            , "5 m s^-1"
            , "5 m"
            , "values of dimension [m s^-1] print in m/s"
            , "prefer m/s"
            , "1.3888888888888888888… m s^-1"
            , "removed the preference m/s"
            , "5 km h^-1"
            ]
        case evalP ":prefer 5" of
          Left err -> T.isInfixOf "has no unit to prefer" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "± on tensors: one independent nudge per component" $ do
        evalP "[1, 1, 1] m ± 0.1 m" @?= Right ["[1.0 ± 0.1, 1.0 ± 0.1, 1.0 ± 0.1] m"]
        runLinesP ["let v = [1, 1, 1] m ± 0.1 m", "v.0 - v.1", "v - v"]
          @?= Right ["0.0 ± 0.2 m", "[0, 0, 0] m"]
        evalP "[1, 2] ± [0.1, 0.2]" @?= Right ["[1.0 ± 0.1, 2.0 ± 0.2]"]
        case evalP "[1, 2] ± [0.1, 0.2, 0.3]" of
          Left err -> T.isInfixOf "shape and dimension of the value" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "covariance is the square-root factor's product; cholesky inverts it" $ do
        evalP "let x = gauss 2 in covariance [x.0 + 3 * x.1, 2 * x.0]"
          @?= Right ["[10, 2; 2, 4]"]
        evalP "cholesky [[4, 2], [2, 10]]" @?= Right ["[2, 0; 1, 3]"]
        evalP "cholesky [[4, 2], [2, 3]]"
          @?= Right ["[2, 0; 1, 1.4142135623730950488…]"]
        evalP "cholesky [[1, 2], [2, 1]]"
          @?= Left "error: sqrt of a value that may be negative"
        typeOfTextP "covariance" @?= Right "Vec n d -> Mat n n [d^2]"
        typeOfTextP "cholesky" @?= Right "Mat n n [d^2] -> Mat n n d"
    , testCase "v ±σ P is a vector with covariance P, stamped like any ±" $ do
        runLinesP
          [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "w"
          , "covariance w"
          , ":covariance w"
          ]
          @?= Right
            [ "[0 ±σ 2, 0.0 ±σ 3.2] m"
            , "[4, 2; 2, 10] m^2"
            , "covariance [4, 2; 2, 10] m^2"
            , "bound box [0, 0] m"
            ]
        runLinesP
          [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "let w2 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
          , "covariance (w - w2)"
          ]
          @?= Right ["[8, 4; 4, 20] m^2"]
        runLinesP
          [ "let w3 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2 #gps"
          , "let w4 = [0, 0] m ±σ [[4, 2], [2, 10]] m^2 #gps"
          , "w3 - w4"
          ]
          @?= Right ["[0, 0] m"]
        case evalP "[0, 0] m ± [[4, 2], [2, 10]] m^2" of
          Left err -> T.isInfixOf "a bound has no covariance" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase ":covariance separates the statistical part from the bound box" $ do
        evalP ":covariance 5 ±σ 0.1" @?= Right ["variance 0.01", "bound 0"]
        runLinesP ["let t = 45 deg ± 0.001 rad", ":covariance [cos t, sin t, 0] km"]
          @?= Right
            [ "covariance [0, 0, 0; 0, 0, 0; 0, 0, 0] km^2"
            , "bound box [0.00071, 0.00071, 0] km"
            ]
    , testCase "points: scales, .+ and .-, printing on the written scale" $ do
        evalP "20 degC" @?= Right ["20 degC"]
        evalP "20 °C .+ 5 K" @?= Right ["25 degC"]
        evalP "20 degC .+ 9 deltaF" @?= Right ["25 degC"]
        evalP "77 °F .- 68 °F" @?= Right ["9 deltaF"]
        evalP "20 degC to degF" @?= Right ["68 degF"]
        evalP "(25 degC .- 20 degC) to K" @?= Right ["5 K"]
        evalP "100 degC .- 32 degF" @?= Right ["100 K"]
        evalP "0 kelvin to degC" @?= Right ["-273.15 degC"]
        evalP "0 J2000 to JD" @?= Right ["2451545 JD"]
        evalP "(0 J2000 .+ 365.25 day) .- 0 J2000" @?= Right ["365.25 day"]
        evalP "100 gauge .- 0 gauge" @?= Right ["100 Pa"]
    , testCase "points over vectors: frames, projection, conversion between frames" $ do
        runLinesP
          [ "scale site = m at [100, 200, 0] m"
          , "[1, 2, 3] site"
          , ":type [1, 2, 3] site"
          , "([1, 2, 3] site) .- ([0, 0, 0] site)"
          , "([1, 2, 3] site) .+ [1, 1, 1] km"
          , "([1, 2, 3] site).0"
          , ":type ([1, 2, 3] site).0"
          , "[1, 2, 3] site == [1, 2, 3] site"
          , "scale eci = km at [0, 0, 0] km"
          , "[7000, 0, 0] eci to site"
          ]
          @?= Right
            [ "[1, 2, 3] site"
            , "Point (Vec 3 [m])"
            , "[1, 2, 3] m"
            , "[1001, 1002, 1003] site"
            , "1 site"
            , "Point [m]"
            , "true"
            , "[6999900, -200, 0] site"
            ]
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "Point (Tensor s d) -> Tensor s d -> Point (Tensor s d)"
        case runLinesP ["scale site = m at [100, 200, 0] m", "[1, 2, 3] site + [1, 1, 1] m"] of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case runLinesP
          ["scale site = m at [100, 200, 0] m", "[1, 2, 3] site < [2, 3, 4] site"] of
          Left err -> T.isInfixOf "no ordering on Point (Vec 3 [m])" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "points compare and have no sum" $ do
        evalP "20 degC < 70 degF" @?= Right ["true"]
        evalP "20 degC == 68 degF" @?= Right ["true"]
        evalP "0 J2000 < 0 MJD" @?= Right ["false"]
        typeOfTextP "20 degC" @?= Right "Point [K]"
        typeOfTextP "degC" @?= Right "Scale [K]"
        typeOfTextP "\\p q -> p .- q"
          @?= Right "Point (Tensor s d) -> Point (Tensor s d) -> Tensor s d"
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "Point (Tensor s d) -> Tensor s d -> Point (Tensor s d)"
        typeOfTextP "\\a b -> a < b" @?= Right "Num d -> Num d -> Bool"
        case evalP "20 degC + 5 degC" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "2 * (20 degC)" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "20 degC to K" of
          Left err -> T.isInfixOf "to with a scale" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "[1, 2] < [1, 3]" of
          Left err -> T.isInfixOf "no ordering on Vec 2" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "scale declarations: user scales, :view and :edit read back as written" $ do
        runLinesP
          [ "unit mmHg = 133.322 * Pa"
          , "scale bp = mmHg at 0 mmHg"
          , "120 bp .+ 10 mmHg"
          , "(120 bp .- 80 bp)"
          ]
          @?= Right ["130 bp", "40 mmHg"]
        runLinesP ["let boil = 100 degC", ":view boil"] @?= Right ["boil = 100 degC"]
        runLinesP [":edit degC"] @?= Right ["scale degC = K at 273.15 * K"]
        runLinesP [":edit km"] @?= Right ["unit km = 10^3 * m"]
    , testCase "display units of one dimension cancel against each other" $ do
        evalP "2 m * 90 deg / rad" @?= Right ["3.1415926535897932384… m"]
        evalP "3 h / min" @?= Right ["180"]
        evalP "1 km / m" @?= Right ["1000"]
        evalP "(2 km)^2 / m" @?= Right ["4000 km"]
        evalP "5 km / h" @?= Right ["5 km h^-1"]
        evalP "(3 rad/s) * 2 s" @?= Right ["6 rad"]
    , testCase
        "angle is a dimension: the circular functions take it, their inverses give it"
        $ do
          evalP "sin (45 deg)" @?= Right ["0.70710678118654752440…"]
          evalP "atan2 1 1 to deg" @?= Right ["45.000000000000000000… deg"]
          evalP "asin 1 to deg" @?= Right ["90 deg"]
          evalP "5 mrad to deg" @?= Right ["0.28647889756541160438… deg"]
          evalP "1 sr" @?= Right ["1 sr"]
          case evalP "sin 1" of
            Left err -> T.isInfixOf "write 1 rad or 45 deg" err @? T.unpack err
            Right v -> assertFailure (show v)
          case evalP "1 rad / s + 1 Hz" of
            Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "angles: deg is a unit built on pi" $ do
        evalP "90 deg" @?= Right ["90 deg"]
        evalP "90 deg to rad" @?= Right ["1.5707963267948966192… rad"]
        evalP "sin (90 deg)" @?= Right ["1.0000000000000000000…"]
        evalP "1 arcsec to deg" @?= Right ["0.00027777777777777777777… deg"]
    , testCase "identical definitions are different measurements; a - a still cancels" $ do
        runLines
          ["let a = 5 ± 0.1", "let b = 5 ± 0.1", "a - b", "a - a", "a - 2 * a + a"]
          @?= Right ["0.0 ± 0.2", "0", "0"]
        case runLines ["let a = 5 ± 0.1", "let b = 5 ± 0.1", ":hash a", ":hash b"] of
          Right [ha, hb] -> ha /= hb @? "a and b share a hash"
          other -> assertFailure (show other)
    , testCase
        "the owner stamp is implied: :view prints no label and the text round-trips"
        $ runLines ["let a = 5 ± 0.1", ":view a"] @?= Right ["a = 5 ± 0.1"]
    , testCase "a function-level tolerance is one unknown per input"
        $ runLines ["let f x = x ± 0.01", "f 2 - f 2", "f 2 - f 3"]
          @?= Right ["0", "-1.00 ± 0.02"]
    , testCase "a #label names the unknown: shared across definitions and values" $ do
        runLines ["let a = 5 ± 0.1 #s7", "let b = 5 ± 0.1 #s7", "a - b"] @?= Right ["0"]
        runLines ["let a = 5.0 ± 0.1 #s7", "let b = 5.2 ± 0.1 #s7", "a - b", "a + b"]
          @?= Right ["-0.2", "10.2 ± 0.2"]
        evalText "(5 ± 0.1 #s7) - (5 ± 0.1 #s7)" @?= Right ["0"]
        evalText "(5 ± 0.1 #s7) - (5 ± 0.1 #s8)" @?= Right ["0.0 ± 0.2"]
        evalText "(noise 2 #n) - (noise 2 #n)" @?= Right ["[0, 0]"]
    , testCase "labels print, parse and hash" $ do
        parseShape "5 ± 0.1 #s7"
          @?= Right (Lb "s7" (O (S.PlusMinus Bound) (N 5) (N (1 / 10))))
        parseShape "x == 5 ± 0.1 #s7"
          @?= Right (O S.Eq (V "x") (Lb "s7" (O (S.PlusMinus Bound) (N 5) (N (1 / 10)))))
        runLines ["let a = 5 ± 0.1 #s7", ":view a"] @?= Right ["a = 5 ± 0.1 #s7"]
        case runLines ["let a = 5 ± 0.1 #s7", "let b = 5 ± 0.1", ":hash a", ":hash b"] of
          Right [ha, hb] -> ha /= hb @? "tag and owner share a hash"
          other -> assertFailure (show other)
        case evalText "5 #s7" of
          Left err -> T.isInfixOf "labels nothing here" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase ":budget names tagged and owned nudges"
        $ runLines ["let span = (10 ± 0.01 #left) + (10 ± 0.01 #right)", ":budget span"]
          @?= Right
            [ "20.00 ± 0.02"
            , "  kind   source  contribution  share"
            , "  bound  left    0.01          50% of bound"
            , "  bound  right   0.01          50% of bound"
            ]
    , testCase "sqrt of a dimension that is not a square is a type error, not a loop"
        $ case evalP "sqrt (1 kg)" of
          Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testProperty "a product of enclosures encloses every product of their points"
        $ \(Small a) (Small b) (Small c) (Small d) (Small f) e1 e2 ->
          let x =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact (fromIntegral (a :: Int)))
                  (Exact (fromIntegral (c :: Int) / 7))
              y0 =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact (fromIntegral (b :: Int)))
                  (Exact (fromIntegral (d :: Int) / 7))
              y =
                uncertain
                  Bound
                  (Declared (Hash "y") [] 0)
                  y0
                  (Exact (fromIntegral (f :: Int) / 11))
              -- x and y share the nudge at site x (same midpoint-free id
              -- only when a == b; either way the check must hold).
              at = pointOf [(Hash "x", e1), (Hash "y", e2)]
              z = mulM 24 x y
           in abs (at x * at y - midpoint z) <= radius z
    , testProperty "sqrt, recip, exp and log enclose their true values"
        $ \(Positive n) (Positive d) e1 (Small k) ->
          let r = fromIntegral (n :: Int) / fromIntegral (d :: Int) :: Rational
              x =
                uncertain
                  Bound
                  (Declared (Hash "x") [] 0)
                  (Exact r)
                  (Exact (r / fromIntegral (2 + abs (k :: Int))))
              v = pointOf [(Hash "x", e1)] x
              lo z = midpoint z - radius z
              hi z = midpoint z + radius z
              inside z t = lo z <= t && t <= hi z
              squares z = lo z * lo z <= v && v <= hi z * hi z
              approx t = toRational (t :: Double)
           in counterexample (show (r, v))
                $ either (const False) squares (sqrtM 24 x)
                  && either (const False) (`inside` recip v) (recipM 24 x)
                  && near (expM 24 x) (approx (exp (fromRational v)))
                  && either (const False) (`near` approx (log (fromRational v))) (logM 24 x)
    ]
 where
  -- A point in the enclosure: every nudge at a chosen value in [-1, 1].
  pointOf :: [(Hash, Double)] -> Magnitude -> Rational
  pointOf es = \case
    Exact r -> r
    m@(Affine mid _ _) -> mid + sum [c * eOf n | (c, n) <- nudges m]
   where
    eOf n = case n.origin of
      Tagged _ _ -> 0
      Declared site _ _ -> maybe 0 (\e -> toRational (max (-1) (min 1 e))) (lookup site es)
      Builtin _ -> 0
  -- Double arithmetic is only good to about 1e-15 relative.
  near z t = abs (t - midpoint z) <= radius z + abs t * 1e-12 + 1e-300

{- | Where two terms stop being alpha-equivalent: the outermost differing
subterms, for counterexamples.
-}
firstDifference :: Term n -> Term n -> Maybe String
firstDifference a b
  | alphaEq a b = Nothing
  | otherwise = case (a, b) of
      (PrimApp p as, PrimApp q bs) | p == q, length as == length bs -> firstOf (zipWith firstDifference as bs)
      (Lam _ x, Lam _ y) -> firstDifference x y
      (App f x, App g y) -> firstOf [firstDifference f g, firstDifference x y]
      (Let _ e x, Let _ f y) -> firstOf [firstDifference e f, firstDifference x y]
      (Con c xs, Con c' ys) | c == c', length xs == length ys -> firstOf (zipWith firstDifference xs ys)
      (Case s xs, Case s' ys)
        | length xs == length ys ->
            firstOf (firstDifference s s' : zipWith altDifference xs ys)
      (Pow x n, Pow y m) | n == m -> firstDifference x y
      (Pack xs, Pack ys) | length xs == length ys -> firstOf (zipWith firstDifference xs ys)
      (Proj x i, Proj y j) | i == j -> firstDifference x y
      _ -> here
 where
  here = Just ("first difference:\n  " <> show a <> "\nvs\n  " <> show b)
  altDifference (Alt c _ x) (Alt c' _ y) = if c == c' && alphaEq x y then Nothing else here
  firstOf ds = case catMaybes ds of
    [] -> here
    d : _ -> Just d

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
        $ forAll (snd <$> genProgram)
        $ \e -> case desugarClosed noResolver e of
          Left _ -> discard
          Right (t, _) -> case decodeStored (encodeStored t) of
            Left err -> counterexample (T.unpack err) False
            Right t' ->
              counterexample
                (show t')
                (alphaEq t t' && encodeStored t' == encodeStored t && hashTerm t' == hashTerm t)
    , testCase "definitions, history, units, labels and cycles survive a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ "let speed = 5 km / h"
            , ":prefer kPa"
            , "unit furlong = 201.168 * m"
            , "let r = 10 mm ± 0.01 mm #batch7"
            , "let even n = if n == 0 then true else odd (n - 1); let odd n = if n == 0 then false else even (n - 1)"
            , "unit mmHg = 133.322 * Pa"
            , "scale bp = mmHg at 0 mmHg"
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
        loaded.codebase.scales @?= s.codebase.scales
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
            , "#lpdo2  (current)"
            , "#erifi"
            , "201.168 m"
            , "0 mm"
            , "true"
            , "false"
            , "r = 10 * mm ± 0.01 * mm #batch7"
            , "101.325 kPa"
            ]
    , testCase
        "the store only holds what the user added, plus the prelude terms those use"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir ["let d = 3 km", ":add"]
          (loaded, _) <- reload dir
          -- km and its definition chain are on disk; a prelude name the user
          -- never touched is still only in memory from the prelude.
          Map.size loaded.codebase.terms @?= Map.size withPrelude.codebase.terms + 1
          linesIn loaded ["d", "G"]
            @?= Right ["3 km", "6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
    , testCase "a user rebinding of a prelude name wins over the prelude on reload" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let c = 3e8 m / s", ":update"]
        (loaded, _) <- reload dir
        linesIn loaded ["c"] @?= Right ["300000000 m s^-1"]
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
    , testCase "a store of another format is refused" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let x = 1", ":add"]
        writeFile (dir </> "format") "eval codebase 99\n"
        opened <- openStore dir
        case opened of
          Left err -> T.isInfixOf "is not an eval codebase of format" err @? T.unpack err
          Right _ -> assertFailure "opened a store of another format"
    ]
 where
  withTempStore :: (FilePath -> IO a) -> IO a
  withTempStore k = do
    tmp <- getTemporaryDirectory
    stamp <- getPOSIXTime
    let dir = tmp </> ("eval-test-" <> show (round (stamp * 1000000) :: Integer))
    createDirectoryIfMissing True dir
    r <- k dir
    removePathForcibly dir
    pure r
  -- Feed lines one at a time, persisting after each, as Main does.
  persistLines :: FilePath -> [Text] -> IO Session
  persistLines dir ls = do
    st <- either (error . T.unpack) id <$> openStore dir
    let go s [] = pure s
        go s (l : rest) = case feed s l of
          Left err -> error (T.unpack err)
          Right (s', _) -> sync st s.codebase s'.codebase >> go s' rest
    go withPrelude ls
  reload :: FilePath -> IO (Session, [Text])
  reload dir = do
    st <- either (error . T.unpack) id <$> openStore dir
    (cb, notes) <- loadStore st withPrelude.codebase
    pure
      ( either
          (error . T.unpack)
          id
          (refreshPreferences withPrelude{codebase = cb, staging = cb})
      , notes
      )
  linesIn :: Session -> [Text] -> Either Text [Text]
  linesIn s0 = go s0 []
   where
    go _ acc [] = Right (concat (reverse acc))
    go s acc (l : rest) = do
      (s', outs) <- feed s l
      go s' (outs : acc) rest

{- | The short hash a prelude or scratch name prints as, for tests that
compare against @:hash@ output without pinning digests.
-}
hashShownAs :: [Text] -> Text -> Text
hashShownAs setup n = case runLinesP (setup ++ [":hash " <> n]) of
  Right outs | Just out <- lastMay outs -> T.drop 1 out
  other -> error ("hashShownAs: " <> show other)
 where
  lastMay xs = if null xs then Nothing else Just (last xs)

dozenHash :: Text
dozenHash = hashShownAs ["unit dozen = 12"] "dozen"

kmHash :: Text
kmHash = hashShownAs [] "km"

-- Tuples, lists and case --------------------------------------------------------------
--
-- Design §2.3, §5.1: Con and Case replaced If and the boolean literal.

dataTests :: TestTree
dataTests =
  testGroup
    "data"
    [ testCase "tuples: construction, types, fst and snd, equality" $ do
        evalP "(1, 2 m)" @?= Right ["(1, 2 m)"]
        typeOfTextP "(1, 2 m, true)" @?= Right "(Num, Num [m], Bool)"
        evalP "fst (3, 4)" @?= Right ["3"]
        evalP "snd (3, 4 s)" @?= Right ["4 s"]
        evalP "(1, 2) == (1, 2)" @?= Right ["true"]
        evalP "(1, 2) == (1, 3)" @?= Right ["false"]
        typeOfTextP "fst" @?= Right "(a, b) -> a"
    , testCase "lists: literals, cons, the prelude functions, laziness" $ do
        evalP "{1, 2, 3}" @?= Right ["{1, 2, 3}"]
        evalP "1 : {2, 3}" @?= Right ["{1, 2, 3}"]
        typeOfTextP "{1 m, 2 m}" @?= Right "{Num [m]}"
        evalP "map (\\x -> x * 2) {1, 2, 3}" @?= Right ["{2, 4, 6}"]
        evalP "length (range 1 10)" @?= Right ["10"]
        evalP "foldl (\\a b -> a + b) (0 m) {1 m, 2 m, 3 m}" @?= Right ["6 m"]
        evalP "zip {1, 2} {true, false}" @?= Right ["{(1, true), (2, false)}"]
        evalP "reverse (range 1 5)" @?= Right ["{5, 4, 3, 2, 1}"]
        evalP "filter (\\x -> x > 2) (range 1 5)" @?= Right ["{3, 4, 5}"]
        evalP "{1, 2} == {1, 2, 3}" @?= Right ["false"]
        typeOfTextP "map" @?= Right "(a -> b) -> {a} -> {b}"
        typeOfTextP "zip" @?= Right "{a} -> {b} -> {(a, b)}"
        -- a cons cell's tail is a thunk: an error in it surfaces only when walked
        evalP "fst (case 1 : {1 / 0} of {} -> (0, 0); x : _ -> (x, 0))" @?= Right ["1"]
    , testCase
        "case: one constructor deep, exhaustive, canonical order; _ and variables fill in" $ do
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
          @?= Right ["7.5 km s^-1", "(Vec 3 [m], Vec 3 [m s^-1])"]
    ]
