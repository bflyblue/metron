module Main (main) where

import Control.Monad (foldM, forM_)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Text.IO qualified as TIO
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Affine hiding (Builtin, DivideByZero)
import Eval.Affine qualified as A
import Eval.Codebase (
  Codebase (..),
  emptyCodebase,
  lookupName,
  lookupTypeName,
  showReference,
 )
import Eval.Core
import Eval.Desugar
import Eval.Dimension (DimAtom (..), Spelling (..), dimAtoms, dimOne, isDimOne)
import Eval.Driver
import Eval.Eval
import Eval.Hash
import Eval.Infer (TypeError (..), elaborateClosed)
import Eval.Lexer hiding (TNum, TProj)
import Eval.Lexer qualified as L
import Eval.Parser
import Eval.Prelude (preludeSource, stdlibCodebase, stdlibMoved, stdlibNames)
import Eval.Pretty
import Eval.Repl qualified as R
import Eval.Store
import Eval.Syntax qualified as S
import Eval.TCore
import Eval.Type
import Eval.Unicode qualified as U
import Gen (exprDepth, genProgram, instanceOf)
import System.Directory (
  createDirectoryIfMissing,
  doesDirectoryExist,
  doesFileExist,
  getTemporaryDirectory,
  listDirectory,
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
        , contractionTests
        , sliceTests
        , propertyTests
        , unitTests
        , lintRegressionTests
        , preludeTests
        , displayTests
        , affineTests
        , storeTests
        , dataTests
        , itTests
        , respellTests
        , replTests
        , namespaceTests
        , editTests
        , stdlibTests
        ]
    )

-- Term-building helpers -------------------------------------------------

num :: Rational -> Term n
num r = Lit (LTensor ([], [r]))

bool :: Bool -> Term n
bool b = Con (if b then "True" else "False") []

-- | An if, as the desugarer writes it: a case on Bool in canonical order.
ifT :: Term n -> Term n -> Term n -> Term n
ifT c t e = Case c [Alt (Builtin "False") VNil e, Alt (Builtin "True") VNil t]

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
  typesIn acc = TypeLookup (\k -> fst <$> lookup k acc) (const Nothing)

{- | Elaborate, lint, evaluate and render a closed term against some
definitions. Type errors, lint failures and evaluation errors all come
back as text.
-}
run :: Defs -> Term Z -> Either Text Text
run defs t = do
  elaborated <- elaborateDefs defs
  let typesOf = TypeLookup (\k -> fst <$> lookup k elaborated) (const Nothing)
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
              TBool
              (TPrimApp "add" (TFun numT (TFun numT numT)) [TVr FZ, TLit (LTensor ([], [1]))])
          )
          @?= Left "argument of add has type Bool, expected Num"
    , testCase
        "lint rejects a primitive at a type that is not an instance of its scheme"
        $ lintClosed
          noLookup
          ( TPrimApp
              "add"
              (TFun TBool (TFun TBool TBool))
              [TCon "True" TBool [], TCon "False" TBool []]
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
                , TLit (LTensor ([3], [1, 2, 3]))
                ]
        lintClosed noLookup (at 1) @?= Right [Forall [] (vecT (LLit 3))]
        case lintClosed noLookup (at 2) of
          Left err -> T.isInfixOf "not an instance of" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a mismatched let annotation"
        $ case lintClosed
          noLookup
          (TLet "x" (Forall [] TBool) (TLit (LTensor ([], [1]))) (TVr FZ)) of
          Left err -> T.isPrefixOf "let binder annotated" err @? T.unpack err
          Right sc -> assertFailure (show sc)
    , testCase "lint rejects a type application without an abstraction"
        $ lintClosed noLookup (TTyApp (TLit (LTensor ([], [1]))) (AType TBool))
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
    , testCase "a dot glued to a name is a field access, not composition"
        $ toks "r.x" @?= Right [TIdent "r", TField "x"]
    , testCase "dot with spaces is composition, .xs is not a projection"
        $ toks "f . g" @?= Right [TIdent "f", TOp ".", TIdent "g"]
    , testCase "projection must be glued to an atom"
        $ either (const True) (const False) (toks "v .0") @? "expected an error"
    , testCase "a glued ._ is a wildcard axis; ._name is not" $ do
        toks "m._.0 t._._.2"
          @?= Right [TIdent "m", TWild, L.TProj 0, TIdent "t", TWild, TWild, L.TProj 2]
        toks "x._y" @?= Right [TIdent "x", TOp ".", TIdent "_y"]
        either (const True) (const False) (toks "m ._.0") @? "expected an error"
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
  | Sl Tree Int Int
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
  S.Slice a k i -> Sl (shape a) k i
  S.FieldOf a f -> A (shape a) (V f)
  S.Record hd fs -> foldl (\acc (n, x) -> A acc (A (V n.text) (shape x))) (shape hd) fs

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
    , testCase "slices: each wildcard skips an axis, left to right" $ do
        parseShape "m._.0" @?= Right (Sl (V "m") 1 0)
        parseShape "t._._.2" @?= Right (Sl (V "t") 2 2)
        parseShape "t._.0.1" @?= Right (Pj (Sl (V "t") 1 0) 1)
        parseShape "t.1._.0" @?= Right (Sl (Pj (V "t") 1) 1 0)
        parseShape "f m._.0" @?= Right (A (V "f") (Sl (V "m") 1 0))
        parseShape "r.x._.0" @?= Right (Sl (A (V "r") (V "x")) 1 0)
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
          Right (_, prov) -> Map.lookup [] prov.spans @?= Just (S.Span (S.Pos 1 1) (S.Pos 1 6))
          Left err -> assertFailure (T.unpack err)
    , testCase "provenance records children by path"
        $ case parseExpr "1 + 20"
          >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
          Right (_, prov) -> Map.lookup [1] prov.spans @?= Just (S.Span (S.Pos 1 5) (S.Pos 1 7))
          Left err -> assertFailure (T.unpack err)
    , testCase "a resolver turns free names into references"
        $ let resolver n =
                if n == "k"
                  then Just (ATerm (Resolution (h "kay", Nothing) False False))
                  else Nothing
           in case parseExpr "k + 1"
                >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
                Right (t, _) ->
                  assertBool (show t) (alphaEq t (Ref (h "kay") Nothing "" +. num 1 :: Term Z))
                Left err -> assertFailure (T.unpack err)
    , testCase "codebase names shadow primitives"
        $ let resolver n =
                if n == "sqrt"
                  then Just (ATerm (Resolution (h "mine", Nothing) False False))
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
    , testCase "negative" $ renderRational 20 (-(1 / 4)) @?= "-0.25"
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
    [ testCase
        ":ls lists names with their types, filtered by glob, kind or type query"
        $ do
          let ls args =
                runLinesP
                  ( [ "let speed = 7.5 km/s"
                    , "unit furlong = 201.168 * m"
                    , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
                    , "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"
                    ]
                      ++ [":ls " <> args]
                  )
          ls ""
            @?= Right
              [ "area : Shape -> Num [m^2]"
              , "unit furlong : Num [m]"
              , "speed : Num [m s^-1]"
              , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
              , "Circle : Num [m] -> Shape"
              , "Rect : Num [m] -> Num [m] -> Shape"
              , "namespace std (" <> T.pack (show (length stdlibNames)) <> " names)"
              ]
          ls "k*m"
            @?= Right
              [ "unit klm : Num [cd rad^2]"
              , "unit km : Num [m]"
              , "unit kohm : Num [kg m^2 s^-3 A^-2]"
              ]
          ls "--units furl" @?= Right ["unit furlong : Num [m]"]
          ls "--scales degC" @?= Right ["scale degC : Scale [K]"]
          ls "--types"
            @?= Right
              [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
              , "Circle : Num [m] -> Shape"
              , "Rect : Num [m] -> Num [m] -> Shape"
              , -- The library's one type, the joint covariance in blocks.
                "data Cov2 n d d1 = Cov2 {rr :: Mat n n [d^2], rv :: Mat n n [d d1], vv :: Mat n n [d1^2]}"
              , "Cov2 : Mat n n [d^2] -> Mat n n [d d1] -> Mat n n [d1^2] -> Cov2 n d d1"
              ]
          ls ": Shape -> a" @?= Right ["area : Shape -> Num [m^2]"]
          ls ": {a} -> Num" @?= Right ["length : {a} -> Num"]
          -- unification both ways: the query's d is one variable, cross has two
          ls ": Vec 3 d -> Vec 3 d -> Vec 3 [d^2]"
            @?= Right ["cross : Vec 3 d -> Vec 3 d1 -> Vec 3 [d d1]"]
          ls "Rect : Num [m] -> Num [m] -> b"
            @?= Right ["Rect : Num [m] -> Num [m] -> Shape"]
          ls "nothing-like-this" @?= Right ["nothing matches"]
          case ls "--bogus" of
            Left err -> T.isInfixOf "unknown flag --bogus" err @? T.unpack err
            Right v -> assertFailure (show v)
          case ls ": Nope" of
            Left err -> T.isInfixOf "unknown type `Nope`" err @? T.unpack err
            Right v -> assertFailure (show v)
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
    , testCase "indices, vzipWith and vimap (design §3.3)" $ do
        typeOfText "indices" @?= Right "Vec n d -> Vec n"
        typeOfText "vzipWith"
          @?= Right "(Num d -> Num d1 -> Num d2) -> Tensor s d -> Tensor s d1 -> Tensor s d2"
        typeOfTextP "vimap" @?= Right "(Num -> Num d -> Num d1) -> Vec n d -> Vec n d1"
        typeOfText "indices ([1, 2] m)" @?= Right "Vec 2"
    , testCase "timap's index is a Vec (rank s) (design §4.1)" $ do
        typeOfText "timap"
          @?= Right "(Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1"
        -- Projecting from the index asks for that many leading lengths.
        typeOfText "\\t -> timap (\\i x -> i.0 * x) t"
          @?= Right "Tensor (n : s) d -> Tensor (n : s) d"
        typeOfText "\\t -> timap (\\i x -> if i.0 == i.1 then x else 0) t"
          @?= Right "Tensor (n : m : s) -> Tensor (n : m : s)"
        -- A length-polymorphic function on the index leaves the rank open.
        typeOfText "\\t -> timap (\\i x -> dot i i * x) t"
          @?= Right "Tensor s d -> Tensor s d"
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
            [ "Tensor (n : m : s) -> Tensor (n : m : s)"
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
            , "(Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1"
            , "[0, 2; 0, 4]"
            ]
        -- A rank in a type encodes under its own length tag and decodes back.
        let def =
              TypeDef
                [(0, KShape)]
                [[TTensor (SCons (LRank 0 1) (SVar 0)) dimOne]]
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
          @?= Right "Tensor (n : n : s) d -> Tensor s d"
        typeOfText "\\t -> contract 0 2 t"
          @?= Right "Tensor (n : m : n : s) d -> Tensor (m : s) d"
        typeOfText "\\t -> permute [2, 0, 1] t"
          @?= Right "Tensor (n : m : k : s) d -> Tensor (k : n : m : s) d"
        typeOfText "\\t -> permute [1, 0] t"
          @?= Right "Tensor (n : m : s) d -> Tensor (m : n : s) d"
        typeOfTextP "trace" @?= Right "Tensor (n : n : s) d -> Tensor s d"
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
          @?= Right ["g = \\x -> permute [2, 0, 1] x"]
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
        typeOfText "([1, 2; 3, 4] m)._.0" @?= Right "Vec 2 [m]"
    , testCase "types are computed from the axis and position" $ do
        typeOfText "\\m -> m._.0"
          @?= Right "Tensor (n : m + 1 : s) d -> Tensor (n : s) d"
        typeOfText "\\t -> t._._.2"
          @?= Right "Tensor (n : m : k + 3 : s) d -> Tensor (n : m : s) d"
        typeOfText "\\m -> m._.0 + m._.2"
          @?= Right "Tensor (n : m + 3 : s) d -> Tensor (n : s) d"
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
  Right (t, _) -> case elaborateClosed noLookup t of
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
        withElaborated src e $ \_ (schemes, typed) -> lintClosed noLookup typed === Right schemes
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
  , -- The same in the unicode spelling of `:set unicode on` (design §7.3).
    testProperty "printed Core in unicode re-parses to an alpha-equivalent term"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          let printed = renderTermIn Unicode (\_ _ _ -> "#") VNil t
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
            fmap fst (elaborateClosed noLookup t)
              === fmap fst (elaborateClosed noLookup t)
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
    TData _ _ -> "data"
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
    , testCase "a rank mismatch names both ranks" $ do
        case evalText "indices [[1, 2], [3, 4]]" of
          Left err -> T.isInfixOf "a vector against a matrix" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalText "norm 3" of
          Left err -> T.isInfixOf "a vector against a number" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalText "[1, 2] + [[1, 2], [3, 4]]" of
          Left err -> T.isInfixOf "a vector against a matrix" err @? T.unpack err
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

-- Prelude ----------------------------------------------------------------------------

-- | A session on a seeded codebase: the library under std, with `use std` stored.
seeded :: Session
seeded = either (error . T.unpack) id seededSession

-- | What a new store is seeded with, and a format-3 store migrated with.
theSeed :: Either Text Seed
theSeed = stdlibSeed

evalP :: Text -> Either Text [Text]
evalP src = snd <$> feed seeded src

runLinesP :: [Text] -> Either Text [Text]
runLinesP = go seeded []
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
        $ length stdlibNames > 600 @? "prelude is unexpectedly small"
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
    , testCase "vimap maps with each component's position as a value" $ do
        evalP "vimap (\\i x -> i * x) [10, 20, 30]" @?= Right ["[0, 20, 60]"]
        runLinesP ["let v = [1, 2, 3] m", "vimap (\\i x -> x) v == v"]
          @?= Right ["true"]
        evalP "vimap (\\i x -> i * x) ([1, 2, 3] m)" @?= Right ["[0, 2, 6] m"]
        -- The position is a value, not a literal (design §2.10).
        case evalP "vimap (\\i x -> x ^ i) [1, 2]" of
          Left err -> T.isInfixOf "expecting - or integer literal" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "let v = [1, 2]\nvimap (\\i x -> v.i) v" of
          Left err -> T.isInfixOf "unknown field `i`" err @? T.unpack err
          Right v -> assertFailure (show v)
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
    [ testCase ":set unicode prints the unicode spellings, which read back" $ do
        runLinesP [":set"] @?= Right ["precision 20", "sigma 3", "unicode off"]
        runLinesP [":set unicode on", ":set", ":set unicode off", ":set"]
          @?= Right
            [ "precision 20"
            , "sigma 3"
            , "unicode on"
            , "precision 20"
            , "sigma 3"
            , "unicode off"
            ]
        case runLinesP [":set unicode maybe"] of
          Left err -> T.isInfixOf "unicode is on or off" err @? T.unpack err
          Right v -> assertFailure (show v)
        let defs =
              [ "let f x = x^2 + 1"
              , "let g x y = if x <= y then x^-1 else y"
              , "data Body = Body {mass :: Num [kg], vel :: Vec 3 [m/s]}"
              ]
            inputs =
              [ "9.81 m/s^2"
              , "5 km / h"
              , "Body {mass = 5 kg, vel = [0, 0, 1] m/s}"
              , ":type (\\x -> x, 9.81 m/s^2)"
              , ":view f"
              , ":view g"
              , ":view Body"
              ]
            ascii =
              [ "9.81 m s^-2"
              , "5 km h^-1"
              , "Body {mass = 5 kg, vel = [0, 0, 1] m s^-1}"
              , "(a -> a, Num [m s^-2])"
              , "f = \\x -> x^2 + 1"
              , "g = \\x -> \\y -> if x <= y then x^-1 else y"
              , "data Body = Body {mass :: Num [kg], vel :: Vec 3 [m s^-1]}"
              ]
            unicode =
              [ "9.81 m s⁻²"
              , "5 km h⁻¹"
              , "Body {mass = 5 kg, vel = [0, 0, 1] m s⁻¹}"
              , "(a → a, Num [m s⁻²])"
              , "f = λx → x² + 1"
              , "g = λx → λy → if x ≤ y then x⁻¹ else y"
              , "data Body = Body {mass :: Num [kg], vel :: Vec 3 [m s⁻¹]}"
              ]
        runLinesP (defs ++ inputs) @?= Right ascii
        -- The one input with a unicode spelling is echoed in it first.
        runLinesP (defs ++ ":set unicode on" : inputs)
          @?= Right ("  ≡ 9.81 m/s²" : unicode)
        -- Both spellings lex to the same tokens, a superscript power standing
        -- for its caret form.
        let caret = concatMap $ \case
              TSup n -> [TOp "^"] ++ [TOp "-" | n < 0] ++ [L.TNum (fromInteger (abs n))]
              t -> [t]
        mapM_
          (\(a, u) -> (caret <$> toks u) @?= toks a)
          (zip ascii unicode)
        -- A superscript is glued only to an atom: after a stale `x#hash`
        -- (a hash label to the lexer) the power keeps its caret.
        let power namer k =
              renderTermIn
                Unicode
                (\_ _ _ -> namer)
                VNil
                (Pow (Ref selfType Nothing (Hint "x")) k)
        power "x" (-2) @?= "x⁻²"
        power "x#a3f9k" 2 @?= "x#a3f9k^2"
        -- and read back as the same values and definitions
        runLinesP
          [ "data Body = Body {mass :: Num [kg], vel :: Vec 3 [m s⁻¹]}"
          , "9.81 m s⁻²"
          , "Body {mass = 5 kg, vel = [0, 0, 1] m s⁻¹}"
          , "let f = λx → x² + 1"
          , ":view f"
          ]
          @?= Right
            [ "9.81 m s^-2"
            , "Body {mass = 5 kg, vel = [0, 0, 1] m s^-1}"
            , "f = \\x -> x^2 + 1"
            ]
    , testCase "a quantity prints in the unit it was written in" $ do
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

{- | A position and a velocity built on two shared statistical nudges, so
that their cross-covariance is full: over @(e0, e1)@, @r@ has coefficient
rows @(1, 2)@ and @(3, 0)@, @v@ rows @(0, 1)@ and @(1, -1)@.
-}
correlatedPair :: [Text]
correlatedPair =
  [ "let e = gauss 2"
  , "let r = [e.0 + 2 * e.1, 3 * e.0] m"
  , "let v = [e.1, e.0 - e.1] m/s"
  ]

{- | Design §12, "A filter step in blocks": the lines whose outputs the
document quotes. A change here goes there too.
-}
filterStep :: [Text]
filterStep =
  [ "let eye = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
  , "let r0 = [7000, 0, 0] km ±σ 1 km"
  , "let v0 = [0, 7.5, 0] km/s ±σ 1 m/s"
  , "let r1 = r0 + v0 * (10 s)"
  , "let p1 = jointCovariance (r1, v0)"
  , "p1.rv"
  , ":covariance (r1, v0)"
  , "let dt = 60 s"
  , "let phi = (eye, dt * eye, [0, 0, 0; 0, 0, 0; 0, 0, 0] s^-1, eye)"
  , "let p2 = propagateCov2 phi p1"
  , "p2 == jointCovariance (r1 + v0 * dt, v0)"
  , "p2.rr"
  , "p2.rv"
  , "let h_r = [[1, 0, 0]]"
  , "let h_v = [[0, 0, 0]] s"
  , "let r_meas = [[(10 m)^2]]"
  , "let s_innov = innovationCov2 h_r h_v p2 r_meas"
  , "s_innov"
  , "let k = gain2 h_r h_v p2 (inverse s_innov)"
  , "k"
  , "let p3 = updateCov2 k h_r h_v p2"
  , "p3.rr to m^2"
  , "p3.rv to m^2/s"
  , "p3.vv to m^2/s^2"
  , "transpose p2.rv - snd k @ (h_r @ p2.rr + h_v @ transpose p2.rv) == transpose p3.rv"
  ]

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
    , testCase "mid, bound and sd take an enclosure apart" $ do
        let parts x = map (\f -> evalP (f <> " (" <> x <> ")")) ["mid", "bound", "sd"]
        parts "1 ± 0.1" @?= [Right ["1"], Right ["0.1"], Right ["0"]]
        parts "1 ±σ 0.1" @?= [Right ["1"], Right ["0"], Right ["0.1"]]
        parts "(1 ± 0.1) + (2 ± 0.2)" @?= [Right ["3"], Right ["0.3"], Right ["0"]]
        parts "(1 ±σ 0.1) * 2 + (1 ± 0.05)"
          @?= [Right ["3"], Right ["0.05"], Right ["0.2"]]
        parts "5" @?= [Right ["5"], Right ["0"], Right ["0"]]
        parts "1/3" @?= [Right ["0.33333333333333333333…"], Right ["0"], Right ["0"]]
        -- the bound of a nonlinear result is the printed one
        evalP "bound ((5 ± 0.1) * (5 ± 0.1))" @?= Right ["1.01"]
        -- the operand's dimension and display unit
        evalP "bound (10 mm ± 0.1 mm)" @?= Right ["0.1 mm"]
        evalP "mid (10 mm ± 0.1 mm)" @?= Right ["10 mm"]
        evalP "sd (2 km ±σ 3 m)" @?= Right ["0.003 km"]
        -- elementwise on tensors
        evalP "bound ([1, 2] m ± 0.1 m)" @?= Right ["[0.1, 0.1] m"]
        evalP "mid ([1, 2; 3, 4] ±σ 0.5)" @?= Right ["[1, 2; 3, 4]"]
        evalP "sd ([1, 2] ±σ 0.5)" @?= Right ["[0.5, 0.5]"]
        -- σ is a square root: exact when the variance is a square, an
        -- enclosure otherwise
        case evalP "sd ((1 ±σ 0.1) + (1 ±σ 0.1 #other))" of
          Right [v] -> T.isPrefixOf "0.1414213562" v @? T.unpack v
          other -> assertFailure (show other)
        typeOfTextP "mid" @?= Right "Tensor s d -> Tensor s d"
        typeOfTextP "bound" @?= Right "Tensor s d -> Tensor s d"
        typeOfTextP "sd" @?= Right "Tensor s d -> Tensor s d"
        typeOfTextP "bound (1 m ± 1 cm)" @?= Right "Num [m]"
        -- a policy of one's own: consistent within the bound and three σ
        runLinesP
          [ "let consistent a b = let d = a - b in abs (mid d) <= bound d + 3 * sd d"
          , "consistent (5 ± 0.1) (5.05)"
          , "consistent (5 ±σ 0.01) (5.1)"
          ]
          @?= Right ["true", "false"]
    , testCase "sigma a e is the prefix spelling of a ±σ e, beside within" $ do
        evalP "sigma 1 0.1" @?= Right ["1.0 ±σ 0.1"]
        evalP "1 `sigma` 0.1" @?= evalP "1 ±σ 0.1"
        evalP "sd (sigma 1 0.1)" @?= Right ["0.1"]
        runLinesP ["let x = sigma 1 0.1", ":view x"] @?= Right ["x = 1 ±σ 0.1"]
        -- it declares an uncertainty, so a #label may follow it
        evalP "(sigma 1 0.1 #a) - (1 ±σ 0.1 #a)" @?= Right ["0"]
        -- and, like within, it is not a unit
        case evalP "3 sigma" of
          Left err -> T.isInfixOf "`sigma` is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
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
        -- det is polymorphic in the size, with no static size check, and is
        -- on dimensionless matrices only (design §4.3, §4.6).
        typeOfTextP "det" @?= Right "Mat n n -> Num"
        typeOfTextP "\\a -> det a + 1" @?= Right "Mat n n -> Num"
        runLinesP ["let d a = det a", "d [[2, 0, 0], [0, 3, 0], [0, 0, 4]] + d [[2]]"]
          @?= Right ["26"]
        evalP "det ([[1 m, 0 m], [0 m, 2 m]] / (1 m))" @?= Right ["2"]
        case evalP "det [[1 m, 0 m], [0 m, 1 m]]" of
          Left err ->
            T.isInfixOf "expected Mat n n, got Mat 2 2 [m]: dimensions differ by [m^-1]" err
              @? T.unpack err
          Right v -> assertFailure (show v)
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
    , testCase
        "crossCovariance sums cᵢc'ⱼᵀ over the statistical nudges two vectors share"
        $ do
          -- Over (e0, e1): r has rows (1, 2) and (3, 0), v rows (0, 1) and
          -- (1, -1), so Cov(r, v) = [1·0 + 2·1, 1·1 + 2·(-1); 3·0, 3·1].
          runLinesP
            ( correlatedPair
                ++ [ "crossCovariance r v"
                   , "crossCovariance v r == transpose (crossCovariance r v)"
                   , "crossCovariance r r == covariance r"
                   ]
            )
            @?= Right ["[2, -1; 0, 3] m^2 s^-1", "true", "true"]
          -- Correlated nudges from a covariance matrix.
          runLinesP
            [ "let w = [0, 0] m ±σ [[4, 2], [2, 10]] m^2"
            , "crossCovariance w w == covariance w"
            , "crossCovariance w w"
            ]
            @?= Right ["true", "[4, 2; 2, 10] m^2"]
          -- Independent vectors: all zeros, in the product of the dimensions.
          runLinesP
            [ "crossCovariance ([1, 2] m ±σ 1 m) ([3, 4, 5] s ±σ 1 s)"
            , ":type crossCovariance ([1, 2] m ±σ 1 m) ([3, 4, 5] s ±σ 1 s)"
            , "crossCovariance ([1, 2] km ±σ 1 m) ([1, 2] h ±σ 1 s)"
            ]
            @?= Right ["[0, 0, 0; 0, 0, 0] m s", "Mat 2 3 [m s]", "[0, 0; 0, 0] km h"]
          -- A shared bound nudge is no covariance.
          evalP "crossCovariance ([1, 2] m ± 1 m #a) ([3, 4] m ± 1 m #a)"
            @?= Right ["[0, 0; 0, 0] m^2"]
          typeOfTextP "crossCovariance" @?= Right "Vec n d -> Vec m d1 -> Mat n m [d d1]"
    , testCase "jointCovariance and the block filter: the types" $ do
        typeOfTextP "jointCovariance" @?= Right "(Vec n d, Vec n d1) -> Cov2 n d d1"
        typeOfTextP "Cov2"
          @?= Right "Mat n n [d^2] -> Mat n n [d d1] -> Mat n n [d1^2] -> Cov2 n d d1"
        typeOfTextP "propagateCov2"
          @?= Right
            "(Mat n m [d1 d2 d3 d^-2], Mat n m [d1 d3^2 d^-2], Mat n m d2, Mat n m d3) -> Cov2 m [d d2^-1] [d d3^-1] -> Cov2 n [d1 d3 d^-1] d"
        typeOfTextP "innovationCov2"
          @?= Right
            "Mat n m d -> Mat n m d1 -> Cov2 m [d1 d2 d^-1] d2 -> Mat n n [d1^2 d2^2] -> Mat n n [d1^2 d2^2]"
        typeOfTextP "gain2"
          @?= Right
            "Mat n m d -> Mat n m d1 -> Cov2 m [d1 d2 d^-1] d2 -> Tensor (n : s) d3 -> (Tensor (m : s) [d1^2 d2^2 d3 d^-1], Tensor (m : s) [d1 d2^2 d3])"
        typeOfTextP "updateCov2"
          @?= Right
            "(Mat n m d, Mat n m [d1^2 d2^-1]) -> Mat m n [d^-1] -> Mat m n [d2 d1^-2] -> Cov2 n [d d2 d1^-1] d1 -> Cov2 n [d d2 d1^-1] d1"
    , testCase "propagateCov2 agrees exactly with the affine forms' own correlation" $ do
        runLinesP
          ( correlatedPair
              ++ [ "let p = jointCovariance (r, v)"
                 , "p"
                 , "let eye = [[1, 0], [0, 1]]"
                 , -- Φ = I is the identity on the record.
                   "propagateCov2 (eye, [[0, 0], [0, 0]] s, [[0, 0], [0, 0]] s^-1, eye) p == p"
                 , -- Φ = [I, Δt I; 0, I]: the blocks of Φ P Φᵀ against the
                   -- covariance of (r + v Δt, v) read off the nudges.
                   "propagateCov2 (eye, 10 s * eye, [[0, 0], [0, 0]] s^-1, eye) p == jointCovariance (r + v * (10 s), v)"
                 , -- A Φ with every block full and of its own dimension.
                   "let f_rr = [[1, 2], [0, 1]]"
                 , "let f_rv = [[3, 0], [1, 1]] s"
                 , "let f_vr = [[0, 1], [2, 0]] s^-1"
                 , "let f_vv = [[1, 0], [1, 1]]"
                 , "propagateCov2 (f_rr, f_rv, f_vr, f_vv) p"
                 , "jointCovariance (f_rr @ r + f_rv @ v, f_vr @ r + f_vv @ v)"
                 , "propagateCov2 (f_rr, f_rv, f_vr, f_vv) p == jointCovariance (f_rr @ r + f_rv @ v, f_vr @ r + f_vv @ v)"
                 ]
          )
          @?= Right
            [ "Cov2 {rr = [5, 3; 3, 9] m^2, rv = [2, -1; 0, 3] m^2 s^-1, vv = [1, -1; -1, 2] m^2 s^-2}"
            , "true"
            , "true"
            , "Cov2 {rr = [74, 28; 28, 16] m^2, rv = [26, 41; 12, 12] m^2 s^-1, vv = [10, 13; 13, 25] m^2 s^-2}"
            , "Cov2 {rr = [74, 28; 28, 16] m^2, rv = [26, 41; 12, 12] m^2 s^-1, vv = [10, 13; 13, 25] m^2 s^-2}"
            , "true"
            ]
    , testCase
        ":covariance of a pair prints the blocks of jointCovariance and both boxes"
        $ do
          expecting
            ( runLinesP
                ( correlatedPair
                    ++ [ ":covariance (r, v)"
                       , "let p = jointCovariance (r, v)"
                       , "p.rr"
                       , "p.rv"
                       , "p.vv"
                       ]
                )
            )
            $ \outs -> do
              take 4 outs
                @?= [ "rr [5, 3; 3, 9] m^2"
                    , "rv [2, -1; 0, 3] m^2 s^-1"
                    , "vv [1, -1; -1, 2] m^2 s^-2"
                    , "bound box ([0, 0] m, [0, 0] m s^-1)"
                    ]
              map (T.drop 3) (take 3 outs) @?= drop 4 outs
          runLinesP [":covariance ([1, 2] m ± 0.5 m, [3, 4] m/s ±σ 1 m/s)"]
            @?= Right
              [ "rr [0, 0; 0, 0] m^2"
              , "rv [0, 0; 0, 0] m^2 s^-1"
              , "vv [1, 0; 0, 1] m^2 s^-2"
              , "bound box ([0.5, 0.5] m, [0, 0] m s^-1)"
              ]
          evalP ":covariance ([1, 2] m, [[1]])"
            @?= Left "covariance: a number, a vector, or a pair of vectors"
    , testCase "design §12: a filter step in blocks"
        $ runLinesP filterStep
          @?= Right
            [ "[1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1"
            , "rr [1.0001, 0, 0; 0, 1.0001, 0; 0, 0, 1.0001] km^2"
            , "rv [1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1"
            , "vv [1e-6, 0, 0; 0, 1e-6, 0; 0, 0, 1e-6] km^2 s^-2"
            , "bound box ([0, 0, 0] km, [0, 0, 0] km s^-1)"
            , "true"
            , "[1.0049, 0, 0; 0, 1.0049, 0; 0, 0, 1.0049] km^2"
            , "[7e-5, 0, 0; 0, 7e-5, 0; 0, 0, 7e-5] km^2 s^-1"
            , "[[1005000]] m^2"
            , "([0.99990049751243781094…; 0; 0], [6.9651741293532338308…e-5; 0; 0] s^-1)"
            , "[99.990049751243781094…, 0, 0; 0, 1004900, 0; 0, 0, 1004900] m^2"
            , "[0.0069651741293532338308…, 0, 0; 0, 70, 0; 0, 0, 70] m^2 s^-1"
            , "[0.99512437810945273631…, 0, 0; 0, 1, 0; 0, 0, 1] m^2 s^-2"
            , "true"
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
        -- The library lives under std, so :edit prints its definitions in that block.
        runLinesP [":edit degC"]
          @?= Right ["namespace std", "  scale degC = K at 273.15 * K"]
        runLinesP [":edit km"] @?= Right ["namespace std", "  unit km = 10^3 * m"]
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
      Declared site _ _ -> maybe 0 (toRational . max (-1) . min 1) (lookup site es)
      A.Builtin _ -> 0
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
          loaded.codebase.scales @?= s.codebase.scales
          loaded.codebase.uses @?= [S.Use "std" Nothing]
          linesIn loaded ["d", "G"]
            @?= Right ["3 km", "6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
          -- The seed is at time 0, before the user's lines.
          ls <- T.lines <$> TIO.readFile (dir </> "names.log")
          ("0 use std" `elem` ls) @? "the stored use is a log line"
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
            @?= Right
              [ "[1, 0; 0, 1] m^2"
              , "[0, 0; 0, 0] m s"
              , "Cov2 {rr = [1, 0; 0, 1] m^2, rv = [0, 0; 0, 0] m s, vv = [1, 0; 0, 1] s^2}"
              , "rr [1, 0; 0, 1] m^2"
              , "rv [0, 0; 0, 0] m s"
              , "vv [1, 0; 0, 1] s^2"
              , "bound box ([0, 0] m, [0, 0] s)"
              , "data Cov2 n d d1 = Cov2 {rr :: Mat n n [d^2], rv :: Mat n n [d d1], vv :: Mat n n [d1^2]}"
              , "Cov2 : Mat n n [d^2] -> Mat n n [d d1] -> Mat n n [d1^2] -> Cov2 n d d1"
              ]
    , testCase "a root binding shadows the library's on reload; :unuse std persists" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let c = 3e8 m / s", ":add", ":unuse std"]
        (loaded, _) <- reload dir
        loaded.codebase.uses @?= []
        linesIn loaded ["c", "std.c", ":use std", "1 km"]
          @?= Right ["300000000 m s^-1", "299792458 m s^-1", "stored use std", "1 km"]
        ls <- T.lines <$> TIO.readFile (dir </> "names.log")
        any (" unuse std" `T.isSuffixOf`) ls @? "an unuse line"
    , testCase
        "a format-3 store is migrated: seeded before its log, the old G kept as history"
        $ withTempStore
        $ \dir -> do
          -- A store as the format-3 code wrote it: the prelude in memory at the
          -- root, only the user's labels in the log, the prelude terms they use
          -- written beside theirs.
          createDirectoryIfMissing True (dir </> "terms")
          createDirectoryIfMissing True (dir </> "types")
          writeFile (dir </> "format") "eval codebase 3\n"
          user <-
            either
              (assertFailure . T.unpack)
              pure
              ( foldM
                  (\s l -> fst <$> feed s l)
                  legacyPrelude
                  ["let c = 3e8 m / s", ":update", "let d = 3 km", "let w = 2 * G", ":add"]
              )
          sync (Store dir) legacyPrelude.codebase user.codebase
          before <- T.lines <$> TIO.readFile (dir </> "names.log")
          (loaded, notes) <- reload dir
          notes @?= []
          readFile (dir </> "format") >>= (@?= "eval codebase 4\n")
          loaded.codebase.uses @?= [S.Use "std" Nothing]
          -- The user's own lines are still there, after the seed.
          afterwards <- T.lines <$> TIO.readFile (dir </> "names.log")
          lastN (length before) afterwards @?= before
          linesIn loaded ["c", "std.c", "d", "1 km", "w"]
            @?= Right
              [ "300000000 m s^-1"
              , "299792458 m s^-1"
              , "3 km"
              , "1 km"
              , "1.33486e-10 ±σ 3e-15 m^3 kg^-1 s^-2"
              ]
          -- The seed brings the library's record type, its labels included.
          linesIn loaded ["(jointCovariance ([1, 2] m ±σ 1 m, [3, 4] m ±σ 1 m)).rr"]
            @?= Right ["[1, 0; 0, 1] m^2"]
          expecting (linesIn loaded [":ls std"]) $ \outs ->
            ("unit km : Num [m]" `elem` outs) @? "the library is listed"
          -- w uses the root G the old prelude had, which is now std.G's history.
          linesIn loaded [":view w", ":todo"]
            @?= Right ["w = 2 * G#e1bms", "stale: w uses G#e1bms (use :upgrade G)"]
          expecting (linesIn loaded [":upgrade std.G", ":view w"]) $ \outs ->
            last outs @?= "w = 2 * G"
          -- The old G in std.G's history is the migration's, not the user's:
          -- a newer library's G still updates it.
          moved <- either (assertFailure . T.unpack) pure stdlibMoved
          newer <-
            either
              (assertFailure . T.unpack)
              pure
              (sessionP [multiline ["namespace std", "  let G = 7"], ":update"])
          case stdlibUpgrade newer.codebase moved loaded of
            Left err -> assertFailure (T.unpack err)
            Right (_, outs) ->
              any ("updated G #" `T.isPrefixOf`) outs @? show outs
          -- Merged into a store seeded fresh, std.G still ends on the new G.
          let fresh = dir </> "fresh"
          _ <- persistLines fresh []
          _ <- mergeInto fresh dir
          (merged, _) <- reload fresh
          lookupName "std.G" merged.codebase @?= lookupName "std.G" seeded.codebase
          linesIn merged ["w"] @?= Right ["1.33486e-10 ±σ 3e-15 m^3 kg^-1 s^-2"]
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
              [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
                , "  unit au = 149597870700 * m"
                , "  scale tip = au at 0 au"
                , "  data Body = Body {mass :: Num [kg], dist :: Num [m]}"
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
        loaded.codebase.history @?= s.codebase.history
        loaded.codebase.units @?= s.codebase.units
        loaded.codebase.scales @?= s.codebase.scales
        loaded.codebase.typeNames @?= s.codebase.typeNames
        loaded.codebase.conNames @?= s.codebase.conNames
        loaded.codebase.fieldNames @?= s.codebase.fieldNames
        Map.member "celestial.kepler.anomaly" loaded.codebase.names @? "renamed"
        Map.member "mechanics.mass" loaded.codebase.fieldNames @? "field path"
        Set.member "mechanics.au" loaded.codebase.units @? "unit path"
        Set.member "mechanics.tip" loaded.codebase.scales @? "scale path"
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
          Left err -> T.isInfixOf "is not a unit" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a type indexed by rank survives a reload" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["data Idx s = Idx (Vec (rank s))", ":add"]
        (loaded, notes) <- reload dir
        notes @?= []
        linesIn loaded [":view Idx", ":type Idx [0, 1, 2]"]
          @?= Right ["data Idx s = Idx (Vec (rank s))", "Idx [n, m, k]"]
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
        opened <- openStore theSeed dir
        case opened of
          Left err -> T.isInfixOf "is not an eval codebase of format" err @? T.unpack err
          Right _ -> assertFailure "opened a store of another format"
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
              [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
              , "data Body = Body {mass :: Num [kg]}"
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
              ["1", "2 kg", "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"]
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
        "merging from what is not a store is refused and touches nothing; old formats migrate"
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
          refused plain "is not an eval codebase"
          listDirectory plain >>= (@?= ["notes.txt"])
          refused (root </> "missing") "no such directory"
          doesDirectoryExist (root </> "missing") >>= (@?= False)
          _ <- persistLines (root </> "future") ["let x = 1", ":add"]
          writeFile (root </> "future" </> "format") "eval codebase 99\n"
          refused (root </> "future") "is not an eval codebase of format"
          -- an empty store of format 2 migrates on open, and the report says so
          createDirectoryIfMissing True (root </> "old")
          writeFile (root </> "old" </> "format") "eval codebase 2\n"
          r <- mergeInto a (root </> "old")
          map (T.isInfixOf "was migrated in place from format 2") r.notes @?= [True]
          readFile (root </> "old" </> "format")
            >>= (@?= "eval codebase " <> show formatVersion <> "\n")
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
    st <- either (error . T.unpack) id <$> openStore theSeed dir
    let go s [] = pure s
        go s (l : rest) = case feed s l of
          Left err -> error (T.unpack err)
          Right (s', _) -> sync st s.codebase s'.codebase >> go s' rest
    go seeded ls
  reload :: FilePath -> IO (Session, [Text])
  reload dir = do
    st <- either (error . T.unpack) id <$> openStore theSeed dir
    (cb, notes) <- loadStore st emptyCodebase
    pure
      ( either
          (error . T.unpack)
          id
          (refreshPreferences emptySession{codebase = cb, staging = cb})
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
          @?= Right ["7.5 km s^-1", "(Vec 3 [m], Vec 3 [m s^-1])"]
    , testCase "declared types: constructors, case, types, printing" $ do
        runLinesP
          [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
            , "Num [m] -> Shape"
            , "Shape -> Num [m^2]"
            , "Rect (1 m) (2 m)"
            , "{3.1415926535897932384… m^2, 2 m^2}"
            , "{Shape}"
            , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
            , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
          @?= Right ["{Just 1, Just 2}", "5", "0", "a -> Maybe a -> a", "Maybe a"]
    , testCase "declared types: parameters take their kinds from use; recursion" $ do
        runLinesP
          [ "data Q d = Q (Num d) (Num d)"
          , "let lo q = case q of Q a _ -> a"
          , "lo (Q (1 m) (2 m))"
          , ":type Q"
          , ":type lo"
          , "data V n = V (Vec n [m]) (Vec n [m/s])"
          , ":type V"
          , "data Tree a = Leaf | Node (Tree a) a (Tree a)"
          , "let sumTree z t = case t of Leaf -> z; Node l x r -> sumTree z l + x + sumTree z r"
          , "sumTree (0 kg) (Node (Node Leaf (1 kg) Leaf) (2 kg) (Node Leaf (3 kg) Leaf))"
          , ":type sumTree"
          , ":view Tree"
          , "data Body = Body (Num [kg]) (Vec 3 [m]) (Vec 3 [m/s])"
          , "let mass b = case b of Body m _ _ -> m"
          , "mass (Body (5 kg) ([1,2,3] km) ([4,5,6] km/s))"
          , "data E = E (Num [kg m^2 / s^2]) (Num [N]) (Num [m s⁻²]) (Point [K]) Bool (Num, {Num [m]})"
          , ":view E"
          ]
          @?= Right
            [ "1 m"
            , "Num d -> Num d -> Q d"
            , "Q d -> Num d"
            , "Vec n [m] -> Vec n [m s^-1] -> V n"
            , "6 kg"
            , "Tensor s d -> Tree (Tensor s d) -> Tensor s d"
            , "data Tree a = Leaf | Node (Tree a) a (Tree a)"
            , "5 kg"
            , "data E = E (Num [kg m^2 s^-2]) (Num [kg m s^-2]) (Num [m s^-2]) (Point [K]) Bool (Num, {Num [m]})"
            ]
    , testCase "declared types: == and /= when every field compares" $ do
        runLinesP
          [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
          [ "data Shape = Circle (Num [m])"
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
          [ "data Body = Body {mass :: Num [kg], pos :: Vec 3 [m], vel :: Vec 3 [m/s]}"
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
            , "Vec 3 [m]"
            , "Body {mass = 6 kg, pos = [1, 2, 3] km, vel = [0, 0, 0] m s^-1}"
            , "Body -> Num [kg m^2 s^-2]"
            , "kinetic = \\b -> 0.5 * (case b of Body mass _ _ -> mass) * norm (case b of Body _ _ vel -> vel)^2"
            , "[4001, 5001, 6001] m s^-1"
            , "bump = \\dv -> \\b -> case b of Body mass pos vel -> Body mass pos ((case b of Body _ _ vel' -> vel') + dv)"
            , "[9, 9, 9] m s^-1"
            , "data Body = Body {mass :: Num [kg], pos :: Vec 3 [m], vel :: Vec 3 [m s^-1]}"
            , "2 m"
            , "1"
            , "a -> b -> Pair a b"
            ]
        let refused src needle = case runLinesP src of
              Left err -> T.isInfixOf needle err @? T.unpack err
              Right v -> assertFailure (show v)
            body = "data Body = Body {mass :: Num [kg], pos :: Vec 3 [m]}"
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
            , "data Body = Body (Num [kg]) (Vec 3 [m])"
            , "Body (1 kg) ([0, 0, 0] m)"
            ]
        -- a glued .name is a field, so composition needs spaces
        evalP "(sqrt . abs) (-16)" @?= Right ["4"]
        case evalP "(sqrt.abs) (-16)" of
          Left err -> T.isInfixOf "unknown field `abs`" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "record values print with their field names and read back" $ do
        let decls =
              [ "data Body = Body {mass :: Num [kg], pos :: Vec 3 [m]}"
              , "data Pair a b = Pair {first :: a, second :: b}"
              , "data Maybe a = Nothing | Just a"
              , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
            [ "Vec (rank s) -> Idx s"
            , "data Idx s = Idx (Vec (rank s))"
            , "Tensor s d -> Vec (rank s) -> Tagged s d"
            , "Tagged [1, 2; 3, 4] [0, 1]"
            , "Tagged [2, 2] 1"
            , "Tensor s d -> Vec (rank s) -> Tagged s d"
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
        refused ["data W = W (Num [furlong])"] "a dimension is a product of base units"
        refused ["data W = W (Vec [m])"] "a length is a number, a parameter, or rank s"
        refused
          ["data Maybe a = Nothing | Just a", "case Just 1 of Nothing -> 0"]
          "does not cover Just"
        refused
          ["data Maybe a = Nothing | Just a", "case Just 1 of Nothing -> 0; Just -> 1"]
          "has 1 fields"
        refused
          ["data Shape = Circle (Num [m])", "Circle 1"]
          "expected Num [m], got Num"
        refused
          ["data Shape = Circle (Num [m])", "Circle (1 m) (2 m)"]
          "Shape is not a function"
        -- `1 m` is an application too: the unit is the second argument, and
        -- the type error says how to write the quantity
        refused
          ["data Shape = Circle (Num [m])", "Circle 1 m"]
          "hint: 1 and `m` are two separate arguments here; a quantity in argument position needs parentheses: (1 m)"
        refused
          ["data Shape = Circle (Num [m])", "let c = Circle 1 m"]
          "hint: 1 and `m` are two separate arguments"
        refused ["let f a b = a + b", "f [1,2] km 3"] "parentheses: (the vector km)"
        -- a bound name is not a unit, so no hint
        case runLinesP ["let g m = sqrt 2 m"] of
          Left err -> not (T.isInfixOf "hint:" err) @? T.unpack err
          Right v -> assertFailure (show v)
        -- :add refuses a type that exists with another definition.
        refused
          [ "data Shape = Circle (Num [m])"
          , ":add"
          , "data Shape = Circle (Num [s])"
          , ":add"
          ]
          "already exists with a different definition"
    , testCase "declared types: names are labels" $ do
        let outs =
              runLinesP
                [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
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
            T.isPrefixOf "Num [m] -> Num [m] -> #" ty @? T.unpack ty
          other -> assertFailure (show other)
    , testCase
        "constructors and definitions share one namespace; the newer label wins"
        $ do
          runLinesP
            [ "1 T"
            , "data Temp = T (Num [K])"
            , "T (300 K)"
            , ":type T"
            , "let T = 2"
            , "T + 1"
            ]
            @?= Right ["1 T", "T (300 K)", "Num [K] -> Temp", "3"]
          case runLinesP ["data Temp = T (Num [K])", "1 T"] of
            Left err -> T.isInfixOf "`T` is not a unit" err @? T.unpack err
            Right v -> assertFailure (show v)
    , testCase "the type grammar" $ do
        let ok src = case parseType src of
              Left err -> assertFailure (T.unpack err)
              Right _ -> pure ()
        mapM_
          ok
          [ "Num [m]"
          , "Vec 3 [m] -> Maybe a"
          , "(a, Num [kg m^2 / s^2])"
          , "{Tree a}"
          , "Point (Vec 3 [m])"
          , "Tensor [2, 3] d"
          , "Num"
          ]
        case parseProgram "structural data Pair a b = Pair a b | Other (Num [m])" of
          Right [S.SData d] -> do
            d.name.text @?= "Pair"
            map (.text) d.params @?= ["a", "b"]
            map (\(c, fs) -> (c.text, length fs)) d.constructors
              @?= [("Pair", 2), ("Other", 1)]
            d.structural @?= True
          other -> assertFailure (show other)
    ]

-- | The session after feeding lines to one with the prelude.
sessionP :: [Text] -> Either Text Session
sessionP = go seeded
 where
  go s [] = Right s
  go s (l : ls) = feed s l >>= \(s', _) -> go s' ls

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
        runLinesP ["3 m + 2 m", ":type it"] @?= Right ["5 m", "Num [m]"]
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

-- The unicode echo ------------------------------------------------------------------

respellTests :: TestTree
respellTests =
  testGroup
    "unicode echo"
    [ testCase "an input line in its unicode spelling" $ do
        respell "2 +-s 0.1 * 3 km/h" @?= Just "2 ±σ 0.1 * 3 km/h"
        respell "\\x -> x^2 <= 4" @?= Just "λx → x² ≤ 4"
        respell "1 +- 0.1" @?= Just "1 ± 0.1"
        respell "u >< v @ w" @?= Just "u × v · w"
        respell "a /\\ b .* c ./ d" @?= Just "a ∧ b ⊙ c ⊘ d"
        respell "f . g" @?= Just "f ∘ g"
        respell "a /= b || c" @?= Just "a ≠ b ∨ c"
    , testCase "nothing to respell gives nothing" $ do
        respell "1 + 2" @?= Nothing
        -- names, `*`, `/` and `&&` keep their spelling
        respell "sqrt (2 * pi) / 3 deg && true" @?= Nothing
        -- already unicode
        respell "λx → x² ≤ 4" @?= Nothing
        respell "a ⋅ b" @?= Nothing
        -- input that does not lex
        respell "1 \" 2 -> 3" @?= Nothing
    , testCase "superscripts for glued integer powers" $ do
        respell "x^2 + y^-1" @?= Just "x² + y⁻¹"
        respell "(a + b)^3 * [1, 2]^10" @?= Just "(a + b)³ * [1, 2]¹⁰"
        respell "9.81 m s^-2" @?= Just "9.81 m s⁻²"
        -- a spaced caret, or one not after an atom, stays
        respell "x ^ 2" @?= Nothing
        respell "x^ 2" @?= Nothing
    , testCase "spans are kept when lengths differ" $ do
        respell "a <= b && c >= d" @?= Just "a ≤ b && c ≥ d"
        respell "\\x y -> x^-2 <= y +-s 1 -> 2" @?= Just "λx y → x⁻² ≤ y ±σ 1 → 2"
        respell "(\\x -> x)   >=   y -- a comment -> here"
          @?= Just "(λx → x)   ≥   y -- a comment -> here"
        -- a tab counts as the lexer counts it
        respell "x\t<= 1 ->\t2" @?= Just "x\t≤ 1 →\t2"
        -- `f\x` must not become the identifier `fλx`
        respell "f\\x -> x" @?= Just "f\\x → x"
    , testCase ":set unicode on echoes statement lines" $ do
        runLinesP [":set unicode on", "2 +-s 0.1"]
          @?= Right ["  ≡ 2 ±σ 0.1", "2.0 ±σ 0.1"]
        runLinesP [":set unicode on", "let f x = x^2", "f 3"]
          @?= Right ["  ≡ let f x = x²", "9"]
        -- nothing to respell, a command, or unicode off: no echo
        runLinesP [":set unicode on", "1 + 2"] @?= Right ["3"]
        runLinesP [":set unicode on", ":type \\x -> x"] @?= Right ["a → a"]
        runLinesP ["2 +-s 0.1"] @?= Right ["2.0 ±σ 0.1"]
    ]

-- REPL: completion, unicode entry, colour ---------------------------------------

-- | Complete at the end of a line, as haskeline asks: reversed left text.
completeAt :: Session -> String -> Maybe (String, [R.Completion])
completeAt s line = R.complete s (reverse line, "")

replacements :: Session -> String -> [String]
replacements s line = maybe [] (map (.replacement) . snd) (completeAt s line)

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

-- | Text in an SGR colour, as "Eval.Repl" paints it.
coloured :: Text -> Text -> Text
coloured code t = "\ESC[" <> code <> "m" <> t <> "\ESC[0m"

keyword', unit', type', grey', red' :: Text -> Text
keyword' = coloured "35"
unit' = coloured "36"
type' = coloured "33"
grey' = coloured "90"
red' = coloured "31"

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
                $ sessionP ["data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"]
        replacements s "area (Ci" @?= ["Circle"]
        "Shape" `elem` replacements s ":view Sh" @? "Shape"
    , testCase "fields complete after a dot" $ do
        let s =
              either (error . T.unpack) id
                $ sessionP
                  [ "data Body = Body {mass :: Num [kg], vel :: Vec 3 [m/s]}"
                  , "let b = Body (5 kg) ([0, 0, 1] m/s)"
                  ]
        completeAt s "b.ma" @?= Just ("b", [R.Completion ".mass" "mass" True])
        map (.display) (R.completions s "b" ".ma") @?= ["mass"]
        -- Every field in scope completes, the library's Cov2 fields among them.
        map (.display) (R.completions s "b" ".") @?= ["mass", "rr", "rv", "vel", "vv"]
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
          (R.classify (Right ["area : Shape -> Num [m^2]", "unit furlong : Num [m]"]))
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
          [ "Num [m] -> Shape"
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
          , "data Shape = Circle (Num [m]) |"
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
          [ "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
          , three
          , ":type area"
          , "area (Rect (2 m) (3 m))"
          ]
          @?= Right
            [ "Shape -> Num [m^2]"
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
        let decl = "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
            numM = type' "Num" <> " [" <> unit' "m" <> "]"
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
        R.paint (R.namesOf shapes) R.Signature "area : Shape -> Num [m^2]"
          @?= "area : "
            <> type' "Shape"
            <> " -> "
            <> type' "Num"
            <> " ["
            <> unit' "m"
            <> "^2]"
        R.paint names R.Signature "unit furlong : Num [m]"
          @?= keyword' "unit" <> " furlong : " <> type' "Num" <> " [" <> unit' "m" <> "]"
        -- Type variables named like units stay plain outside brackets.
        R.paint names R.Type "(g → m) → {g}" @?= "(g → m) → {g}"
        R.highlightType names "g -> Num [g]"
          @?= "g -> " <> type' "Num" <> " [" <> unit' "g" <> "]"
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
          "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"
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
                , red' "  expected Num [m], got Num [s]: dimensions differ by [m s^-1]"
                ]
          map stripSgr painted @?= T.splitOn "\n" err
          -- The visible columns of the excerpt and the carets are unchanged.
          map (T.length . stripSgr) painted @?= map T.length (T.splitOn "\n" err)
    , testCase "paint: what does not lex falls back to its kind" $ do
        R.paint names R.Value "3 m $ 4 km" @?= "3 m $ 4 " <> unit' "km"
        R.paint names R.Signature "x : Num [m] ?" @?= "x : " <> type' "Num [m] ?"
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
              , "data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"
              , "area : Shape -> Num [m^2]"
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
      $ sessionP ["data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])"]
  bodies =
    either (error . T.unpack) id
      $ sessionP ["data Body = Body {mass :: Num [kg], pos :: Vec 3 [km]}"]
  isPrefixOfS p x = take (length p) x == p
  agrees name u
    | Just n <- lookup u superscripts =
        toks ("m" <> glued u) == Right [TIdent "m", TSup n]
          && isRight (evalP ("2" <> glued u))
          && evalP ("2" <> glued u) == evalP ("2^" <> T.pack (show n))
    | name == "sqrt" =
        -- A prefix operator where sqrt is an application (§7.3): same value.
        toks u == Right [TSqrt] && evalP "√9" == evalP "sqrt 9" && isRight (evalP "√9")
    | Just a <- lookup u asciiSpellings =
        let lexed = toks ("a " <> u <> " b")
         in isRight lexed && lexed == toks ("a " <> a <> " b")
    | otherwise =
        toks u == Right [TIdent u] || toks ("x" <> u) == Right [TIdent ("x" <> u)]
  superscripts = [(T.singleton c, n) | (c, n) <- zip "⁰¹²³⁴⁵⁶⁷⁸⁹" [0 ..]] ++ [("⁻", -1)]
  glued u = if u == "⁻" then "⁻¹" else u
  isRight = either (const False) (const True)

-- Namespaces (design §7.6) ------------------------------------------------------------

-- | A multi-line input, as a file or continuation lines give it.
multiline :: [Text] -> Text
multiline = T.intercalate "\n"

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
root definition, a unit, a scale, a record with a field a function uses, a
cycle, a block definition shadowing a root name, and a prelude reference.
-}
exportScript :: [Text]
exportScript =
  [ multiline
      [ "let size = 10"
      , "let d = 2 km"
      , "unit furlong = 201.168 * m"
      , "namespace orbital"
      , "  unit au = 149597870700 * m"
      , "  scale tip = au at 1 au"
      , "  data Body = Body {mass :: Num [kg], dist :: Num [m]}"
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
      , "  let useOrbital = orbital.kepler.anomaly 1 2 + orbital.weight orbital.earth / g0 / kg"
      , "  data Probe = Probe {body :: orbital.Body, place :: Num [m]}"
      , "  let probePlace p = p.place"
      ]
  , ":add"
  ]

-- | An error that mentions a text.
expectError :: Either Text [Text] -> Text -> Assertion
expectError r needle = case r of
  Left err ->
    (needle `T.isInfixOf` err)
      @? T.unpack ("expected " <> needle <> " in:\n" <> err)
  Right outs -> assertFailure ("expected an error, got " <> show outs)

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
            lastN 4 outs
              @?= ["use std (stored)", "use std (stored)", "use orbital", "use std (stored)"]
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
                    , "  data Body = Body {mass :: Num [kg], dist :: Num [m]}"
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
              @?= "data orbital.Body = orbital.Body {mass :: Num [kg], dist :: Num [m]}"
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
        -- The library's labels are under std (design §7.7).
        expectError
          (runLinesP [multiline ["namespace std.km", "  let x = 1"]])
          "`std.km` is a definition; it cannot also be a namespace"
        expectError
          (runLinesP [":namespace std.km"])
          "`std.km` is a definition; it cannot also be a namespace"
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
                  , "  unit au = 149597870700 * m"
                  , "  data Body = Body {mass :: Num [kg]}"
                  , "  let mu = 3"
                  ]
              , ":add"
              , ":ls orbital"
              ]
          )
          $ \outs ->
            lastN 4 outs
              @?= [ "unit au : Num [m]"
                  , "mu : Num"
                  , "data Body = Body {mass :: Num [kg]}"
                  , "Body : Num [kg] -> Body"
                  ]
        expecting (runLinesP (orbitalSetup ++ [":namespace orbital", ":ls"])) $ \outs ->
          lastN 2 outs @?= ["mu : Num", "period : Num d -> Num d"]
        -- Alone at the root: the root's own labels, then the namespaces under it.
        expecting (runLinesP (orbitalSetup ++ [":ls"])) $ \outs ->
          lastN 2 outs
            @?= [ "namespace orbital (2 names)"
                , "namespace std (" <> T.pack (show (length stdlibNames)) <> " names)"
                ]
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
              @?= ["mu : Num", "period : Num d -> Num d", "namespace kepler (1 name)"]
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
                    , "  unit au = 149597870700 * m"
                    , "  data Body = Body {mass :: Num [kg]}"
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
          $ \outs -> last outs @?= "d = 2 * km"
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
                  ["namespace orbital", "  let km = 5", "  let d = 2 std.km", "  let e = km"]
              , ":add"
              , ":namespace orbital"
              , ":view d"
              , ":view e"
              , "d"
              ]
          )
          $ \outs -> lastN 3 outs @?= ["d = 2 * std.km", "e = km", "2 std.km"]
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
        same "scales" (.scales)
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
            @?= [ "use std"
                , "namespace orbital"
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
        expectError (runLinesP [":export out.ev"]) "only the REPL writes files"
        expectError (runLinesP [":export dir/out"]) "only the REPL writes files"
        expectError
          (runLinesP [":export orbitl"])
          "`orbitl` is not a namespace; to write a file give a path like orbitl.ev"
        fmap fst (exportRequest s ["orbitl"])
          @?= Left "`orbitl` is not a namespace; to write a file give a path like orbitl.ev"
        expectError
          (runLinesP [":export nowhere out.ev"])
          "`nowhere` is not a namespace"
        fmap fst (exportRequest s ["out.ev"]) @?= Right (Just "out.ev")
        fmap fst (exportRequest s ["orbital", "out.ev"]) @?= Right (Just "out.ev")
        fmap snd (exportRequest s ["orbital", "out.ev"])
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
              [ multiline ["namespace orbital", "  unit au = 149597870700 * m"]
              , ":add"
              , multiline
                  [ "namespace orbital"
                  , "  data Orbit = Orbit {radius :: Num [au]}"
                  , "  let one = 1 au"
                  ]
              , "data Pair = Pair orbital.Orbit orbital.Orbit"
              ]
        runLinesP (setup ++ ["2 orbital.au", "orbital.one to km", "3 .std.km"])
          @?= Right ["added orbital.au", "2 orbital.au", "149597870.7 km", "3 km"]
        expecting (runLinesP (setup ++ [":add", ":view Pair", ":edit orbital.Orbit"])) $ \outs ->
          lastN 3 outs
            @?= [ "data Pair = Pair orbital.Orbit orbital.Orbit"
                , "namespace orbital"
                , "  data Orbit = Orbit {radius :: Num [m]}"
                ]
    , testCase "a dotted name is plain in the highlighter" $ do
        s <- either (assertFailure . T.unpack) pure (sessionP orbitalSetup)
        R.highlight (R.namesOf s) "orbital.period 2" @?= "orbital.period 2"
    ]

-- The :edit round trip (design §7.3) -------------------------------------------------

{- | A codebase to edit: two namespaces, root definitions, a unit, a record
with a field a function uses, a cycle, a @±@ definition, a leaf to move,
and dependents across namespaces.
-}
editScript :: [Text]
editScript =
  [ multiline
      [ "let size = 10"
      , "let trip = 2 km"
      , "let area w h = w * h"
      , "unit furlong = 201.168 * m"
      , "namespace orbital"
      , "  data Body = Body {mass :: Num [kg], dist :: Num [m]}"
      , "  let weight b = b.mass * 9.81 m/s^2"
      , "  let earth = Body {mass = 6 kg, dist = 1 km}"
      , "  let x = 3"
      , "  let y = x + 1"
      , "  let spare = 42"
      , "  let jitter = 2 +- 0.5"
      , "  let even n = if n == 0 then true else odd (n - 1)"
      , "  let odd n = if n == 0 then false else even (n - 1)"
      , "namespace mechanics"
      , "  let g0 = 9.80665 m/s^2"
      , "  let fall t = g0 * t^2 / 2"
      , "  let useY = orbital.y * size"
      ]
  , ":add"
  ]

editSession :: IO Session
editSession = either (assertFailure . T.unpack) pure (sessionP editScript)

-- | The file @:edit args@ would open.
editFileOf :: Session -> [Text] -> IO Text
editFileOf s args = case editRequest s args of
  Right (EditOpen _ (Right file) _) -> pure file
  other -> assertFailure ("no file to edit: " <> show other)

-- | The text with the first occurrence of a part replaced, which must be there.
replaceOnce :: Text -> Text -> Text -> IO Text
replaceOnce old new text = case T.breakOn old text of
  (_, rest) | T.null rest -> assertFailure (T.unpack ("no " <> old <> " in:\n" <> text))
  (before, rest) -> pure (before <> new <> T.drop (T.length old) rest)

-- | An edit that must succeed.
edited :: EditScope -> Text -> Session -> IO (Session, [Text])
edited target text s =
  either
    (\err -> assertFailure (T.unpack (err <> "\nin the file:\n" <> text)))
    pure
    (applyEdit target text s)

-- | The labels and history of two codebases are the same.
sameLabels :: Codebase -> Codebase -> Assertion
sameLabels a b = do
  a.names @?= b.names
  a.history @?= b.history
  a.typeNames @?= b.typeNames
  a.conNames @?= b.conNames
  a.fieldNames @?= b.fieldNames
  a.units @?= b.units
  a.scales @?= b.scales

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
        -- The same body under another keyword is an update of the label.
        plain <- editFileOf s [] >>= replaceOnce "unit furlong" "let furlong"
        (s2, outs2) <- edited EditCodebase plain s
        outs2 @?= ["updated furlong: unit -> let"]
        expectError (snd <$> feed s2 "2 furlong") "`furlong` is not a unit"
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
              >>= replaceOnce "dist :: Num [m]}" "dist :: Num [s]}"
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
              >>= replaceOnce "dist :: Num [m]}" "dist :: Num [m], spin :: Num}"
              >>= replaceOnce "Body (6 * kg) (1 * km)" "Body (6 * kg) (1 * km) 3"
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
              >>= replaceOnce "dist :: Num [m]}" "dist :: Num [m], spin :: Num}"
          (_, outs3) <- edited (EditName "orbital.Body") added s
          map (T.takeWhile (/= '#')) outs3
            @?= [ "updated data orbital.Body"
                , "left orbital.earth on "
                , "left orbital.weight on "
                ]
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
    , testCase "(j) :edit std includes the library; :edit alone never touches it" $ do
        s <- editSession
        file <- editFileOf s ["std"]
        ("unit km = 10^3 * m" `T.isInfixOf` file) @? "std.km is in the file"
        file' <- replaceOnce "unit km = 10^3 * m\n" "unit km = 1001 * m\n" file
        (s', outs) <- edited (EditNamespace "std") file' s
        -- The library's own users are in the file; the user's are propagated.
        outs
          @?= [ T.replace "std.km" "km" (movedLine "updated" s s' "std.km")
              , movedLine "upgraded" s s' "trip"
              , movedLine "upgraded" s s' "orbital.earth"
              ]
        snd <$> feed s' "trip to m" @?= Right ["2002 m"]
        -- The codebase without std: nothing under std is removed.
        plain <- editFileOf s []
        ("unit km" `T.isInfixOf` plain) @?= False
        changed <- replaceOnce "let size = 10\n" "let size = 11\n" plain
        (s2, _) <- edited EditCodebase changed s
        let underStd c = Map.filterWithKey (\k _ -> "std." `T.isPrefixOf` k) c.names
        underStd s2.codebase @?= underStd s.codebase
    , testCase "(k) :edit --file resumes from a file" $ do
        s <- editSession
        dir <- getTemporaryDirectory
        let path = dir </> "eval-edit-test.ev"
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

-- The standard library (design §7.7) -------------------------------------------------

{- | The library as the old root prelude entered it, before it moved under
std: the statements of 'preludeSource' at the root, added.
-}
legacyPrelude :: Session
legacyPrelude =
  either (error . T.unpack) id $ do
    (s, _) <- feed emptySession preludeSource
    (s', _) <- feed s ":add"
    pure s'

stdlibTests :: TestTree
stdlibTests =
  testGroup
    "standard library"
    [ testCase "the move under std keeps the hash of every definition without a ±" $ do
        -- Printed by `:hash km` and `:hash map` in a prelude session at 21cb8e8,
        -- before the library moved under std.
        runLinesP [":hash std.km", ":hash std.map"] @?= Right ["#90tke", "#v2enr.0"]
        let old n = lookupName n legacyPrelude.codebase
            new n = lookupName ("std." <> n) seeded.codebase
        old "km" @?= new "km"
        old "map" @?= new "map"
        old "degC" @?= new "degC"
        isJust (new "km") @? "std.km"
        -- Every library name but the ± ones and what uses them keeps its hash.
        [ n
          | n <- Map.keys legacyPrelude.codebase.names
          , old n /= new n
          ]
          @?= ["G", "M_earth", "M_sun"]
    , testCase "a ± definition is stamped with its full path: std.G is not a root G" $ do
        -- `:hash G` printed #e1bms at 21cb8e8, when the prelude's G was at the root.
        expecting (runLinesP [":hash G", ":hash std.G"]) $ \case
          [g, stdG] -> do
            g @?= stdG
            (g /= "#e1bms") @? "std.G has a new hash"
          outs -> assertFailure (show outs)
        expecting
          ( runLinesP
              [ ":unuse std"
              , "let G = (6.67430e-11 ±σ 1.5e-15) * m^3 / (kg * s^2)"
              , ":add"
              , ":hash G"
              , ":hash std.G"
              ]
          )
          $ \outs -> case lastN 2 outs of
            [g, stdG] -> do
              -- The root G has the hash the root prelude's G had.
              g @?= "#e1bms"
              (stdG /= g) @? "std.G differs from the root G"
            other -> assertFailure (show other)
    , testCase "units resolve through the stored use std and print bare" $ do
        evalP "5 km" @?= Right ["5 km"]
        runLinesP ["5 std.km", "1 km to m", "3 degC"]
          @?= Right ["5 km", "1000 m", "3 degC"]
        runLinesP [":type std.G"] @?= Right ["Num [m^3 kg^-1 s^-2]"]
    , testCase ":ls alone shows the root and one line for std; :ls std the library" $ do
        runLinesP [":ls"]
          @?= Right ["namespace std (" <> T.pack (show (length stdlibNames)) <> " names)"]
        -- :ls lists a type and its constructor on two lines and no fields:
        -- std.Cov2 is one label and two lines, its three fields none.
        let listed = length stdlibNames + 1 - 3
        expecting (runLinesP [":ls std"]) $ \outs -> do
          length outs @?= listed
          ("unit km : Num [m]" `elem` outs) @? "km"
          ("scale degC : Scale [K]" `elem` outs) @? "degC"
        expecting (runLinesP [":ls --all"]) $ \outs -> do
          ("unit std.km : Num [m]" `elem` outs) @? "full paths with --all"
          length outs @?= listed
        runLinesP [":ls --units furl"] @?= Right ["nothing matches"]
    , testCase "a root name shadows the library's: c and std.c" $ do
        runLinesP ["let c = 3e8 m/s", "c", "std.c", ":add", "c", "std.c"]
          @?= Right
            [ "300000000 m s^-1"
            , "299792458 m s^-1"
            , "added c"
            , "300000000 m s^-1"
            , "299792458 m s^-1"
            ]
        expecting
          (runLinesP ["let c = 3e8 m/s", "let x = c + std.c", ":add", ":view x"])
          $ \outs ->
            last outs @?= "x = c + std.c"
    , testCase "library names are names: :rename, :unname, :edit" $ do
        runLinesP [":rename std.h std.hour", "3 hour", "2 hour + 30 min"]
          @?= Right ["renamed `std.h` to `std.hour`", "3 hour", "150 min"]
        expectError (runLinesP [":rename std.h std.hour", "3 h"]) "unknown name `h`"
        expectError (runLinesP [":unname std.AU", "1 AU"]) "unknown name `AU`"
        runLinesP [":edit std.km"] @?= Right ["namespace std", "  unit km = 10^3 * m"]
    , testCase ":uses, :unuse and :use for the stored use std" $ do
        runLinesP [":uses"] @?= Right ["use std (stored)"]
        runLinesP [":unuse std", ":uses"]
          @?= Right ["removed the stored use std; :use std puts it back", "no uses"]
        expectError (runLinesP [":unuse std", "5 km"]) "unknown name `km`"
        runLinesP [":unuse std", "5 std.km", ":use std", "5 km", ":uses"]
          @?= Right
            [ "removed the stored use std; :use std puts it back"
            , "5 std.km"
            , "stored use std"
            , "5 km"
            , "use std (stored)"
            ]
        expectError (runLinesP [":use std"]) "use std is already stored"
        -- A session use and a stored one of the same path: the stored goes first.
        runLinesP ["use std", ":uses", ":unuse std", ":uses", ":unuse std", ":uses"]
          @?= Right
            [ "use std (stored)"
            , "use std"
            , "removed the stored use std; :use std puts it back"
            , "use std"
            , "no uses"
            ]
        -- The scratch must still check without it.
        expectError
          (runLinesP ["let d = 2 km", ":unuse std"])
          "the pending definitions would not check"
    , testCase ":stdlib upgrade: up to date, added, updated, kept" $ do
        runLinesP [":stdlib upgrade"] @?= Right ["the library is up to date"]
        lib <- either (assertFailure . T.unpack) pure stdlibCodebase
        -- An older library: G as a plain number, c the user rebinds, AU absent.
        old <-
          either
            (assertFailure . T.unpack)
            pure
            ( sessionWith
                emptySession
                [ multiline ["namespace std", "  let G = 1", "  let c = 2", "  let gone = 3"]
                , ":add"
                , multiline ["namespace std", "  let c = 5"]
                , "let twice = std.G * 2"
                , ":update"
                ]
            )
        case stdlibUpgrade lib [] old of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added std.km" `elem` outs) @? "km added"
            any ("updated std.G " `T.isPrefixOf`) outs @? "G updated"
            ("kept std.c (yours)" `elem` outs) @? "c kept"
            any ("upgraded twice " `T.isPrefixOf`) outs @? "twice upgraded"
            linesIn' s ["std.c", "std.gone", "twice", "1 std.km"]
              @?= Right ["5", "3", "1.33486e-10 ±σ 3e-15 m^3 kg^-1 s^-2", "1 std.km"]
            -- A library type comes with its constructor and field labels.
            ("added data std.Cov2" `elem` outs) @? "Cov2 added"
            ("added std.jointCovariance" `elem` outs) @? "jointCovariance added"
            linesIn'
              s
              -- A field is found through a use, as a bare name is.
              [":use std", "(jointCovariance ([1, 2] m ±σ 1 m, [3, 4] m ±σ 1 m)).rv"]
              @?= Right ["stored use std", "[0, 0; 0, 0] m^2"]
        -- A type label the codebase has is left alone.
        old2 <-
          either
            (assertFailure . T.unpack)
            pure
            ( sessionWith
                emptySession
                [multiline ["namespace std", "  data Cov2 = Cov2"], ":add"]
            )
        case stdlibUpgrade lib [] old2 of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added data std.Cov2" `notElem` outs) @? "Cov2 kept"
            lookupTypeName "std.Cov2" s.codebase @?= lookupTypeName "std.Cov2" old2.codebase
    , testCase
        ":rename and :move re-hash a stamped definition and upgrade its dependents"
        $ do
          let hashOf ls n = fmap last (runLinesP (ls ++ [":hash " <> n]))
          -- A plain definition keeps its hash; a ± one takes its new path's.
          expecting (runLinesP ["let q = 1", ":add", ":rename q r"]) $ \outs ->
            last outs @?= "renamed `q` to `r`"
          expecting
            ( runLinesP
                ["let a = 1 ± 0.1", "let b = a * 2", ":add", ":rename a c", "b", ":todo"]
            )
            $ \outs -> do
              case drop 2 outs of
                renamed : rehashed : upgraded : rest -> do
                  renamed @?= "renamed `a` to `c`"
                  ("re-hashed c #" `T.isPrefixOf` rehashed) @? T.unpack rehashed
                  ("upgraded b #" `T.isPrefixOf` upgraded) @? T.unpack upgraded
                  rest @?= ["2.0 ± 0.2", "nothing to do"]
                other -> assertFailure (show other)
          hashOf ["let a = 1 ± 0.1", ":add", ":rename a c"] "c"
            @?= hashOf ["let c = 1 ± 0.1", ":add"] "c"
          -- A namespace moved: each stamped member re-hashed, as if entered there.
          let lab = [multiline ["namespace lab", "  let x = 1 ± 0.1", "  let y = x + 1"], ":add"]
          expecting (runLinesP (lab ++ [":rename lab field"])) $ \outs ->
            map (T.takeWhile (/= '#')) (lastN 3 outs)
              @?= [ "renamed the 2 labels under `lab` to `field`"
                  , "re-hashed field.x "
                  , "re-hashed field.y "
                  ]
          hashOf (lab ++ [":move lab.x field"]) "field.x"
            @?= hashOf [multiline ["namespace field", "  let x = 1 ± 0.1"], ":add"] "field.x"
          -- The library's G: its dependents follow it.
          expecting (runLinesP [":rename std.G std.Gn", ":todo"]) $ \outs ->
            map (T.unwords . take 2 . T.words) outs
              @?= [ "renamed `std.G`"
                  , "re-hashed Gn"
                  , "upgraded M_earth"
                  , "upgraded M_sun"
                  , "nothing to"
                  ]
    , testCase
        ":rename of a nominal type re-hashes it, its users and the types that use it"
        $ do
          let shapes =
                [ "data Shape = Circle (Num [m]) | Square (Num [m])"
                , "data Wrap = Wrap Shape"
                , "let size s = case s of Circle r -> r; Square a -> a"
                , "let one = Wrap (Circle (1 m))"
                , ":add"
                ]
          expecting
            ( runLinesP
                ( shapes
                    ++ [":rename Shape Form", "size (Square (2 m))", "one", ":view Wrap", ":todo"]
                )
            )
            $ \outs -> do
              let report = takeWhile (/= "2 m") (dropWhile (not . ("renamed" `T.isPrefixOf`)) outs)
              take 1 report @?= ["renamed `Shape` to `Form`"]
              sort (map (T.unwords . take 2 . T.words) (drop 1 report))
                @?= ["re-hashed data", "re-hashed data", "upgraded one", "upgraded size"]
              lastN 3 outs
                @?= ["Wrap (Circle (1 m))", "data Wrap = Wrap Form", "nothing to do"]
          -- The type now has the hash a fresh declaration under the new name has.
          let typeHash ls n = do
                s <- sessionP ls
                pure (lookupTypeName n s.codebase)
          typeHash (shapes ++ [":rename Shape Form"]) "Form"
            @?= typeHash ["data Form = Circle (Num [m]) | Square (Num [m])", ":add"] "Form"
    ]
 where
  linesIn' s0 = go s0 []
   where
    go _ acc [] = Right (concat (reverse acc))
    go s acc (l : rest) = do
      (s', outs) <- feed s l
      go s' (outs : acc) rest
  sessionWith s0 = \case
    [] -> Right s0
    l : ls -> feed s0 l >>= \(s', _) -> sessionWith s' ls
