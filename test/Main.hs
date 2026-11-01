module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM_)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Support.Render (render)

import Astro (astroTests)
import Backend (backendTests)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Ratio (denominator, numerator)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Text.IO qualified as TIO
import Data.Time.Clock.POSIX (getPOSIXTime)
import Gen (exprDepth, genProgram, instanceOf)
import Limits (limitTests, measure)
import Metron.Affine hiding (Builtin, DivideByZero)
import Metron.Affine qualified as A
import Metron.Builtin
import Metron.Codebase (
  Codebase (..),
  emptyCodebase,
  lookupConName,
  lookupName,
  lookupTypeName,
  showReference,
 )
import Metron.Core
import Metron.Desugar
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
import Metron.Dimension qualified as Dimension
import Metron.Driver
import Metron.Eval
import Metron.Hash
import Metron.Infer (
  TypeError (..),
  elaborateClosed,
 )
import Metron.Lexer hiding (TNum, TProj)
import Metron.Lexer qualified as L
import Metron.Limits (defaultLimits, newBudget, settingLines)
import Metron.NameResolution (LabelKind (..), Qualified (..), qualifyName)
import Metron.Numerical.Approx (isqrt)
import Metron.Parser
import Metron.Prelude (
  isLibraryPath,
  stdlibCodebase,
  stdlibDefaultUses,
  stdlibNames,
  stdlibNamespaces,
 )
import Metron.Pretty
import Metron.Primitive.Types
import Metron.Repl qualified as R
import Metron.Store
import Metron.Syntax qualified as S
import Metron.TCore
import Metron.Type
import Metron.Type.Match
import Metron.Type.Syntax (queryScheme)
import Metron.Unicode qualified as U
import Precision (precisionTests)
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

{- | Every test has a five-minute limit as a backstop to 'caseLimit', which
times each generated case but not the generator itself: the whole suite
normally runs in seconds, so a test that reaches it has hung. What the
limits tests measure of the heap runs first, on the main thread ("Limits").
-}
main :: IO ()
main = do
  measured <- measure
  defaultMain
    . localOption (mkTimeout 300_000_000)
    $ testGroup
      "metron"
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
      , rotationTests
      , turnedChartTests
      , movingChartTests
      , axisSlotTests
      , namedAxesTests
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
      , backendTests
      , namespaceTests
      , editTests
      , stdlibTests
      , limitTests measured
      , annotationTests
      , forallTests
      , dimensionSyntaxTests
      , readingTests
      , partUTests
      , partFTests
      , roleTests
      , astroTests
      , precisionTests
      ]

-- Term-building helpers -------------------------------------------------

num :: Rational -> Term n
num r = Lit (LTensor ([], [r]))

bool :: Bool -> Term n
bool b = Con (boolC b) []

-- | An if, as the desugarer writes it: a case on Bool in canonical order.
ifT :: Term n -> Term n -> Term n -> Term n
ifT c t e = Case c [Alt FalseC VNil e, Alt TrueC VNil t]

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
          ( Runtime
              typedOf
              (\_ _ _ -> Nothing)
              (\_ _ _ -> Nothing)
              (const Nothing)
              (const Nothing)
              (newBudget defaultLimits typed)
          )
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
    "metron"
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
  S.Ascribe a _ -> shape a
  S.ChartForm cl ->
    foldl
      (\acc x -> A acc (shape x))
      (shape cl.parent)
      (catMaybes [cl.origin, cl.step, cl.generators, cl.spin])
  S.FromTo v c c1 -> A (A (shape v) (shape c)) (shape c1)
  S.UnitBody a -> shape a
  S.UnitSyntax a -> shape a

parserTests :: TestTree
parserTests =
  testGroup
    "parser"
    [ testCase "precedence: * over +"
        $ parseShape "1 + 2 * 3" @?= Right (O S.Add (N 1) (O S.Outer (N 2) (N 3)))
    , testCase "left associativity of -"
        $ parseShape "10 - 3 - 2" @?= Right (O S.Sub (O S.Sub (N 10) (N 3)) (N 2))
    , testCase "conversions chain from the left: x to a to b is (x to a) to b" $ do
        parseShape "x to a to b" @?= Right (O S.To (O S.To (V "x") (V "a")) (V "b"))
        parseShape "x to a to b to c"
          @?= Right (O S.To (O S.To (O S.To (V "x") (V "a")) (V "b")) (V "c"))
        parseShape "x + 1 to a to b"
          @?= Right (O S.To (O S.To (O S.Add (V "x") (N 1)) (V "a")) (V "b"))
        -- After a conversion from a configuration, or a subtraction in a frame.
        parseShape "v from c to c1 to km"
          @?= Right (O S.To (A (A (V "v") (V "c")) (V "c1")) (V "km"))
        parseShape "b .- a on c to km"
          @?= Right (O S.To (O S.On (O S.PSub (V "b") (V "a")) (V "c")) (V "km"))
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
                  then Just (ATerm (Resolution (h "kay", Nothing) False False False))
                  else Nothing
           in case parseExpr "k + 1"
                >>= either (Left . renderDesugarError) Right . desugarClosed resolver of
                Right (t, _) ->
                  assertBool (show t) (alphaEq t (Ref (h "kay") Nothing "" +. num 1 :: Term Z))
                Left err -> assertFailure (T.unpack err)
    , testCase "codebase names shadow primitives"
        $ let resolver n =
                if n == "sqrt"
                  then Just (ATerm (Resolution (h "mine", Nothing) False False False))
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
        refused "noise 18446744073709551616"
        refused "[1, 2].18446744073709551616"
        refused "contract 0 18446744073709551616 [1, 2; 3, 4]"
        refused "slice 0 18446744073709551616 [1, 2; 3, 4]"
        refused "f :: Vec 18446744073709551616 -> Num\nlet f v = 1"
        refused "g :: forall (a : 18446744073709551616). Vec a -> Vec a\nlet g v = v"
    , testCase "a tensor past the components limit is refused when built" $ do
        let refused src = case evalText src of
              Left err ->
                T.isInfixOf "more than 10000000 (`:set components`)" err @? T.unpack err
              Right out -> assertFailure (show out)
        refused "gauss 10000001"
        -- a product of tensors each within the limit can exceed it
        refused "let v = noise 4000 in outer v v"
        refused "let v = noise 4000 in wedge v v"
        refused "let v = noise 4000 in dot (outer v [1]) (outer [1] v)"
        evalText "let v = noise 3000 in (outer v v).1.2" @?= Right ["0 ± 1"]
        -- the limit is a setting, and a stack of tensors counts too
        case runLines [":set components 100", "noise 101"] of
          Left err -> T.isInfixOf "101 components, more than 100" err @? T.unpack err
          Right out -> assertFailure (show out)
        case runLines [":set components 100", "[noise 50, noise 50, noise 50]"] of
          Left err -> T.isInfixOf "150 components, more than 100" err @? T.unpack err
          Right out -> assertFailure (show out)
        runLines
          [ ":set components 100"
          , "(noise 100).99"
          , ":set components 150"
          , "(noise 101).100"
          ]
          @?= Right ["0 ± 1", "0 ± 1"]
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
          evalText "vmap (\\x -> x * m) (noise 0)" @?= Right ["[] m"]
          evalText "let e = vmap (\\x -> x * m) (noise 0) in dot e e" @?= Right ["0 m^2"]
          evalText "vzipWith (\\a b -> a * b) ([] :: Vec 0 m) ([] :: Vec 0 s)"
            @?= Right ["[] m s"]
          evalText "timap (\\i x -> x * m) (noise 0)" @?= Right ["[] m"]
          -- inside a polymorphic function, the caller's dimension
          runLines
            [ "let f g xs = vmap g xs"
            , "dot (f (\\x -> x * m) (noise 0)) (f (\\x -> x * s) (noise 0))"
            ]
            @?= Right ["0 m s"]
          runLines ["let h v = vmap (\\x -> x * 1 kg) v", "h (noise 0)"]
            @?= Right ["[] kg"]
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

{- | An expression that is @true@ when every component of the dimensionless
tensor @e@ encloses the matching component of @t@ (@|mid d| ≤ bound d@ for
@d = e − t@) with a bound of at most @tol@.
-}
encloses :: Text -> Text -> Text -> Text
encloses tol e t =
  "let d = ("
    <> e
    <> ") - ("
    <> t
    <> ") in vmap (\\x -> if abs (mid x) <= bound x && bound x <= "
    <> tol
    <> " then 0 else 1) d == vmap (\\x -> 0) d"

{- | Design §3.8: charts turned from their parent. Rotations are enclosures,
so a conversion is checked with 'encloses' on the amount from a fixed
point, divided by its unit, and never with @==@.
-}
turnedChartTests :: TestTree
turnedChartTests =
  testGroup
    "turnedCharts"
    [ testCase "one level: lvlh's x axis is eci's y, and back" $ do
        runLinesP
          ( frame
              ++ [ encloses "1e-20" (fromEci "[1, 0, 0] lvlh") "[7000000, 1, 0]"
                 , -- reading back, by the generator negated
                   encloses
                     "1e-20"
                     "transformBy (expm (-(rotz (90 deg)))) (([7000000, 1, 0] eci .- ([0, 0, 0] lvlh to eci)) / 1 m)"
                     "[1, 0, 0]"
                 , "[1, 0, 0] lvlh to eci"
                 , "[7000000, 1, 0] eci to lvlh"
                 , "[0, 0, 0] lvlh"
                 ]
          )
          @?= Right
            [ "true"
            , "true"
            , "[7000000.0000000000000…, 1.0000000000000000000…, 0] eci"
            , "[1.0000000000000000000…, 3.0e-24 ± 3.8e-24, 0] lvlh"
            , "[0, 0, 0] lvlh"
            ]
    , testCase
        "two levels: the rotations compose in order, the origin turns with the parent"
        $ do
          -- arm is turned from lvlh by rotx (90 deg), its origin [0, 2, 5] m
          -- along lvlh's axes. By hand: R = Rz(90) Rx(90) = [0, 0, 1; 1, 0, 0;
          -- 0, 1, 0], the origin [7000000, 0, 0] + Rz(90) [0, 2, 5] =
          -- [6999998, 0, 5], so [1, 2, 3] arm is [6999998, 0, 5] + [3, 1, 2].
          -- The product reversed would give [-2, -3, 1] for R [1, 2, 3], and
          -- the origin not turned [7000000, 2, 5].
          let arm = frame ++ ["chart arm on lvlh at [0, 2, 5] m by rotx (90 deg)"]
          runLinesP
            ( arm
                ++ [ encloses "1e-20" (fromEci "[1, 2, 3] arm") "[7000001, 1, 7]"
                   , encloses "1e-20" (fromEci "[0, 0, 0] arm") "[6999998, 0, 5]"
                   , encloses "1e-20" "rotationOf arm" "[0, 0, 1; 1, 0, 0; 0, 1, 0]"
                   , encloses
                       "1e-20"
                       "transformBy (expm (-(rotx (90 deg))) @ expm (-(rotz (90 deg)))) (([7000001, 1, 7] eci .- ([0, 0, 0] arm to eci)) / 1 m)"
                       "[1, 2, 3]"
                   , "[7000001, 1, 7] eci to arm"
                   ]
            )
            @?= Right
              [ "true"
              , "true"
              , "true"
              , "true"
              , "[1.0000000000000000000…, 1.9999999999999999999…, 3.0000000000000000000…] arm"
              ]
    , testCase
        "an origin is an amount along the parent's axes, not steps of the parent"
        $ do
          runLinesP
            [ eci
            , "chart kmc on eci step km"
            , "chart sub on kmc at [1, 0, 0] km step m"
            , "[0, 0, 0] sub to eci"
            , "chart kmt on eci step km by rotz (90 deg)"
            , "chart subt on kmt at [1, 0, 0] km step m"
            , encloses "1e-20" (fromEci "[0, 0, 0] subt") "[0, 1000, 0]"
            , -- a chart under a turned one, not turned itself, has its parent's axes
              encloses "1e-20" (fromEci "[1, 0, 0] subt") "[0, 1001, 0]"
            ]
            @?= Right ["[1000, 0, 0] eci", "true", "true"]
    , testCase "a sequence with then is the Euler product, applied in order" $ do
        let pf =
              [eci, "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"]
        runLinesP
          ( pf
              ++ [ -- rows along eci and columns along pf, against a rotation
                   -- along one axis set: Rᵀ E is the identity
                   encloses
                     "1e-20"
                     "transpose (rotationOf pf) @ euler313 (30 deg) (45 deg) (60 deg)"
                     "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
                 , encloses
                     "1e-20"
                     (fromEci "[1, 2, 3] pf")
                     "euler313 (30 deg) (45 deg) (60 deg) @ [1, 2, 3]"
                 ]
          )
          @?= Right ["true", "true"]
    , testCase "displacements within a frame are along its axes, exactly" $ do
        runLinesP
          ( frame
              ++ [ -- chart coordinates (design §3.10, F6): no rotation applies
                   "[1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , ":type [1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , -- re-expressed along eci's axes, the rotated difference
                   encloses
                     "1e-20"
                     "(([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci) / 1 m"
                     "expm (rotz (90 deg)) @ [1, -3, 3]"
                 , encloses
                     "1e-20"
                     "(([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci) / 1 m"
                     "[3, 1, 3]"
                 , -- q .+ (p .- q) is p, in one frame
                   "([4, 5, 6] lvlh .+ ([1, 2, 3] lvlh .- [4, 5, 6] lvlh)) == [1, 2, 3] lvlh"
                 , "let p = [1, 2, 3] eci"
                 , "let q = [7, 8, 9] eci"
                 , -- the difference re-expressed equals the difference of the
                   -- points re-expressed (design §3.10, F7)
                   encloses
                     "1e-20"
                     "(((p to lvlh) .- (q to lvlh)) - ((p .- q) to lvlh)) / 1 m"
                     "[0, 0, 0]"
                 , encloses
                     "1e-20"
                     "((p .- q on lvlh) - ((p .- q) to lvlh)) / 1 m"
                     "[0, 0, 0]"
                 , -- an amount along a chart's axes reaches the base's with from
                   encloses
                     "1e-20"
                     "(([1, 0, 0] m from lvlh to eci) - (([1, 0, 0] lvlh to eci) .- ([0, 0, 0] lvlh to eci))) / 1 m"
                     "[0, 0, 0]"
                 ]
          )
          @?= Right
            [ "[1, -3, 3] m"
            , "Vec lvlh m"
            , "true"
            , "true"
            , "true"
            , "true"
            , "true"
            , "true"
            ]
        -- Two frames' amounts do not mix unconverted.
        expectError
          ( runLinesP
              ( frame
                  ++ ["([1, 2, 3] lvlh .- [0, 0, 0] lvlh) + ([1, 2, 3] eci .- [0, 0, 0] eci)"]
              )
          )
          "the axes of lvlh against the axes of GCRS"
    , testCase "a covariance and a Cov2 block through rotateCov are R P Rᵀ" $ do
        let pm = "[[4, 1, 0], [1, 9, 0], [0, 0, 1]]"
        typeOfTextP "rotateCov"
          @?= Right "forall n m d d1. Mat n m d -> Mat m m d1 -> Mat n n (d^2*d1)"
        typeOfTextP "rotateVec"
          @?= Right
            "forall n m d s d1. Mat n m d -> Tensor (m : s) d1 -> Tensor (n : s) (d*d1)"
        runLinesP
          ( frame
              ++ [ encloses
                     "1e-20"
                     ("rotateCov (rotationOf lvlh) " <> pm)
                     ("rotationOf lvlh @ " <> pm <> " @ transpose (rotationOf lvlh)")
                 , encloses
                     "1e-20"
                     ("rotateCov (rotationOf lvlh) " <> pm)
                     "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , -- an unturned chart's is exactly the identity
                   "rotateCov (rotationOf eci) " <> pm <> " == " <> pm
                 , "blk :: Cov2 lvlh m (m/s)\nlet blk = Cov2 {rr = "
                     <> pm
                     <> " * 1 m^2, rv = "
                     <> pm
                     <> " * 1 m^2/s, vv = 2 * "
                     <> pm
                     <> " * (1 m/s)^2}"
                 , "let turned = inChartCov2 lvlh blk"
                 , encloses "1e-20" "turned.rr / 1 m^2" "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , encloses "1e-20" "turned.rv / (1 m^2/s)" "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 , encloses
                     "1e-20"
                     "turned.vv / (1 m/s)^2"
                     "2 * [[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
                 ]
          )
          @?= Right ["true", "true", "true", "true", "true", "true"]
    , testCase "an uncertain angle: the coordinates carry it, correlated" $ do
        runLinesP
          [ eci
          , "chart tilt on eci by rotz (30 deg ± 0.001 rad)"
          , "let v = (([1000, 0, 0] tilt to eci) .- [0, 0, 0] eci) / 1 m"
          , -- x = 1000 cos θ, y = 1000 sin θ: bounds near 0.5 and 0.87
            "bound v.0 > 0.4 && bound v.0 < 0.6"
          , "bound v.1 > 0.8 && bound v.1 < 0.95"
          , -- the norm is 1000 whatever the angle: the first-order terms cancel
            "bound (norm v) < bound v.0 / 100"
          , "abs (mid (norm v) - 1000) < 1e-3"
          , -- on its own frame the point is exact
            "[1000, 0, 0] tilt .- [0, 0, 0] tilt"
          ]
          @?= Right ["true", "true", "true", "true", "[1000, 0, 0] m"]
    , testCase "a chart used in 100 conversions computes its rotation once" $ do
        -- Each mention of lvlh shares one value, and so one rotation.
        runLinesP
          ( frame
              ++ [ encloses
                     "1e-15"
                     "foldl (\\acc k -> acc + (([k, 0, 0] lvlh to eci) .- ([0, 0, 0] lvlh to eci)).1 / 1 m) 0 (range 1 100)"
                     "5050"
                 ]
          )
          @?= Right ["true"]
    , testCase ":view and :edit of a sequence read back to the same hash" $ do
        let pf = "chart pf on eci at [0, 2, 0] km by rotz (30 deg) then rotx (45 deg)"
        runLinesP [eci, pf, ":view pf"] @?= Right [pf]
        let hashAfter def = runLinesP [eci, def, ":hash pf"]
        expecting (runLinesP [eci, pf, ":edit pf"]) $ \outs ->
          hashAfter (T.strip (last outs)) @?= hashAfter pf
    , testCase "design §12: a perifocal chart" $ do
        runLinesP perifocalSession
          @?= Right
            [ "chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
            , "[887785.38831025442775…, 5462310.6012293745031…, 4286607.0498705616718…] eci"
            , "[6999.9999999999999999…, -1.3e-20 ± 8.9e-20, 6e-21 ± 2.4e-20] pf"
            , "[-6.9508252147247766082…, -0.95119863033241545830…, 2.6516504294495532165…] km s^-1"
            , "[4.5767451288348659649…, -1.3794313182928119555…, 1.0170048711651340350…; -1.3794313182928119555…, 4.0482548711651340350…, -3.5986214154904359879…; 1.0170048711651340350…, -3.5986214154904359879…, 5.3749999999999999999…] km^2"
            , "7000 km"
            ]
    , testCase "a sequence-turned chart survives a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ eci
            , "chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"
            , "chart pf on lvlh by rotz (30 deg) then rotx (45 deg)"
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.names @?= s.codebase.names
        loaded.codebase.charts @?= s.codebase.charts
        linesIn loaded [":view pf", ":hash pf"]
          @?= linesIn s [":view pf", ":hash pf"]
        linesIn loaded ["[1, 2, 3] pf to eci"] @?= linesIn s ["[1, 2, 3] pf to eci"]
    ]
 where
  eci = multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
  frame = [eci, "chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"]
  fromEci p = "(((" <> p <> ") to eci) .- [0, 0, 0] eci) / 1 m"

{- | The session of design §12, "A perifocal chart": a chart turned by the
3-1-3 sequence of an orbit's elements, a point on it, and a velocity and a
covariance given along its axes.
-}
perifocalSession :: [Text]
perifocalSession =
  [ "space GCRS = Vec 3 m"
  , "chart eci on GCRS"
  , "chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
  , ":view pf"
  , "let rp = [7000, 0, 0] pf"
  , "rp to eci"
  , "(rp to eci) to pf"
  , "let vp = [0, 7.5, 0] km/s from pf to eci"
  , "vp to km/s"
  , "rotateCov (rotationOf pf) ([[1, 0, 0], [0, 4, 0], [0, 0, 9]] km^2) to km^2"
  , "rp.0"
  ]

{- | Design §3.8: moving charts. A chart declared with parameters is a
function to a chart, applied at a time; a spinning chart carries its
angular velocity, and the kinematics compose through the tree. The physics
is checked against hand formulas (sines and cosines, not @expm@), against
a finite difference of positions, and by the transport law that a body
fixed on a chart is at rest relative to it.
-}
movingChartTests :: TestTree
movingChartTests =
  testGroup
    "movingCharts"
    [ testCase
        "a moving chart declares, prints with its parameter and spin, and applies"
        $ do
          runLinesP
            ( spinning
                ++ [ ":view spinner"
                   , ":type spinner"
                   , "[7000000, 0, 0] eci to spinner t1"
                   , "[7000000, 0, 0] eci to (spinner t1)"
                   , "spinner t1"
                   ]
            )
            @?= Right
              [ "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
              , "Point unix -> Chart spinner"
              , "[6981397.0116296611947…, -509995.84901098588542…, 0] (spinner (1000 unix))"
              , "[6981397.0116296611947…, -509995.84901098588542…, 0] (spinner (1000 unix))"
              , "chart (spinner (1000 unix))"
              ]
          -- what an instant prints reads back: one frame, one point
          runLinesP
            (spinning ++ ["[1, 2, 3] (spinner (1000 unix)) == [1, 2, 3] (spinner t1)"])
            @?= Right ["true"]
          -- a spin with no `by`: the generators are an empty list, and no `by` prints
          runLinesP
            ( spinning
                ++ [ "chart carousel t on (spinner t) at [10, 0, 0] m spinning [0, 0, 2] * w"
                   , ":view carousel"
                   ]
            )
            @?= Right
              ["chart carousel t on (spinner t) at [10, 0, 0] m spinning [0, 0, 2] * w"]
    , testCase ":edit reads a moving chart back to the same hash" $ do
        let hashAfter def = runLinesP (take 4 spinning ++ [def, ":hash spinner"])
        expecting (runLinesP (spinning ++ [":edit spinner"])) $ \outs ->
          hashAfter (T.strip (last outs)) @?= hashAfter (spinning !! 4)
    , testCase
        "a moving chart without its arguments is refused, as a point's chart, a target or a parent"
        $ do
          expectError
            (runLinesP (spinning ++ ["[1, 2, 3] eci to spinner"]))
            "`spinner` takes arguments: apply it, as in p to (spinner t0)"
          expectError
            (runLinesP (spinning ++ ["[1, 2, 3] spinner"]))
            "`spinner` takes arguments: a point is written on an applied chart, as in [1, 2, 3] (spinner t0)"
          expectError
            (runLinesP (spinning ++ ["chart arm t on spinner at [1, 0, 0] m"]))
            "`spinner` takes arguments: apply it, as in chart arm t on (spinner t) at [1, 0, 0] m"
          -- A point on it converts from a configuration named with `from`
          -- (design §3.10, F7), never the one it was written on.
          expectError
            (runLinesP (spinning ++ ["let p = [1, 2, 3] (spinner t1)", "p to eci"]))
            "spinner takes arguments: write p from (spinner …) to eci"
          -- the spin is an angular velocity: rad s^-1, not s^-1
          expectError
            ( runLinesP
                (spinning ++ ["chart bad on eci spinning [0, 0, 1] / 1 s"])
            )
            "rad"
    , testCase "a body fixed on a spinning chart: at rest on it, ω × r in the parent" $ do
        runLinesP
          ( spinning
              ++ [ ":use astro"
                 , "let c = spinner t1"
                 , "let p = [7000000, 0, 0] (spinner t1)"
                 , "let pe = (p from c to eci) .- [0, 0, 0] eci"
                 , "let wv = withAxes eci ([0, 0, 1] * (w / 1 rad))"
                 , -- the inertial velocity of a point turning with the chart
                   "let body = State {epoch = t1, pos = pe, vel = wv × pe}"
                 , encloses "1e-15" "velocityIn c body / (1 m/s)" "[0, 0, 0]"
                 , -- written back: ω × r along the parent's axes, by hand,
                   -- r = 7000 km at θ = w (t1 − t0)
                   encloses
                     "1e-15"
                     "(stateFrom c t1 ([7000000, 0, 0] m) ([0, 0, 0] m/s)).vel / (1 m/s)"
                     "7000000 * (w * 1 s / rad) * [-sin (w * 1000 s), cos (w * 1000 s), 0]"
                 , -- a body at rest in the parent turns backwards on the chart
                   encloses
                     "1e-15"
                     "velocityIn c (State {epoch = t1, pos = pe, vel = [0, 0, 0] m/s}) / (1 m/s)"
                     "[0, -7000000 * (w * 1 s / rad), 0]"
                 ]
          )
          @?= Right ["stored use astro", "true", "true", "true"]
    , testCase
        "stateFrom then velocityIn and the position back on the chart are the round trip"
        $ do
          runLinesP
            ( spinning
                ++ [ ":use astro"
                   , "chart tilted t on (spinner t) at [100, -20, 30] km by rotx (30 deg) spinning [0.1, 0, 0] * w"
                   , "let c = tilted t1"
                   , "let pc = withAxes c ([7000, 100, -50] km)"
                   , "let vc = withAxes c ([1, 7.5, 0.2] km/s)"
                   , "let st = stateFrom c t1 pc vc"
                   , encloses "1e-15" "velocityIn c st / (1 m/s)" "vc / 1 (m/s)"
                   , encloses "1e-15" "((st.pos - originOf c) to c) / 1 m" "pc / 1 m"
                   , encloses
                       "1e-12"
                       "((([0, 0, 0] eci .+ st.pos) to tilted t1) .- [0, 0, 0] (tilted t1)) / 1 m"
                       "pc / 1 m"
                   ]
            )
            @?= Right ["stored use astro", "true", "true", "true"]
    , testCase
        "a declared spin agrees with the rotation it goes with: a finite difference"
        $ do
          -- A body fixed on the chart at t1 and t1 + 1 ms, compared with the
          -- velocity stateFrom gives it: the forward difference is off by
          -- about ω δt / 2 ≈ 3.6e-8 of the speed (the centripetal term). Its
          -- positions at two configurations are compared in the parent
          -- (design §3.10, F7), on one frame they would be one point.
          runLinesP
            ( spinning
                ++ [ ":use astro"
                   , "let pc = withAxes (spinner t1) [7000000, 2000, 300]"
                   , "let seen t = pointOn (spinner t) pc from (spinner t) to eci"
                   , "let fd = (seen (t1 .+ 1 ms) .- seen t1) / (1 ms)"
                   , "let v = (stateFrom (spinner t1) t1 (pc * 1 m) ([0, 0, 0] m/s)).vel"
                   , "let rel = norm (fd - v) / norm v"
                   , "mid rel < 1e-6 && mid rel > 1e-8"
                   , "rel"
                   , "pointOn (spinner (t1 .+ 1 ms)) pc .- pointOn (spinner t1) pc"
                   ]
            )
            @?= Right
              ["stored use astro", "true", "3.6460579499999992e-8 ± 3.5e-23", "[0, 0, 0] m"]
    , testCase
        "two levels: a station under a spinning Earth, a dish spinning on the station"
        $ do
          let station =
                spinning
                  ++ [ ":use astro"
                     , "chart station t on (spinner t) at [6378, 0, 0] km by roty (30 deg)"
                     , "let wv = withAxes eci ([0, 0, 1] * (w / 1 rad))"
                     , "let c = station t1"
                     ]
          runLinesP
            ( station
                ++ [ -- the station's own spin is none; it turns with the Earth
                     encloses "1e-25" "spinOf c * 1 s" "wv * 1 s"
                   , -- its origin moves with the Earth's frame: ω × (R_p a), by hand
                     encloses
                       "1e-12"
                       "originVelocityOf c / (1 m/s)"
                       "6378000 * (w * 1 s / rad) * [-sin (w * 1000 s), cos (w * 1000 s), 0]"
                   , -- a body fixed at the station is at rest relative to it
                     "let pe = ([1, 2, 3] (station t1) from c to eci) .- [0, 0, 0] eci"
                   , "let body = State {epoch = t1, pos = pe, vel = wv × pe}"
                   , encloses "1e-12" "velocityIn c body / (1 m/s)" "[0, 0, 0]"
                   ]
            )
            @?= Right ["stored use astro", "true", "true", "true"]
          -- A dish turning on the station, two spinning levels: the composed
          -- ω_abs = ω_p + R ω and the origin's transport agree with a
          -- central difference of positions. The dish's own turning adds
          -- 0.037 m/s to the Earth's 464 m/s; the difference is off by about
          -- (|ω| δt)² / 6 of each, under 1e-12 m/s, where a spin left out,
          -- turned the wrong way or not turned by R would be off by 0.01 m/s.
          -- (Checked by component: `norm` of so small an enclosure is slow.)
          runLinesP
            ( station
                ++ [ "chart dish t on (station t) at [0, 0, 10] m by rotz (0.01 rad/s * (t .- t0)) spinning [0, 0, 0.01] rad/s"
                   , "let pc = withAxes (dish t1) [3, 1, 2]"
                   , "let seen t = pointOn (dish t) pc from (dish t) to eci"
                   , "let fd = (seen (t1 .+ 1 ms) .- seen (t1 .+ -1 ms)) / (2 ms)"
                   , "let v = (stateFrom (dish t1) t1 (pc * 1 m) ([0, 0, 0] m/s)).vel"
                   , "vmap (\\x -> if abs (mid x) < 1e-11 then 0 else 1) ((fd - v) / (1 m/s)) == [0, 0, 0]"
                   , encloses
                       "1e-25"
                       "spinOf (dish t1) * 1 s"
                       "(wv + ([0, 0, 0.01] / 1 s from (dish t1) to eci)) * 1 s"
                   ]
            )
            @?= Right ["stored use astro", "true", "true"]
    , testCase "an uncertain spin rate gives a velocity whose bound grows with |r|" $ do
        runLinesP
          [ ":use astro"
          , "space GCRS = Vec 3 m"
          , "chart eci on GCRS"
          , "let wu = 7.2921159e-5 rad/s ± 1e-10 rad/s"
          , "let t0 = 0 unix"
          , "chart wobbly t on eci by rotz (wu * (t .- t0)) spinning [0, 0, 1] * wu"
          , "let v1 = (stateFrom (wobbly t0) t0 ([7000, 0, 0] km) ([0, 0, 0] m/s)).vel / (1 m/s)"
          , "let v2 = (stateFrom (wobbly t0) t0 ([14000, 0, 0] km) ([0, 0, 0] m/s)).vel / (1 m/s)"
          , -- 7000 km × 1e-10 s^-1 = 7e-4 m/s
            "bound v1.1 > 6.9e-4 && bound v1.1 < 7.1e-4"
          , "bound v2.1 / bound v1.1 > 1.99 && bound v2.1 / bound v1.1 < 2.01"
          ]
          @?= Right ["stored use astro", "true", "true"]
    , testCase "a moving chart survives a reload" $ withTempStore $ \dir -> do
        s <- persistLines dir (spinning ++ [":add"])
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.charts @?= s.codebase.charts
        let probe =
              [ ":view spinner"
              , ":hash spinner"
              , "[1, 2, 3] (spinner t1) from (spinner t1) to eci"
              , "[1, 2, 3] eci to spinner t1"
              ]
        linesIn loaded probe @?= linesIn s probe
        expectError
          (linesIn loaded ["[1, 2, 3] spinner"])
          "`spinner` takes arguments: a point is written on an applied chart"
        expectError
          (linesIn loaded ["[1, 2, 3] (spinner t1) to eci"])
          "spinner takes arguments: write [1, 2, 3] (spinner t1) from (spinner …) to eci"
    , testCase "design §12: a spinning Earth, for illustration" $ do
        -- The GMST model is linear, θ = 280.46061837° + 360.98564736629°/day ×
        -- (t − J2000.0) (Meeus, Astronomical Algorithms, without the T² and
        -- T³ terms). Checked against the IAU 1982 GMST (Aoki et al. 1982,
        -- A&A 105, 359) at 2026 Jan 1 0h UT1, JD 2461041.5: 24110.54841 s +
        -- 8640184.812866 s T + 0.093104 s T² − 6.2e-6 s T³ with T = 0.26
        -- Julian centuries is 100.6608585° modulo 360°; the linear model is
        -- 0.094″ less.
        runLinesP
          ( take 3 spinningEarthSession
              ++ [ "let g = gmst (9496.5 J2000) / 1 deg"
                 , "abs (g - 360 * floor (g / 360) - 100.6608585) < 1e-4"
                 ]
          )
          @?= Right ["true"]
        runLinesP spinningEarthSession
          @?= Right
            [ "chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg / day"
            , "[-734892.0553385001942 ± 3e-13, 3903932.6219852148939…, 4990000] eci"
            , "stored use astro"
            , "[-284.67928970827302009…, -53.589180086727794658 ± 2.2e-17, 0] m s^-1"
            , "[0, 0, 0] m s^-1"
            , "[0.00000000000000000 ± 4e-17, -289.67930235205722039…, 0] m s^-1"
            ]
    ]
 where
  spinning =
    [ multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
    , "let w = 7.2921159e-5 rad/s"
    , "let t0 = 0 unix"
    , "let t1 = 1000 unix"
    , "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
    ]

{- | The session of design §12, "A spinning Earth": a chart turned by a
linear GMST and spinning at its rate, a station fixed on it, and the
station's velocity, which is the Earth's rotation alone.
-}
spinningEarthSession :: [Text]
spinningEarthSession =
  [ multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
  , "let gmst t = 280.46061837 deg + 360.98564736629 deg / day * (t .- 0 J2000)"
  , "chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg/day"
  , ":view earth"
  , "chart greenwich t on (earth t) at [3972.5, 0, 4990] km"
  , "let t26 = 9496.5 J2000"
  , "[0, 0, 0] (greenwich t26) from (greenwich t26) to eci"
  , ":use astro"
  , "let st = stateFrom (greenwich t26) t26 ([0, 0, 0] m) ([0, 0, 0] m/s)"
  , "st.vel to m/s"
  , "velocityIn (greenwich st.epoch) st"
  , "velocityIn (greenwich t26) (State {epoch = t26, pos = st.pos, vel = [0, 0, 0] m/s})"
  ]

-- | Design §3.3, §3.8: @expm@, @transformBy@ and the bivector constructors.
rotationTests :: TestTree
rotationTests =
  testGroup
    "rotations"
    [ testCase "expm of a bivector is a right-handed rotation about each axis" $ do
        evalP "expm (rotz (90 deg)) @ [1, 0, 0]"
          @?= Right ["[3.0e-24 ± 3.8e-24, 1.0000000000000000000…, 0]"]
        evalP (encloses "1e-20" "expm (rotz (90 deg)) @ e1" "e2") @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotx (90 deg)) @ e2" "e3") @?= Right ["true"]
        evalP (encloses "1e-20" "expm (roty (90 deg)) @ e3" "e1") @?= Right ["true"]
        evalP
          (encloses "1e-20" "expm (rotz (30 deg)) @ e1" "[cos (30 deg), sin (30 deg), 0]")
          @?= Right ["true"]
    , testCase "expm of zero is the identity, exactly" $ do
        evalP "expm [[0, 0, 0], [0, 0, 0], [0, 0, 0]]"
          @?= Right ["[1, 0, 0; 0, 1, 0; 0, 0, 1]"]
        evalP "expm [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]"
          @?= Right ["[1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]"]
        evalP "expm (rotz (0 deg)) == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
          @?= Right ["true"]
        case evalP "expm [[5]]" of
          Right [v] -> T.isPrefixOf "[[148.41315910257660342" v @? T.unpack v
          other -> assertFailure (show other)
    , testCase "expm (-B) undoes expm B" $ do
        let b = "axisAngle [1, 2, 2] (40 deg)"
        evalP
          ( encloses
              "1e-20"
              ("expm (-(" <> b <> ")) @ (expm (" <> b <> ") @ [3, -1, 2])")
              "[3, -1, 2]"
          )
          @?= Right ["true"]
        -- not antisymmetric: the series, with its remainder
        let m = "[[0.1, 0.2], [0.3, -0.1]]"
        evalP (encloses "1e-20" ("expm (-" <> m <> ") @ expm " <> m) "[[1, 0], [0, 1]]")
          @?= Right ["true"]
    , testCase "a rotation is orthogonal: Rᵀ R encloses I" $ do
        let i3 = "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
        evalP
          ( encloses
              "1e-20"
              "let r = expm (axisAngle [1, 2, 2] (40 deg)) in transpose r @ r"
              i3
          )
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "let r = euler313 (30 deg) (45 deg) (60 deg) in transpose r @ r"
              i3
          )
          @?= Right ["true"]
    , testCase "an uncertain angle carries its nudge into the entries" $ do
        -- R00 = cos θ moves at the full rate, R01 = sin θ only to second order
        evalP
          "let b = bound (expm (rotz (90 deg ± 0.001 rad))) in b.0.0 >= 0.001 && b.0.0 <= 0.0011 && b.1.1 >= 0.001 && b.0.1 <= 1e-5 && b.2.2 == 0"
          @?= Right ["true"]
        -- an angle whose enclosure contains zero: nothing divides by it
        evalP
          ( encloses
              "0.0011"
              "expm (rotz (0 rad ± 0.001 rad))"
              "[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
        evalP
          "let b = bound (expm (rotz (0 rad ± 0.001 rad))) in b.0.1 >= 0.001 && b.0.0 <= 1e-5"
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm (rotz (1e-30 rad)) @ e1"
              "[cos (1e-30 rad), sin (1e-30 rad), 0]"
          )
          @?= Right ["true"]
    , testCase "four dimensions: two planes by the series, one plane by Rodrigues" $ do
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 1/2, 0, 0], [-1/2, 0, 0, 0], [0, 0, 0, 1/3], [0, 0, -1/3, 0]]"
              ( T.unwords
                  [ "let a = 0.5 rad in let b = (1/3) * 1 rad in"
                  , "[[cos a, sin a, 0, 0], [-sin a, cos a, 0, 0],"
                  , "[0, 0, cos b, sin b], [0, 0, -sin b, cos b]]"
                  ]
              )
          )
          @?= Right ["true"]
        -- one plane, found exactly: the other two axes are untouched
        evalP
          "let r = expm [[0, 3, 0, 0], [-3, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]] in r.2 == [0, 0, 1, 0] && r.3 == [0, 0, 0, 1]"
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 3, 0, 0], [-3, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]"
              "[[cos (3 rad), sin (3 rad), 0, 0], [-sin (3 rad), cos (3 rad), 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]"
          )
          @?= Right ["true"]
    , testCase "expm of a general matrix: the scaled and squared series" $ do
        evalP (encloses "1e-20" "expm [[1, 0], [0, 2]]" "[[exp 1, 0], [0, exp 2]]")
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm [[0, 1, 0], [0, 0, 1], [0, 0, 0]]"
              "[[1, 1, 1/2], [0, 1, 1], [0, 0, 1]]"
          )
          @?= Right ["true"]
        -- uncertain entries: the enclosure holds the midpoint matrix's exponential
        evalP
          ( encloses
              "0.1"
              "expm ([[0.1, 0.2], [0.3, -0.1]] ± 0.01)"
              "expm [[0.1, 0.2], [0.3, -0.1]]"
          )
          @?= Right ["true"]
        -- nearly antisymmetric (two fresh nudges where one would cancel):
        -- Rodrigues with the symmetric part's bound, not the slow series
        let near =
              "let x = sqrt 2 in let y = sqrt 3 in [[0, x * y, 0], [(0 - x) * y, 0, 0], [0, 0, 0]]"
        expectError
          (evalP ("let b = " <> near <> " in b + transpose b == 0 * b"))
          "decide"
        evalP
          ( encloses
              "1e-20"
              ("expm (" <> near <> ")")
              "let a = sqrt 6 * 1 rad in [[cos a, sin a, 0], [-sin a, cos a, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
        evalP "expm [[1, 2], [3, 4]]"
          @?= Right
            [ "[51.968956198705003658…, 74.736564567003212549…; 112.10484685050481882…, 164.07380304920982248…]"
            ]
    , testCase "expm is dimensionless" $ do
        typeOfTextP "expm" @?= Right "forall n. Mat n n -> Mat n n"
        expectError (evalP "expm [[1 m]]") "dimensions differ"
        expectError (evalP "expm (rotz (1 m))") "expected Num rad, got Num m"
        expectError (evalP "rotz 1") "expected Num rad, got Num"
    , testCase "transformBy applies R along every axis" $ do
        let r = "[[1, 2, 0], [3, 4, 1], [0, 1, 5]]"
            s = "[[2, 0, 1], [1, 1, 0], [0, 3, 1]]"
            p = "[[2, 1, 0], [1, 3, 1], [0, 7, 4]]"
        evalP ("transformBy " <> r <> " [1, -2, 3] == " <> r <> " @ [1, -2, 3]")
          @?= Right ["true"]
        evalP
          ( "transformBy "
              <> r
              <> " "
              <> p
              <> " == "
              <> r
              <> " @ "
              <> p
              <> " @ transpose "
              <> r
          )
          @?= Right ["true"]
        evalP
          ( "let a = [1, 2, 3] in let b = [0, -1, 2] in let c = [4, 0, 1] in transformBy "
              <> r
              <> " (a ⊗ b ⊗ c) == ("
              <> r
              <> " @ a) ⊗ ("
              <> r
              <> " @ b) ⊗ ("
              <> r
              <> " @ c)"
          )
          @?= Right ["true"]
        evalP
          ( "transformBy "
              <> r
              <> " (transformBy "
              <> s
              <> " "
              <> p
              <> ") == transformBy ("
              <> r
              <> " @ "
              <> s
              <> ") "
              <> p
          )
          @?= Right ["true"]
        -- the identity keeps every component as it was, nudges and all
        evalP "let t = [[1, 2], [3, 4]] ± 0.1 in transformBy [[1, 0], [0, 1]] t == t"
          @?= Right ["true"]
        -- a rotation of a covariance
        evalP
          ( encloses
              "1e-20"
              "transformBy (expm (rotz (90 deg))) [[4, 1, 0], [1, 9, 0], [0, 0, 1]]"
              "[[9, -1, 0], [-1, 4, 0], [0, 0, 1]]"
          )
          @?= Right ["true"]
    , testCase "transformBy keeps the dimension and the display unit" $ do
        evalP "transformBy [[0, 1], [1, 0]] ([1, 2] km)" @?= Right ["[2, 1] km"]
        evalP "transformBy [[0, 1], [1, 0]] ([[1, 2], [3, 4]] km)"
          @?= Right ["[4, 3; 2, 1] km"]
        evalP "transformBy [[0, 1], [1, 0]] (5 km)" @?= Right ["5 km"]
        typeOfTextP "transformBy"
          @?= Right "forall n s d. Mat n n -> Tensor s d -> Tensor s d"
        typeOfTextP "transformBy (expm (rotz (10 deg))) ([1, 2, 3] m)"
          @?= Right "Vec 3 m"
    , testCase "transformBy refuses an axis of another length, at run time" $ do
        expectError
          (evalP "transformBy [[1, 2], [3, 4]] [1, 2, 3]")
          "transformBy: every axis must have length n: the matrix is 2 × 2 and the tensor's lengths are [3]"
        expectError
          (evalP "transformBy [[1, 2], [3, 4]] [[1, 2, 3], [4, 5, 6]]")
          "every axis must have length n: the matrix is 2 × 2 and the tensor's lengths are [2, 3]"
    , testCase "the constructors' types" $ do
        typeOfTextP "e1" @?= Right "Vec 3"
        typeOfTextP "rotx" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "roty" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "rotz" @?= Right "forall (a : 3). Num rad -> Mat a a"
        typeOfTextP "dual"
          @?= Right
            "forall (a : 3) s d (b : 3) (c : 3). Tensor (a : s) d -> Tensor (b : c : s) d"
        typeOfTextP "axisAngle"
          @?= Right "forall (a : 3) d (b : 3) (c : 3). Vec a d -> Num rad -> Mat b c"
        typeOfTextP "rotation"
          @?= Right "forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a b"
        typeOfTextP "euler313"
          @?= Right "forall (a : 3). Num rad -> Num rad -> Num rad -> Mat a a"
    , testCase "rotz is θ (e2 ∧ e1): ∧ turns its second vector toward its first" $ do
        evalP "e1 /\\ e2" @?= Right ["[0, 1, 0; -1, 0, 0; 0, 0, 0]"]
        evalP "rotz (90 deg) == pi / 2 * (e2 /\\ e1)" @?= Right ["true"]
        evalP "rotx (1 rad)" @?= Right ["[0, 0, 0; 0, 0, -1; 0, 1, 0]"]
        evalP "roty (1 rad)" @?= Right ["[0, 0, 1; 0, 0, 0; -1, 0, 0]"]
        evalP "rotz (1 rad)" @?= Right ["[0, -1, 0; 1, 0, 0; 0, 0, 0]"]
    , testCase "axisAngle and dual" $ do
        evalP "axisAngle [0, 0, 1] (30 deg) == rotz (30 deg)" @?= Right ["true"]
        evalP "axisAngle [0, 0, 2] (30 deg) == rotz (30 deg)" @?= Right ["true"]
        evalP "axisAngle e1 (1 rad) == rotx (1 rad)" @?= Right ["true"]
        evalP "axisAngle e2 (1 rad) == roty (1 rad)" @?= Right ["true"]
        -- dual is the inverse of ⋆; the generator about n is the dual of -n
        evalP "star (dual [1, 2, 3])" @?= Right ["[1, 2, 3]"]
        evalP "dual e3" @?= Right ["[0, 1, 0; -1, 0, 0; 0, 0, 0]"]
        evalP "dual [1, 2, 3] @ [4, 5, 6] == cross [4, 5, 6] [1, 2, 3]"
          @?= Right ["true"]
        evalP (encloses "1e-20" "expm (axisAngle [1, 1, 1] (120 deg)) @ e1" "e2")
          @?= Right ["true"]
    , testCase "rotation a b takes a to b" $ do
        evalP "rotation e1 e2 == rotz (90 deg)" @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotation e1 e2)" "expm (rotz (90 deg))")
          @?= Right ["true"]
        evalP
          ( encloses
              "1e-20"
              "expm (rotation [1, 2, 3] [-2, 0, 1]) @ [1, 2, 3]"
              "norm [1, 2, 3] / norm [-2, 0, 1] * [-2, 0, 1]"
          )
          @?= Right ["true"]
        -- any dimensions: only the directions matter
        evalP "rotation ([1, 0, 0] m) ([0, 5, 0] s) == rotz (90 deg)" @?= Right ["true"]
        -- parallel: the zero bivector; antiparallel: half a turn in the plane through e3
        evalP "rotation [1, 1, 0] [2, 2, 0]" @?= Right ["[0, 0, 0; 0, 0, 0; 0, 0, 0]"]
        evalP (encloses "1e-20" "expm (rotation e1 (-e1)) @ e1" "-e1")
          @?= Right ["true"]
        evalP (encloses "1e-20" "expm (rotation e1 (-e1)) @ e2" "e2") @?= Right ["true"]
        -- along e3 itself, the plane through e1
        evalP (encloses "1e-20" "expm (rotation e3 (-e3)) @ e3" "-e3")
          @?= Right ["true"]
    , testCase "euler313 is the perifocal-to-inertial matrix" $ do
        -- Ω = 30°, i = 45°, ω = 60°, entries by the textbook formula
        let q =
              T.unwords
                [ "let o = 30 deg in let i = 45 deg in let w = 60 deg in"
                , "[[cos o * cos w - sin o * sin w * cos i, -cos o * sin w - sin o * cos i * cos w, sin o * sin i],"
                , "[sin o * cos w + cos o * cos i * sin w, -sin o * sin w + cos o * cos i * cos w, -cos o * sin i],"
                , "[sin i * sin w, sin i * cos w, cos i]]"
                ]
        evalP (encloses "1e-20" "euler313 (30 deg) (45 deg) (60 deg)" q)
          @?= Right ["true"]
    , testCase
        "every constructor's bivector is exactly antisymmetric, enclosures and all"
        $ do
          let antisymmetric b = evalP ("let b = " <> b <> " in b + transpose b == 0 * b")
          antisymmetric "rotz (30 deg ± 0.01 rad)" @?= Right ["true"]
          antisymmetric "axisAngle [1, 1, 1] (120 deg)" @?= Right ["true"]
          antisymmetric "axisAngle ([1, 2, 2] ± 0.1) (40 deg ± 0.01 rad)"
            @?= Right ["true"]
          antisymmetric "rotation [1, 2, 3] [-2, 0, 1]" @?= Right ["true"]
          antisymmetric "rotation ([1, 2, 3] ± 0.01) [-2, 0, 1]" @?= Right ["true"]
          antisymmetric "rotation e1 (-e1)" @?= Right ["true"]
    , testCase "an uncertain angle makes a bivector with nudged entries" $ do
        evalP
          "let b = bound (rotz (90 deg ± 0.001 rad)) in b.0.1 >= 0.001 && b.1.0 >= 0.001 && b.0.0 == 0"
          @?= Right ["true"]
        evalP "rotz (90 deg ± 0.001 rad)"
          @?= Right ["[0, -1.5708 ± 0.0012, 0; 1.5708 ± 0.0012, 0, 0; 0, 0, 0]"]
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
forProgram src = timedForAllShow src.programs showProgram

{- | How long one generated case may take, in microseconds: far above what
any case normally costs (the whole suite runs in seconds), so that a
pathologically slow case fails, with its input printed, instead of
hanging the suite.
-}
caseLimit :: Int
caseLimit = 10_000_000

{- | 'forAllShow' with 'caseLimit' on every case. The limit sits inside the
quantifier, so a case that runs out of time still prints its input.
-}
timedForAllShow ::
  (Testable p) => Gen a -> (a -> String) -> (a -> p) -> Property
timedForAllShow gen shown k = forAllShow gen shown (within caseLimit . k)

-- | 'timedForAllShow' printing the input with 'show'.
timedForAll :: (Show a, Testable p) => Gen a -> (a -> p) -> Property
timedForAll gen = timedForAllShow gen show

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
            ( Runtime
                (const Nothing)
                (\_ _ _ -> Nothing)
                (\_ _ _ -> Nothing)
                (const Nothing)
                (const Nothing)
                (newBudget defaultLimits typed)
            )
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

-- Axis slots ------------------------------------------------------------------

{- | Design §3.9, stage 2b, and §3.10, part F: a chart declaration mints its
frame, and its axes when it turns; points are typed by their frames, and
amounts and rotations by the axes. Each turned chart here is only typed,
or used once, since its rotation costs an @expm@.
-}
namedAxesTests :: TestTree
namedAxesTests =
  testGroup
    "named axes"
    [ testCase "a chart mints a frame, named as the chart" $ do
        runLinesP [eci, ":ls --types eci", ":type eci"]
          @?= Right ["frame eci", "Chart eci"]
        -- Two charts of one body: two frames, two hashes.
        s <- sessionOf [eci, "chart lab on GCRS"]
        lookupTypeName "eci" s.staging /= lookupTypeName "lab" s.staging
          @? "one frame for two charts"
        isJust (lookupTypeName "eci" s.staging) @? "no frame for eci"
        linesIn s [":hash eci"] /= linesIn s [":hash lab"] @? "one hash for two charts"
        -- No source declaration has the frame's label kind.
        u <- sessionOf [eci, "data Eci = Eci"]
        lookupTypeName "Eci" u.staging /= lookupTypeName "eci" u.staging
          @? "a data type is a chart's frame"
        hashTypeDef (frameDef "eci" False)
          /= hashTypeDef (TypeDef [] [[]] (Owner "eci"))
          @? "an owner stamp is a frame stamp"
        hashTypeDef (frameDef "eci" False) /= hashTypeDef (frameDef "eci" True)
          @? "a frame with parameters is the same type as one without"
        decodeTypeDef (encodeTypeDef (frameDef "eci" True))
          @?= Right (frameDef "eci" True)
        decodeTypeDef (encodeTypeDef (axesDef "eci")) @?= Right (axesDef "eci")
        let inertial = spaceDef "GCRS" [3] (dimFromAtoms [(Base Dimension.L, 1)])
        decodeTypeDef (encodeTypeDef inertial) @?= Right inertial
        expectError
          (linesIn u ["mkChart {Eci} {} eci {} {} {} {}"])
          "mkChart takes the frame a chart declaration mints first"
        -- A rescaling shares its parent's frame and mints none; a scalar
        -- chart's frame is named too.
        t <- sessionOf [eci, "chart ekm on eci step km"]
        lookupTypeName "ekm" t.staging @?= Nothing
        isJust (lookupTypeName "temperature.degC" t.staging) @? "no frame for degC"
        linesIn t [":type [1, 2, 3] ekm", "[1, 2, 3] ekm .- [0, 0, 0] eci"]
          @?= Right ["Point eci", "[1000, 2000, 3000] m"]
        -- The frame of a renamed chart follows it.
        r <- sessionOf [eci, ":add", ":rename eci frame"]
        linesIn r [":ls --types frame", ":type [1, 2, 3] frame"]
          @?= Right ["frame frame", "Point frame"]
    , testCase "a point is on its frame; rotationOf is Mat space frame" $ do
        runLinesP
          ( frame
              ++ [ ":type [1, 2, 3] lvlh"
                 , ":type [1, 2, 3] lvlh .- [0, 0, 0] lvlh"
                 , ":type rotationOf lvlh"
                 , ":type [1, 0, 0] m to lvlh"
                 , ":type spinOf lvlh"
                 , ":type rotationOf lvlh @ ([1, 0, 0] m to lvlh)"
                 , ":type ([1, 0, 0] m to lvlh) from lvlh to eci"
                 ]
          )
          @?= Right
            [ "Point lvlh"
            , "Vec lvlh m"
            , "Mat GCRS lvlh"
            , "Vec lvlh m"
            , "Vec GCRS (1/s)"
            , "Vec GCRS m"
            , "Vec GCRS m"
            ]
        runLinesP
          ( frame
              ++ [ encloses "1e-20" "(([1, 2, 3] m to lvlh) from lvlh to eci) / 1 m" "[1, 2, 3]"
                 , encloses "1e-20" "det (rotationOf lvlh)" "1"
                 ]
          )
          @?= Right ["true", "true"]
        -- A chart parameter writes a point on any frame.
        runLinesP
          (frame ++ ["let place c x = pointOn c x", ":type place", "place lvlh [1, 2, 3]"])
          @?= Right ["forall c. Chart c -> Coords c -> Point c", "[1, 2, 3] lvlh"]
        -- The wrong rotation is a type error.
        expectError
          ( runLinesP
              (frame ++ ["let v = [1, 2, 3] eci .- [0, 0, 0] eci", "rotationOf lvlh @ v"])
          )
          "the axes of lvlh against the axes of GCRS"
    , testCase "a literal takes its frame from use; a named value is anonymous" $ do
        let setup = frame ++ ["let p = [1, 2, 3] eci", "let off = [0, 0, 2] m"]
        runLinesP
          (setup ++ ["p .+ [1, 0, 0] m", ":type off", ":type withAxes lvlh off"])
          @?= Right ["[2, 2, 3] eci", "Vec 3 m", "Vec lvlh m"]
        expectError
          (runLinesP (setup ++ ["p .+ off"]))
          "the axes of GCRS against anonymous axes; give it a frame with `withAxes c v`, or `v to c` if it is along its space's base axes"
        -- A function keeps its frame general; a value meets a frame through
        -- withAxes or a signature that keeps it polymorphic.
        runLinesP
          ( setup
              ++ [ "let shift q = q .+ [1, 0, 0] m"
                 , ":type shift"
                 , "shift p"
                 , encloses
                     "1e-20"
                     "(p .+ (withAxes lvlh off from lvlh to eci) .- p) / 1 m"
                     "[0, 0, 2]"
                 , multiline ["off2 :: forall (a : 3). Vec a m", "let off2 = [0, 0, 2] m"]
                 , ":ls off2"
                 , "p .+ off2"
                 , -- :type is the type of `it`, a named value
                   ":type off2"
                 ]
          )
          @?= Right
            [ "forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c"
            , "[2, 2, 3] eci"
            , "true"
            , "off2 : forall (a : 3). Vec a m"
            , "[1, 2, 5] eci"
            , "Vec 3 m"
            ]
    , testCase "roots on one space convert; two spaces never meet" $ do
        let setup = [eci, "chart lab on GCRS", "let p = [1, 2, 3] eci"]
        runLinesP
          (setup ++ ["p to lab", "(p .- [0, 0, 0] eci) + ([1, 0, 0] lab .- [0, 0, 0] lab)"])
          @?= Right ["[1, 2, 3] lab", "[2, 2, 3] m"]
        let apart = [eci, "space Bench = Vec 3 m", "chart lab on Bench", "let p = [1, 2, 3] eci"]
        expectError
          (runLinesP (apart ++ ["p to lab"]))
          "frames of two spaces, GCRS and Bench"
        expectError
          (runLinesP (apart ++ ["(p .- [0, 0, 0] eci) + ([1, 0, 0] lab .- [0, 0, 0] lab)"]))
          "the axes of GCRS against the axes of Bench"
    , testCase "scalar charts are typed by their frames too" $ do
        runLinesP
          [ "20 degC to degF"
          , "77 °F .- 68 °F"
          , ":type 20 degC"
          , ":type degC"
          , "chart warm on ITS90 at 300 K"
          , "1 warm .- 0 warm"
          ]
          @?= Right ["68 degF", "9 deltaF", "Point degC", "Chart degC", "1 K"]
    , testCase "a moving chart has one frame for every time" $ do
        let spinning =
              [ eci
              , "let w = 7.2921159e-5 rad/s"
              , "let t0 = 0 unix"
              , "chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w"
              ]
        runLinesP
          ( spinning
              ++ [ ":type rotationOf (spinner t0)"
                 , ":type rotationOf (spinner (t0 .+ 1 s))"
                 , ":type rotationOf (spinner t0) - rotationOf (spinner (t0 .+ 1 s))"
                 , ":type [1, 2, 3] (spinner t0)"
                 ]
          )
          @?= Right
            [ "Mat GCRS spinner"
            , "Mat GCRS spinner"
            , "Mat GCRS spinner"
            , "Point spinner"
            ]
    , testCase "a written type names a frame, its axes and a space's" $ do
        let signed =
              frame
                ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] m"]
                   , multiline ["c :: Chart lvlh", "let c = lvlh"]
                   ]
        runLinesP
          ( signed
              ++ [ ":type v"
                 , ":type rotationOf lvlh @ v"
                 , ":type c"
                 , ":type (rotationOf lvlh :: Mat GCRS lvlh)"
                 , ":type (rotationOf lvlh :: Mat eci lvlh)"
                 ]
          )
          @?= Right
            [ "Vec lvlh m"
            , "Vec GCRS m"
            , "Chart lvlh"
            , "Mat GCRS lvlh"
            , "Mat GCRS lvlh"
            ]
        expectError
          (runLinesP (frame ++ [":type (rotationOf lvlh :: Mat lvlh GCRS)"]))
          "the axes of"
        runLinesP
          ( frame
              ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] lvlh .- [0, 0, 0] lvlh"]
                 , ":type v"
                 ]
          )
          @?= Right ["Vec lvlh m"]
        -- In one group with the chart: a signature framing a chart's
        -- origin, and a data declaration over a chart's axes.
        runLinesP
          [ multiline
              [ eci
              , "r0 :: Vec eci m"
              , "let r0 = [7000, 0, 0] km"
              , "chart lvlh on eci at r0 by rotz (90 deg)"
              , "data Obs = Obs (Vec eci m)"
              ]
          , ":type r0"
          , ":type Obs ([1, 2, 3] eci .- [0, 0, 0] eci)"
          , ":type rotationOf lvlh"
          ]
          @?= Right ["Vec GCRS m", "Obs", "Mat GCRS lvlh"]
        -- The group's charts enter first, unchecked: a stored signature a
        -- redefinition they depend on breaks is still checked.
        expectError
          ( runLinesP
              [ eci
              , multiline ["k :: Num m", "let k = 3 m"]
              , ":add"
              , multiline
                  ["let k = 2 s", "chart c on eci by rotz (k / 1 s * 1 rad)"]
              ]
          )
          "`k`'s definition has type `Num s`, not as general as its signature `Num m`"
        -- A root chart's origin is along its space's base axes, so a named
        -- value there needs a signature that keeps it polymorphic.
        expectError
          (runLinesP [eci, "let o = [100, 200, 0] m", "chart site on GCRS at o"])
          "anonymous axes"
        runLinesP
          [ eci
          , multiline ["o :: forall (a : 3). Vec a m", "let o = [100, 200, 0] m"]
          , "chart site on GCRS at o"
          , "[1, 2, 3] site"
          ]
          @?= Right ["[1, 2, 3] site"]
        -- Named slots follow a chart's axes when it is renamed, in a
        -- signature and in a data field, and across a reload.
        let renamed =
              frame
                ++ [ multiline ["v :: Vec lvlh m", "let v = [1, 0, 0] m"]
                   , "data Obs = Obs (Vec lvlh m) (Point lvlh)"
                   , ":add"
                   , ":rename lvlh turned"
                   ]
        moved <- sessionOf renamed
        linesIn moved [":type v", ":view Obs"]
          @?= Right ["Vec turned m", "data Obs = Obs (Vec turned m) (Point turned)"]
        withTempStore $ \dir -> do
          stored <- persistLines dir renamed
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.signatures @?= stored.codebase.signatures
          linesIn loaded [":type v", ":view Obs"]
            @?= Right ["Vec turned m", "data Obs = Obs (Vec turned m) (Point turned)"]
        -- A chart redefined as no chart leaves no frame behind.
        fmap
          (lastN 1)
          (runLinesP [eci, ":add", "let eci = 3", ":update", ":ls --types eci"])
          @?= Right ["nothing matches"]
        -- A signature that names a chart's axes reads back in one group
        -- with the chart: through :export and :load, and across a reload.
        s <- sessionOf (signed ++ [":add"])
        source <- either (assertFailure . T.unpack) pure (exportSource s Nothing)
        reloaded <-
          either
            (\err -> assertFailure (T.unpack (err <> "\nin the export:\n" <> source)))
            pure
            (sessionP [source, ":add"])
        reloaded.codebase.signatures @?= s.codebase.signatures
        reloaded.codebase.names @?= s.codebase.names
        withTempStore $ \dir -> do
          stored <- persistLines dir (signed ++ [":add"])
          (loaded, notes) <- reload dir
          notes @?= []
          loaded.codebase.signatures @?= stored.codebase.signatures
          linesIn loaded [":type v"] @?= Right ["Vec lvlh m"]
    , testCase "the library's states are typed by their spaces" $ do
        runLinesP [":use astro", ":type velocityIn", ":type stateFrom"]
          @?= Right
            [ "stored use astro"
            , "forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c -> State c1 s1 -> Vec c (m/s)"
            , "forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c -> Point c1 -> Vec c m -> Vec c (m/s) -> State c1 s1"
            ]
        runLinesP
          ( frame
              ++ [ ":use astro"
                 , "let st = stateFrom lvlh (0 unix) ([1, 0, 0] m) ([0, 1, 0] m/s)"
                 , ":type st"
                 , ":type st.pos"
                 , encloses "1e-20" "velocityIn lvlh st / (1 m/s)" "[0, 1, 0]"
                 ]
          )
          @?= Right
            ["stored use astro", "State unix GCRS", "Vec GCRS m", "true"]
    ]
 where
  eci = multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
  frame = [eci, "chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"]

{- | The name slot of a shape position (design §3.9, stage 1). These read
definitions whose stored types carry a named set by hash, with no chart
behind it, and check the unifier, lint and the encoding on the slot
directly; 'namedAxesTests' has them from source.
-}
axisSlotTests :: TestTree
axisSlotTests =
  testGroup
    "axis slots"
    [ testCase "a named axis set does not unify with anonymous axes"
        $ typed (prim2 "add" (ref lvlhV) (Noise Bound (Owner "") 3))
          @?= Left
            ( "expected Vec "
                <> showHash lvlh
                <> ", got Vec 3: the axes of "
                <> showHash lvlh
                <> " against anonymous axes; give it a frame with `withAxes c v`, or `v to c` if it is along its space's base axes"
            )
    , testCase "a literal takes the axes of what it meets (decision 5)"
        $ typed (prim2 "add" (ref lvlhV) (Lit (LTensor ([3], [1, 2, 3]))))
          @?= Right [Forall [] (vecAlong lvlh)]
    , testCase "a local value's free axes are anonymous (decision 5)"
        $ typed
          ( Let
              "off"
              (Lit (LTensor ([3], [1, 2, 3])))
              (prim2 "add" (Var FZ) (Noise Bound (Owner "") 3))
          )
          @?= Right [Forall [] (TTensor (pos (LLit 3) AAnon SNil) dimOne)]
    , testCase "two named axis sets do not unify"
        $ typed (prim2 "add" (ref lvlhV) (ref eciV))
          @?= Left
            ( "expected Vec "
                <> showHash lvlh
                <> ", got Vec "
                <> showHash eci
                <> ": the axes of "
                <> showHash lvlh
                <> " against the axes of "
                <> showHash eci
            )
    , testCase "an axis variable binds to a named set"
        $ typed (Lam "v" (prim2 "add" (Var FZ) (ref lvlhV)))
          @?= Right [Forall [] (TFun (vecAlong lvlh) (vecAlong lvlh))]
    , testCase "dot's contracted positions share one axis variable" $ do
        -- Rows along eci, columns along lvlh, applied to a vector along
        -- lvlh: a vector along eci.
        typed (prim2 "dot" (ref rot) (ref lvlhV)) @?= Right [Forall [] (vecAlong eci)]
        case typed (prim2 "dot" (ref rot) (ref eciV)) of
          Left err -> "the axes of" `T.isInfixOf` err @? T.unpack err
          Right sc -> assertFailure (show sc)
        -- An unknown left operand takes the right's axes at the contracted
        -- position.
        case typed (Lam "v" (prim2 "dot" (Var FZ) (ref lvlhV))) of
          Right [Forall _ (TFun (TTensor left _) _)] -> left @?= pos (LLit 3) (ANamed lvlh) SNil
          other -> assertFailure (show other)
    , testCase "an instance substitutes axis variables" $ do
        let scheme p = fromMaybe (error "no scheme") (primScheme p)
            e = (LLit 3, ANamed eci)
            l = (LLit 3, ANamed lvlh)
        TFun (mat e l) (mat l e) `isInstanceOf` scheme "transpose" @?= True
        TFun (mat e l) (mat e l) `isInstanceOf` scheme "transpose" @?= False
        TFun (mat e l) (mat l e) `isInstanceOf` scheme "inverse" @?= True
        TFun (mat l l) (vecAlong lvlh) `isInstanceOf` scheme "star" @?= True
        TFun (mat e l) (vecAlong lvlh) `isInstanceOf` scheme "star" @?= False
    , testCase "lint checks the contracted axes of dot" $ do
        let at r =
              TPrimApp
                "dot"
                ( TFun
                    (TTensor (pos (LLit 3) (ANamed eci) (pos (LLit 3) (ANamed lvlh) SNil)) dimOne)
                    (TFun (vecAlong r) (vecAlong eci))
                )
                [TRef rot Nothing "", TRef (if r == lvlh then lvlhV else eciV) Nothing ""]
        lintClosed look (at lvlh) @?= Right [Forall [] (vecAlong eci)]
        lintClosed look (at eci)
          @?= Left
            "dot: the right operand's first length and axes are not the left operand's last"
    , testCase "an anonymous position keeps the bytes of a bare length" $ do
        let def ax = TypeDef [] [[TTensor (pos (LLit 3) ax SNil) dimOne]] structuralLabel
        -- no parameters, one constructor of one field: a tensor whose shape
        -- is tag 1, the length 3, the end; no dimension; the structural label
        encodeTypeDef (def AAnon) @?= BS.pack [0, 1, 1, 0x21, 1, 0, 3, 0, 0, 1, 0]
        -- a variable slot is tag 3, the length, the axis (2, its id), the end
        encodeTypeDef (def (AVar 5))
          @?= BS.pack [0, 1, 1, 0x21, 3, 0, 3, 2, 5, 0, 0, 1, 0]
    , testCase "named and variable slots encode under their own tags and decode back" $ do
        let def =
              TypeDef
                [(0, KLen), (1, KAxis)]
                [
                  [ TTensor (pos (LVar 0 0) (AVar 1) (pos (LLit 3) (ANamed lvlh) SNil)) dimOne
                  , TChart
                      ( Frame
                          (FrNamed lvlh)
                          (ANamed lvlh)
                          (Space (SpNamed eci) (pos (LLit 3) AAnon SNil) dimOne (ANamed eci))
                      )
                  , TPoint
                      ( Frame
                          (FrNamed lvlh)
                          (AVar 1)
                          (Space (SpNamed eci) (pos (LLit 3) AAnon SNil) dimOne (AVar 1))
                      )
                  , TOver
                      (Frame (FrNamed lvlh) (AVar 1) (Space (SpNamed eci) SNil dimOne AAnon))
                      (Just dimOne)
                  , TData selfType [ALen (LLit 2), AAxis AAnon]
                  ]
                ]
                structuralLabel
        decodeTypeDef (encodeTypeDef def) @?= Right def
    ]
 where
  eci = Hash (BS.replicate 32 0xe1)
  lvlh = Hash (BS.replicate 32 0x1f)
  eciV = Hash (BS.replicate 32 0xa1)
  lvlhV = Hash (BS.replicate 32 0xa2)
  rot = Hash (BS.replicate 32 0xa3)
  pos = SCons
  vecAlong a = TTensor (pos (LLit 3) (ANamed a) SNil) dimOne
  mat (r, x) (c, y) = TTensor (pos r x (pos c y SNil)) dimOne
  stored =
    [ (eciV, vecAlong eci)
    , (lvlhV, vecAlong lvlh)
    , (rot, mat (LLit 3, ANamed eci) (LLit 3, ANamed lvlh))
    ]
  look = TypeLookup (\k -> (\t -> [Forall [] t]) <$> lookup k stored) (const Nothing)
  ref k = Ref k Nothing ""
  -- Elaborated and linted.
  typed t = do
    (schemes, tt) <- first (.message) (elaborateClosed look t)
    _ <- first ("lint: " <>) (lintClosed look tt)
    pure schemes

{- | The Core boundary keeps internal unit objects out of ordinary arithmetic,
while unit construction and suffix application remain checked primitives.
-}
readingTests :: TestTree
readingTests =
  testGroup
    "internal units and public amount arithmetic"
    [ testCase "Core arithmetic rejects internal units" $ do
        forM_ [ref km *. ref km, ref len *. ref km, ref len /. ref km, Pow (ref km) 2] $ \tm ->
          expectLeft (typed tm) "unit where an amount goes"
        expectLeft (typed (ref km +. ref km)) "units do not add"
    , testCase "internal scale constructs amounts and unit wraps a scalar" $ do
        typed (PrimApp "scale" [num 3, ref km]) @?= Right [Forall [] (numD metre)]
        typed (PrimApp "unit" [ref len *. num 60]) @?= Right [Forall [] (TUnit metre)]
        expectLeft
          (typed (PrimApp "unit" [Lit (LTensor ([2], [1, 2]))]))
          "a unit is one number"
    , testCase "generalised multiplication takes scalar times tensor" $ do
        fmap (map renderScheme) (typed (Lam "a" (Lam "b" (Var (FS FZ) *. Var FZ))))
          @?= Right ["Num d -> Tensor s d1 -> Tensor s (d*d1)"]
        fmap (map renderScheme) (typed (Lam "u" (Pow (Var FZ) 2)))
          @?= Right ["Num d -> Num (d^2)"]
        typed (Let "sq" (Lam "u" (Var FZ *. Var FZ)) (App (Var FZ) (ref len)))
          @?= Right [Forall [] (numD (Dimension.dimPow 2 metre))]
    , testCase "internal unit types still encode and decode" $ do
        let def = TypeDef [(0, KDim)] [[TUnit (Dimension.dimVar 0)]] structuralLabel
        decodeTypeDef (encodeTypeDef def) @?= Right def
    ]
 where
  km = Hash (BS.replicate 32 0xb1)
  len = Hash (BS.replicate 32 0xb3)
  metre = dimFromAtoms [(Base Dimension.L, 1)]
  look =
    TypeLookup
      ( \k -> (\ty -> [Forall [] ty]) <$> lookup k [(km, TUnit metre), (len, numD metre)]
      )
      (const Nothing)
  ref k = Ref k Nothing ""
  typed tm = do
    (schemes, tt) <- first (.message) (elaborateClosed look tm)
    _ <- first ("lint: " <>) (lintClosed look tt)
    pure schemes
  expectLeft :: (Show a) => Either Text a -> Text -> Assertion
  expectLeft r needle = case r of
    Left err ->
      (needle `T.isInfixOf` err) @? T.unpack ("expected " <> needle <> " in: " <> err)
    Right x -> assertFailure ("expected an error, got " <> show x)

partUTests :: TestTree
partUTests =
  testGroup
    "units are syntax"
    [ testCase "implicit one at multiplication and division" $ do
        runLinesP ["5 * km", "km * 5", "km/s", "(4 km) / km", "1 / km", "2 / km^2"]
          @?= Right ["5 km", "5 km", "1 km s^-1", "4", "1 km^-1", "2 km^-2"]
        runLinesP ["let mul a b = a * b", "mul 5 (1 km)", "(* km) 5", "(/ s) (4 km)"]
          @?= Right ["5 km", "5 km", "4 km s^-1"]
    , testCase "unit syntax does not escape as a value" $ do
        forM_
          [ "km"
          , "km^2"
          , "km + m"
          , "km < m"
          , "sin rad"
          , "let u = km"
          , "[km, m]"
          , "(km, 2 km)"
          , "(\\u -> u) km"
          , "outer km 2"
          ]
          $ \src ->
            expectError (runLinesP [src]) "a unit is not an expression"
        expectError
          (runLinesP ["f :: Unit m -> Num m", "let f x = x"])
          "units are syntax"
        expectError
          (runLinesP ["data Box r = Box (Quantity r m)"])
          "quantities are amounts"
    , testCase "quantity grouping is determined before implicit one" $ do
        runLinesP
          ["4 km / 2 km", "4 km / km", "(4 km) / km", "1 / 2 m/s", "1 / 2 * m / s"]
          @?= Right ["2", "4", "4", "0.5 s m^-1", "0.5 m s^-1"]
        runLinesP
          ["9.81 m/s^2", "5 km/h", "9.81 m s^-2", "6 m / 2 s", "let x = 2", "6 m / x"]
          @?= Right ["9.81 m s^-2", "5 km h^-1", "9.81 m s^-2", "3 m s^-1", "3 m"]
        let sameTerm a b =
              runLinesP ["let p = " <> a, "let q = " <> b, ":hash p", ":hash q"] >>= \case
                [hp, hq] -> Right (hp == hq)
                other -> Left (T.pack (show other))
        forM_
          [ ("9.81 m/s^2", "9.81 (m/s^2)")
          , ("9.81 m s^-2", "9.81 (m*s^-2)")
          , ("6 m / 2 s", "(6 m) / (2 s)")
          , ("\\x -> x / 1 km/h", "\\x -> x / (1 (km/h))")
          , ("5 * km", "5 * (1 km)")
          , ("x / km^2", "x / (1 (km^2))")
          ]
          $ \(a, b) ->
            if "x /" `T.isPrefixOf` a
              then sameTerm ("\\x -> " <> a) ("\\x -> " <> b) @?= Right True
              else sameTerm a b @?= Right True
    , testCase "aliases and shadowing distinguish units from amounts" $ do
        runLinesP
          ["unit u = s", "1 / 2 m/u", "let v = 1 s", "1 / 2 m/v", "let km = 7", "5 * km"]
          @?= Right ["0.5 u m^-1", "0.5 m^-1 s^-1", "35"]
        runLinesP ["5 * si.km", "(\\km -> 5 * km) 7", "let u = km/h", ":type u"]
          @?= Right ["5 km", "35", "Num (m/s)"]
        expectError (runLinesP ["let u = km/h", "5 u"]) "not a unit or a chart"
    , testCase "unit contexts include declarations, suffixes, to and chart steps" $ do
        runLinesP
          [ "unit min2 = 60 * s"
          , "unit deg2 = pi / 180 * rad"
          , "unit N2 = kg*m/s^2"
          , "unit dC = K"
          , "2 min2 to s"
          , "180 deg2 to rad"
          , "3 N2"
          , "1 dC"
          ]
          @?= Right ["120 s", "3.1415926535897932384… rad", "3 N2", "1 dC"]
        runLinesP
          ["unit am = deg / 60", "unit dF = 5/9 * K", "1 am to deg", "9 dF to K"]
          @?= Right ["0.016666666666666666666… deg", "5 K"]
        runLinesP
          ["chart degF2 on ITS90 at 459.67 deltaF step deltaF", "32 degF2 to degC"]
          @?= Right ["0 degC"]
        expectError
          (runLinesP ["chart bad on ITS90 step 1 K"])
          "expected unit syntax"
        expectError (runLinesP ["unit bad = [1,2] m"]) "a unit is one number"
    , testCase "charts remain first class and cannot enter arithmetic" $ do
        runLinesP ["let c = degF", "3 c", "20 degC to c", "let pt c = 3 c", "pt degC"]
          @?= Right ["3 degF", "68 degF", "3 degC"]
        expectError (runLinesP ["5 * degC"]) "got Chart"
        expectError (runLinesP ["20 degC + 30 degC"]) "Point"
        runLinesP ["20 degC .+ 5 K"] @?= Right ["25 degC"]
    , testCase "display conversions remain unit syntax" $ do
        runLinesP ["5 km/h to m/s", "1 km to m", "let v = 36 km/h", "v to m/s"]
          @?= Right ["1.3888888888888888888… m s^-1", "1000 m", "10 m s^-1"]
        expectError (runLinesP ["1 km to 1 m"]) "an amount after `to`"
        expectError (runLinesP ["5 km to h"]) "dimensions differ"
    , testCase "compound amounts print and read back" $ do
        forM_ ["km/h", "kg*m/s^2", "m/(s^2*K)", "1 / s", "2 * rad^2", "km/km", "km/m"] $ \src ->
          expecting (runLinesP [src]) $ \case
            [printed] -> runLinesP [printed] @?= Right [printed]
            other -> assertFailure (show other)
    , testCase "implicit one preserves uncertainty and chart axes" $ do
        runLinesP
          [ "unit measured = 1 m ± 0.01 m"
          , "(5 * measured) == 5 * (1 measured)"
          , "space Lengths = Vec 3 m"
          , "chart frame on Lengths"
          , "let v = withAxes frame ([1,2,3] m)"
          , "(v / km) == v / (1 km)"
          , "let scaled x = x * km"
          , "scaled [1,2;3,4] == [1,2;3,4] km"
          , "let here c = (3 c) to c"
          , "here degC"
          ]
          @?= Right ["true", "true", "true", "3 degC"]
    , testCase "every library definition prints as source that reads back to its hash" $ do
        s <- editSession
        forM_ stdlibNamespaces $ \ns -> do
          file <- editFileOf s [ns]
          (_, outs) <- edited (EditNamespace ns) file s
          (ns, outs) @?= (ns, ["nothing changed"])
    , testCase "a case that more text follows prints in parentheses and reads back" $ do
        -- A field access is a case, so `let x = r.mass in …` is one.
        let defs =
              [ "data B = B {mass :: Num kg}"
              , "let f r = let x = r.mass in x * 2"
              , "let g r = if (case r of B m -> m > 1 kg) then 1 else 2"
              , "let k b = case b of B m -> (case m > 1 kg of true -> 1; false -> 2)"
              ]
        views <-
          either
            (assertFailure . T.unpack)
            pure
            (runLinesP (defs ++ [":view f", ":view g"]))
        views
          @?= [ "f = \\r -> let x = (case r of B mass -> mass) in x * 2"
              , "g = \\r -> if (case r of B m -> m > 1 kg) then 1 else 2"
              ]
        -- Each printed body, entered again, is the same term.
        forM_ ["f", "g", "k"] $ \n ->
          expecting (runLinesP (defs ++ [":view " <> n, ":hash " <> n])) $ \case
            [v, hsh] ->
              expecting (runLinesP (take 1 defs ++ ["let " <> v, ":hash " <> n])) $ \outs ->
                lastN 1 outs @?= [hsh]
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
  timedForAllShow
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
    BoolT -> "Bool"
    TData _ _ -> "data"
    TFun _ _ -> "function"
    TPoint _ -> "Point"
    TOver _ _ -> "Diff"
    TUnit _ -> "Unit"
    TChart{} -> "Chart"
    TupleT _ -> "tuple"
    ListT _ -> "list"
    TTensor sh d ->
      ( case rankOf sh of
          0 -> "Num"
          1 -> "Vec"
          2 -> "Mat"
          _ -> "rank 3"
      )
        <> (if isDimOne d then "" else " with a dimension")
    TQty{} -> "Quantity"
    TVar _ -> "variable"

rankOf :: Shape -> Int
rankOf = \case
  SNil -> 0
  SCons _ _ rest -> 1 + rankOf rest
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
    TTensor (SCons{}) d -> any isBase (dimAtoms d)
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
  TPack _ _ ts -> sum (map polyLets ts)
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
  TPack _ _ ts -> concatMap annotations ts
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
        typeOfText "3 m" @?= Right "Num m"
    , testCase "quantity rule with powers" $ do
        evalText "9.81 m / s^2" @?= Right ["9.81 m s^-2"]
        typeOfText "9.81 m/s^2" @?= Right "Num (m/s^2)"
    , testCase "dimensions multiply and divide" $ do
        evalText "(2 m) * (3 s)" @?= Right ["6 m s"]
        evalText "(6 m) / (2 s)" @?= Right ["3 m s^-1"]
        evalText "(3 m)^2" @?= Right ["9 m^2"]
        evalText "[1, 2] m" @?= Right ["[1, 2] m"]
        evalText "2 kg * 3 m / s^2 == 6 kg * m / s^2" @?= Right ["true"]
    , testCase "adding different dimensions is a static error"
        $ case evalText "1 m + 1 s" of
          Left err -> T.isInfixOf "dimensions differ by m/s" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "the circular functions take an angle"
        $ case evalText "sin (1 m)" of
          Left err ->
            T.isInfixOf "sin takes an angle" err && T.isInfixOf "got Num m" err
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
        typeOfText "\\r -> r^2" @?= Right "forall d. Num d -> Num (d^2)"
        typeOfText "\\r -> pi * r^2" @?= Right "forall d. Num d -> Num (d^2)"
        typeOfText "\\x -> sqrt x" @?= Right "forall d. Num (d^2) -> Num d"
        typeOfText "\\x -> sqrt (x * x)" @?= Right "forall d. Num d -> Num d"
        typeOfText "\\a b -> atan2 a b"
          @?= Right "forall d. Num d -> Num d -> Num rad"
        typeOfText "\\x y -> x < y" @?= Right "forall d. Num d -> Num d -> Bool"
    , testCase "Kennedy's Euclid step: non-divisible exponents"
        $ typeOfText "\\f -> sqrt (f * f * f)"
          @?= Right "forall d. Num (d^2) -> Num (d^3)"
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
          @?= Right
            ["added g", "added fall", "forall d. Num d -> Num (m*d^2/s^2)", "44.145 m"]
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

-- Prelude ----------------------------------------------------------------------------

{- | A session on a seeded codebase: the library by domain, with its six
default uses stored.
-}
seeded :: Session
seeded = either (error . T.unpack) id seededSession

{- | An input in a seeded session after @:use@ of some of the library's
namespaces that are not used by default (@astro@, @physics@), without the
lines the @:use@s print.
-}
evalU :: [Text] -> Text -> Either Text [Text]
evalU spaces src =
  drop (length spaces) <$> runLinesP ([":use " <> n | n <- spaces] ++ [src])

-- | The lines @:ls@ at the root of a fresh codebase gives for the library.
libraryListing :: [Text]
libraryListing =
  [ "namespace " <> ns <> " (" <> T.pack (show (librarySize ns)) <> " names)"
  | ns <- sort stdlibNamespaces
  ]

-- | How many labels the library has under a namespace.
librarySize :: Text -> Int
librarySize ns = length (filter ((ns <> ".") `T.isPrefixOf`) stdlibNames)

-- | What a new store is seeded with.
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
        evalU ["astro", "physics"] "1 AU / c to s"
          @?= Right ["499.00478383615641191… s"]
    , testCase "conversions chain from the left, and print back so" $ do
        evalP "1 km to m to km" @?= Right ["1 km"]
        evalP "20 degC to degF to kelvin" @?= Right ["293.15 kelvin"]
        evalP "1.5 h to min to s" @?= Right ["5400 s"]
        runLinesP ["let f x = x to m to km", ":view f", "f (1500 m)"]
          @?= Right ["f = \\x -> x to m to km", "1.5 km"]
    , testCase "constants are exact where SI defines them so"
        $ evalU ["physics"] "c" @?= Right ["299792458 m s^-1"]
    , testCase "the hour is hr, with h an alias; Planck's h needs use physics" $ do
        evalP "3 hr to min" @?= Right ["180 min"]
        evalP "3 h" @?= Right ["3 h"]
        evalP "3 hr" @?= Right ["3 hr"]
        evalP "5 km/h to m/s" @?= Right ["1.3888888888888888888… m s^-1"]
        evalP "5 km/hr to m/s" @?= Right ["1.3888888888888888888… m s^-1"]
        evalP "1 h == 1 hr" @?= Right ["true"]
        expectError
          (runLinesP [":use physics", "3 h"])
          "`h` is both `time.h` and `physics.h`"
        evalU ["physics"] "3 hr" @?= Right ["3 hr"]
        evalU ["physics"] "physics.h" @?= Right ["6.62607015e-34 J s"]
        evalU ["physics"] "physics.h == planck" @?= Right ["true"]
    , testCase "the library by domain: si names, prefixes, time, angle, imperial" $ do
        evalP "1 newton == 1 N" @?= Right ["true"]
        evalP "2 newton" @?= Right ["2 newton"]
        evalP "kilo" @?= Right ["1000"]
        evalP "1 metre + 1 km" @?= Right ["1001 metre"]
        evalP "1 kohm == 1 kΩ" @?= Right ["true"]
        evalP "1 week to day" @?= Right ["7 day"]
        evalP "1 turn to deg" @?= Right ["360 deg"]
        evalP "1 steradian == 1 sr" @?= Right ["true"]
        evalP "0 kelvin to degC" @?= Right ["-273.15 degC"]
        evalU ["imperial"] "1 mile to km" @?= Right ["1.609344 km"]
        evalU ["imperial"] "1 psi to Pa" @?= Right ["6894.7572931683613367… Pa"]
        evalU ["imperial"] "60 mph to km/h" @?= Right ["96.56064 km h^-1"]
        evalU ["physics"] "1 eV to J" @?= Right ["1.602176634e-19 J"]
        evalU ["astro", "physics"] "1 ly to AU" @?= Right ["63241.077084266280268… AU"]
        -- A data type's dimension names a unit through the scope.
        runLinesP ["data F = F (Num N)", ":type F"]
          @?= Right ["Num (kg*m/s^2) -> F"]
    , testCase "cross is the Hodge dual of the wedge" $ do
        runLinesP [":view cross"] @?= Right ["cross = \\a -> \\b -> star (a ∧ b)"]
        evalP "[1, 2, 3] × [4, 5, 6] == star ([1, 2, 3] ∧ [4, 5, 6])" @?= Right ["true"]
        -- Contracting ε's last index first gives b × a, so the arguments swap.
        evalP "(ε @ [0, 1, 0]) @ [1, 0, 0]" @?= Right ["[0, 0, 1]"]
    , testCase "vimap maps with each component's position as a value" $ do
        -- defined over timap and signed, so it stays vector-only (design §3.3)
        case evalP "vimap (\\i x -> x) [1, 2; 3, 4]" of
          Left err -> T.isInfixOf "a vector against a matrix" err @? T.unpack err
          Right v -> assertFailure (show v)
        evalP ":view vimap"
          @?= Right ["vimap = \\f -> \\v -> timap (\\i -> \\x -> f i.0 x) v"]
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
        typeOfTextP "\\a b -> a /\\ b"
          @?= Right "forall n d d1. Vec n d -> Vec n d1 -> Mat n n (d*d1)"
        evalP "[1, 0] ∧ [0, 1]" @?= Right ["[0, 1; -1, 0]"]
    , testCase "an orbital calculation with units end to end"
        $ runLinesP
          [ "let r = [7000, 0, 0] km"
          , "let v = [0, 7.5, 0] km / s"
          , ":type r × v"
          , "(r × v).2"
          ]
          @?= Right ["Vec 3 (m^2/s)", "52500 km^2 s^-1"]
    ]

-- Display units ----------------------------------------------------------------------

displayTests :: TestTree
displayTests =
  testGroup
    "display units"
    [ testCase ":set unicode prints the unicode spellings, which read back" $ do
        let limits = settingLines defaultLimits
        runLinesP [":set"]
          @?= Right (["precision 20", "sigma 3", "unicode off", "nonlinear 1", "samples 0", "seed 1"] ++ limits)
        runLinesP [":set unicode on", ":set", ":set unicode off", ":set"]
          @?= Right
            ( ["precision 20", "sigma 3", "unicode on", "nonlinear 1", "samples 0", "seed 1"]
                ++ limits
                ++ ["precision 20", "sigma 3", "unicode off", "nonlinear 1", "samples 0", "seed 1"]
                ++ limits
            )
        case runLinesP [":set unicode maybe"] of
          Left err -> T.isInfixOf "unicode is on or off" err @? T.unpack err
          Right v -> assertFailure (show v)
        let defs =
              [ "let f x = x^2 + 1"
              , "let g x y = if x <= y then x^-1 else y"
              , "data Body = Body {mass :: Num kg, vel :: Vec 3 (m/s)}"
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
              , "forall a. (a -> a, Num (m/s^2))"
              , "f = \\x -> x^2 + 1"
              , "g = \\x -> \\y -> if x <= y then x^-1 else y"
              , "data Body = Body {mass :: Num kg, vel :: Vec 3 (m/s)}"
              ]
            unicode =
              [ "9.81 m s⁻²"
              , "5 km h⁻¹"
              , "Body {mass = 5 kg, vel = [0, 0, 1] m s⁻¹}"
              , "forall a. (a → a, Num (m/s²))"
              , "f = λx → x² + 1"
              , "g = λx → λy → if x ≤ y then x⁻¹ else y"
              , "data Body = Body {mass :: Num kg, vel :: Vec 3 (m/s)}"
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
          [ "data Body = Body {mass :: Num kg, vel :: Vec 3 (m/s)}"
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
        evalU ["astro", "physics"] "1 AU / c to min"
          @?= Right ["8.3167463972692735318… min"]
        evalP "90 min to h" @?= Right ["1.5 h"]
    , testCase "a user-declared unit"
        $ runLinesP ["unit furlong = 201.168 m", "1 km to furlong", "8 furlong to km"]
          @?= Right ["4.9709695378986717569… furlong", "1.609344 km"]
    , testCase "let-bound quantities are not units, their components are"
        $ runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2"] @?= Right ["39.24 m"]
    , testCase "the display unit must match the dimension or base units are used"
        $ evalP "sqrt (4 km^2)" @?= Right ["2000 m"]
    , testCase
        "units are codebase metadata: a renamed unit prints under its current name"
        $ runLinesP
          [ "unit fathom = 1.8288 m"
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
      (runLinesP ["unit fathom = 1.8288 m", ":add", ":hash fathom"])

-- Affine arithmetic -----------------------------------------------------------------
--
-- Design §3.2: exact values stay exact, approximations carry rigorous
-- enclosures, declared uncertainty keeps its identity, and printing never
-- shows a digit that is not certain.

{- | Newton's method for Kepler's equation, @E − e sin E = M@, with the
step count as an argument: @ea@ is used four times in each step.
-}
keplerIter :: Text
keplerIter =
  "let keplerIter m e k ea = if k == 0 then ea else keplerIter m e (k - 1) (ea - (ea - e * sin ea * 1 rad - m) / (1 - e * cos ea))"

-- | @k@ steps of 'keplerIter' from @M = 235.4°@, @e = 0.4@.
keplerAt :: Int -> Text
keplerAt k = "keplerIter (235.4 deg) 0.4 " <> T.pack (show k) <> " (235.4 deg)"

-- | The most decimal digits in a numerator or denominator of a magnitude.
longestRational :: Magnitude -> Int
longestRational = \case
  Exact r -> digits r
  Affine m ts s _ -> maximum (digits m : digits s : map (digits . fst) (Map.elems ts))
 where
  digits r = max (length (show (abs (numerator r)))) (length (show (denominator r)))

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
        evalText "tan (pi/4 * 1 rad)" @?= Right ["1.0000000000000000000…"]
        evalText "sqrt 2 * sqrt 2" @?= Right ["2.0000000000000000000…"]
        evalText "exp (-80)" @?= Right ["1.8048513878454151723…e-35"]
        evalText "sinh 1e-20" @?= Right ["1.0000000000000000000…e-20"]
    , testCase "the same operation twice gives the same nudge, so it cancels" $ do
        evalText "sin (1 rad) - sin (1 rad)" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x - x" @?= Right ["0"]
        evalText "let x = 5 ± 0.1 in x + 2 * x - 3 * x" @?= Right ["0"]
        evalText "let y = 1 ± 0.1 in y / y" @?= Right ["1"]
    , testCase "a denominator that may be zero is refused before anything cancels" $ do
        evalText "let x = 1 ± 1 in 1 / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in x / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in 0 / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 1 in (3 * x) / x" @?= Left "error: division by zero"
        evalText "let x = 1 ± 2 in x / x" @?= Left "error: division by zero"
        -- clear of zero, proportional forms still cancel
        evalText "let x = 2 ± 1.5 in (3 * x) / x" @?= Right ["3"]
    , testCase "equal slack is not a shared unknown, so it does not cancel" $ do
        let anonymous = Affine 2 Map.empty 1 Nothing
        case divM 24 anonymous anonymous of
          Right (Exact q) -> assertFailure ("cancelled to " <> show q)
          Right q -> radius q > 0 @? show q
          Left err -> assertFailure (show err)
        -- named nudges beside slack: the slack keeps it from cancelling
        let named = uncertain Bound (Tagged "s" 0) (Exact 2) (Exact (1 / 2))
            withSlack = addM 24 named anonymous
        case divM 24 withSlack withSlack of
          Right (Exact q) -> assertFailure ("cancelled to " <> show q)
          Right q -> radius q > 0 @? show q
          Left err -> assertFailure (show err)
        divM 24 (scaleM 24 3 named) named @?= Right (Exact 3)
    , testCase "remainders of different operand lists never share a nudge" $ do
        -- [1, 12] and [1/11, 2] once ran together as the same bytes
        let remainder operands = enclose "op" 24 operands 1 (Exact 0)
            a = remainder [Exact 1, Exact 12]
            b = remainder [Exact (1 / 11), Exact 2]
        map fst (nudges a) @?= [1]
        subM 24 a b /= Exact 0 @? "the remainders cancelled"
        radius (subM 24 a b) @?= 2
        -- the same operation twice is still one unknown
        subM 24 a (remainder [Exact 1, Exact 12]) @?= Exact 0
        -- an operand's kind and its count are part of the identity
        let x = uncertain Bound (Tagged "s" 0) (Exact 1) (Exact (1 / 2))
        subM 24 (remainder [x]) (remainder [x, Exact 0]) /= Exact 0 @? "count"
    , testCase "declared bounds print as mid ± r" $ do
        evalText "5 ± 0.1" @?= Right ["5.0 ± 0.1"]
        evalText "(5 ± 0.1) * (5 ± 0.1)" @?= Right ["25 ± 1"]
        evalText "(2 ± 0.1) ^ 3" @?= Right ["8.0 ± 1.3"]
        evalText "1e-30 * (1 ± 0.5)" @?= Right ["1.0e-30 ± 5e-31"]
    , testCase "a second-order term below the precision floor never marks" $ do
        -- x (4 − x) is stationary at 2, so its first-order σ cancels
        -- exactly; its second-order term, 1.4e-30, is arithmetic noise at 4
        evalText "let x = 2 ±σ 1e-15 in x * (4 - x)" @?= Right ["4"]
        -- at σ = 1e-3 the term, 1.4e-6, is real and visible
        evalText "let x = 2 ±σ 1e-3 in x * (4 - x)"
          @?= Right
            [ "4 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        -- at a midpoint of zero there is no floor: a square is all second order
        evalText "let n = 0 ±σ 1 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "let n = 0 ±σ 1e-15 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
    , testCase "a shared nudge squares into a one-sided range" $ do
        evalText "let n = noise 1 in n.0 * n.0" @?= Right ["0.5 ± 0.5"]
        evalText "let x = 5 ± 0.1 in x * x" @?= Right ["25 ± 1"]
    , testCase
        "standard uncertainties keep the σ marker and show a bound when it matters"
        $ do
          evalText "6.67430e-11 ±σ 1.5e-15" @?= Right ["6.67430e-11 ±σ 1.5e-15"]
          evalText "(6.67430e-11 ±σ 1.5e-15) * (2 ± 0.1)"
            @?= Right
              [ "1.335e-10 ±σ 3e-15 (bound 6.7e-12) (non-linear: mul: uncertain statistical coefficient, second-order term 5% of the first-order σ; a mean and a σ do not describe it)"
              ]
          -- σ by σ is second order: measured, never a bound (design §3.2)
          evalText "(1 ±σ 0.1) * (1 ±σ 0.1)"
            @?= Right
              [ "1.00 ±σ 0.14 (non-linear: mul, second-order term 7.1% of the first-order σ; a mean and a σ do not describe it)"
              ]
    , testCase "a statistical part non-linear through n*n is marked, never a bound" $ do
        let marked op r = case r of
              Right [v] ->
                T.isInfixOf ("(non-linear: " <> op <> ", ") v
                  && not (T.isInfixOf "0.5 ± 0.5" v)
                  @? T.unpack v
              other -> assertFailure (show other)
            refused what r = case r of
              Left err -> T.isInfixOf what err @? T.unpack err
              Right v -> assertFailure (show v)
        marked "mul" (evalText "let n = 0 ±σ 1 in n * n")
        refused
          "the difference is marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in (n * n) < 2")
        refused
          "sd of a value marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in sd (n * n)")
        refused
          "mid of a value marked non-linear by mul"
          (evalText "let n = 0 ±σ 1 in mid (n * n)")
        -- The discarded remainder has no identity: equal linear models
        -- alone cannot prove either equality or cancellation.
        refused "marked non-linear" (evalText "let n = 0 ±σ 1 in (n * n) == (n * n)")
        evalText "let n = 0 ±σ 1 in bound (n * n)" @?= Right ["0"]
        -- the mark propagates
        marked "mul" (evalText "let n = 0 ±σ 1 in n * n + 5")
        -- a σ of zero after a non-linear step prints as no certainty
        evalText "let n = 0 ±σ 1 in n * n + 5"
          @?= Right
            [ "5 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "let n = 0 ±σ 1 in n * n"
          @?= Right
            [ "0 (non-linear: mul, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        marked "mul" (evalText "let n = 0 ±σ 1 in sqrt (n * n + 5)")
        -- :budget names the operation
        expecting (runLines [":budget let n = 0 ±σ 1 in n * n"]) $ \out ->
          any (T.isInfixOf "non-linear: mul, second-order term unbounded") out @? show out
    , testCase "discarded statistical remainders cannot establish exact equality" $ do
        let refused src = case evalText src of
              Left err -> T.isInfixOf "marked non-linear" err @? T.unpack err
              Right out -> assertFailure (show out)
        refused "let n = 0 ±σ 1 in n*n == 0"
        refused "let n = 0 ±σ 1 in let q = 0 ±σ 2 in n*n == q*q"
        refused "let n = 0 ±σ 1 in sin (n * rad) == n"
        refused "let n = 0 ±σ 1 in sinh n == n"
        refused "sd (sinh (0 ±σ 10))"
        refused "let n = 0 ±σ 1 in sd ((1 ± 1) * n)"
        refused "let n = 0 ±σ 1 in covariance [(1 ± 1) * n]"
        refused "let n = 0 ±σ 1 in crossCovariance [n*n] [n]"
        -- Even below the warning threshold, a discarded remainder
        -- prevents an exact equality proof.
        refused "let n = 0 ±σ 0.00001 in sin (n * rad) == n"
        evalText "let n = 0 ±σ 1 in n - n" @?= Right ["0"]
    , testCase "expm refuses statistical inputs instead of erasing them" $ do
        let refused src = case evalP src of
              Left err ->
                T.isInfixOf "expm with statistical uncertainty is not supported" err
                  @? T.unpack err
              Right out -> assertFailure (show out)
        refused "let n = 0 ±σ 1 in expm [n, 0; 0, 0]"
        refused "let n = 0 ±σ 1 in expm [0, n; -n, 0]"
        refused "let n = 0 ±σ 1 in expm [n*n, 0; 0, 0]"
    , testCase "a small relative σ stays first order and unmarked" $ do
        let g = "(6.67430e-11 ±σ 1.5e-15)"
        evalText ("sqrt " <> g) @?= Right ["8.169639e-6 ±σ 9.2e-11"]
        evalText (g <> " * " <> g) @?= Right ["4.45463e-21 ±σ 1.4e-25"]
        evalText ("sin (" <> g <> " * 1 rad)") @?= Right ["6.67430e-11 ±σ 1.5e-15"]
        evalText "sqrt (100 ±σ 1)" @?= Right ["10.00 ±σ 0.05"]
        -- the delta method's second-order term, |f''|·σ² against |f'|·σ
        evalText "exp (0 ±σ 0.1)"
          @?= Right
            [ "1.0 ±σ 0.1 (non-linear: exp, second-order term 11% of the first-order σ; a mean and a σ do not describe it)"
            ]
        evalText "sqrt (100 ±σ 10)"
          @?= Right
            [ "10.0 ±σ 0.5 (non-linear: sqrt, second-order term 5.4% of the first-order σ; a mean and a σ do not describe it)"
            ]
        -- the threshold is a setting
        runLines [":set nonlinear 10", "(1 ±σ 0.1) * (1 ±σ 0.1)"]
          @?= Right ["1.00 ±σ 0.14"]
    , testCase "a statistical coefficient is never a hard limit" $ do
        -- no division by zero: the bound enclosure excludes zero
        evalText "1 / (1 ±σ 1)"
          @?= Right
            [ "1 ±σ 1 (non-linear: recip, second-order term unbounded; a mean and a σ do not describe it)"
            ]
        evalText "abs (1 ±σ 0.1)" @?= Right ["1.0 ±σ 0.1"]
        -- integer rounding is a comparison, decided at the stated sigma
        evalText "floor (2.5 ±σ 0.1)" @?= Right ["2"]
        case evalText "floor (2.5 ±σ 0.17)" of
          Left err -> T.isInfixOf "straddles a rounding boundary" err @? T.unpack err
          Right v -> assertFailure (show v)
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
        typeOfTextP "mid" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "bound" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "sd" @?= Right "forall s d. Tensor s d -> Tensor s d"
        typeOfTextP "bound (1 m ± 1 cm)" @?= Right "Num m"
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
          Left err -> T.isInfixOf "not a unit or a chart: write the `*`" err @? T.unpack err
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
        typeOfTextP "det" @?= Right "forall n a. Mat n a -> Num"
        typeOfTextP "\\a -> det a + 1" @?= Right "forall n a. Mat n a -> Num"
        runLinesP ["let d a = det a", "d [[2, 0, 0], [0, 3, 0], [0, 0, 4]] + d [[2]]"]
          @?= Right ["26"]
        evalP "det ([[1 m, 0 m], [0 m, 2 m]] / (1 m))" @?= Right ["2"]
        case evalP "det [[1 m, 0 m], [0 m, 1 m]]" of
          Left err ->
            T.isInfixOf "expected Mat n n, got Mat 2 2 m: dimensions differ by 1/m" err
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
            , "  bound  sqrt    9.3e-28       0% of bound"
            ]
    , testCase "the library's G carries its σ and a mass derived from it inherits it" $ do
        evalU ["astro"] "G" @?= Right ["6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
        evalU ["astro"] "iau2015.earth.mu / G" @?= Right ["5.97217e24 ±σ 1.3e20 kg"]
        case evalU ["astro"] ":budget iau2015.earth.mu / G" of
          Right (_ : _ : row : _) -> T.isInfixOf "σ      G" row && T.isInfixOf "100% of σ²" row @? T.unpack row
          other -> assertFailure (show other)
    , testCase "a unit is its own term: an amount of the same size is not one" $ do
        runLinesP ["let x = 1", "x + 2"] @?= Right ["3"]
        -- A unit's declaration makes its body a unit (design §3.10, U7), so
        -- the unit and the amount it was declared from are two terms.
        runLinesP
          [ "unit dozen = 12"
          , "let eggs = 12"
          , "3 dozen"
          , "eggs + 1"
          , ":hash dozen"
          , ":type 1 dozen"
          , ":type eggs"
          ]
          @?= Right ["3 dozen", "13", "#" <> dozenHash, "Num", "Num"]
        hashes <-
          either
            (assertFailure . T.unpack)
            pure
            (runLinesP ["unit dozen = 12", "let eggs = 12", ":hash dozen", ":hash eggs"])
        case hashes of
          [d, e] -> (d /= e) @? "a unit and an amount share a hash"
          other -> assertFailure (show other)
        case runLinesP ["let x = 1", "5 x"] of
          Left err -> T.isInfixOf "`x` is a Num, not a unit or a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
        -- Bq and Hz are one definition and two units; each prints as written.
        runLinesP ["5 Bq", "5 Hz", "1 Bq == 1 Hz"] @?= Right ["5 Bq", "5 Hz", "true"]
    , testCase "a let that rebinds a unit name makes it a quantity"
        $ runLinesP ["let g = 9.81 m / s^2", "g * (2 s)^2", "2 g"]
          @?= Left
            "error at 1:3\n  2 g\n    ^\n  `g` is a Num (m/s^2), not a unit or a chart: write the `*`"
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
            , "d = 5 klick"
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
            [ "values of dimension m/s print in km/h"
            , "18 km h^-1"
            , "50 km h^-1"
            , "5 m s^-1"
            , "5 m"
            , "values of dimension m/s print in m/s"
            , "prefer m/s"
            , "1.3888888888888888888… m s^-1"
            , "removed the preference m/s"
            , "5 km h^-1"
            ]
        -- A preference is a unit (design §3.10, U7), not an amount.
        case evalP ":prefer 5" of
          Left err -> T.isInfixOf "expected unit syntax" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP ":prefer 1 km/h" of
          Left err -> T.isInfixOf "expected unit syntax" err @? T.unpack err
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
        typeOfTextP "covariance" @?= Right "forall n d. Vec n d -> Mat n n (d^2)"
        typeOfTextP "cholesky" @?= Right "forall n a d. Mat n a (d^2) -> Mat n a d"
    , testCase "cholesky and ±σ refuse a matrix that is provably not symmetric" $ do
        evalP "cholesky [1, 100; 0, 1]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.1 and .1.0 differ"
        evalP "[0, 0] ±σ [1, 100; 0, 1]"
          @?= Left "error: ±σ needs a symmetric covariance: entries .0.1 and .1.0 differ"
        evalP "cholesky [4, 0, 1; 0, 4, 0; 2, 0, 4]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.2 and .2.0 differ"
        -- enclosures that do not overlap
        evalP "cholesky [4, 2 ± 0.1; 3, 3]"
          @?= Left "error: cholesky needs a symmetric matrix: entries .0.1 and .1.0 differ"
        -- Overlap is not proof of symmetry.
        evalP "cholesky [4, 2 ± 0.1; 2, 3]"
          @?= Left
            "error: cholesky needs a symmetric matrix: symmetry of entries .0.1 and .1.0 cannot be established"
        evalP "[0, 0] m ±σ [1, 0.5; 0.5, 1] m^2" @?= Right ["[0 ±σ 1, 0 ±σ 1] m"]
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
            @?= Right ["[0, 0, 0; 0, 0, 0] m s", "Mat 2 3 (m*s)", "[0, 0; 0, 0] km h"]
          -- A shared bound nudge is no covariance.
          evalP "crossCovariance ([1, 2] m ± 1 m #a) ([3, 4] m ± 1 m #a)"
            @?= Right ["[0, 0; 0, 0] m^2"]
          typeOfTextP "crossCovariance"
            @?= Right "forall n d m d1. Vec n d -> Vec m d1 -> Mat n m (d*d1)"
    , testCase "jointCovariance and the block filter: the types" $ do
        typeOfTextP "jointCovariance"
          @?= Right "forall n d d1. (Vec n d, Vec n d1) -> Cov2 n d d1"
        typeOfTextP "Cov2"
          @?= Right
            "forall n d d1. Mat n n (d^2) -> Mat n n (d*d1) -> Mat n n (d1^2) -> Cov2 n d d1"
        typeOfTextP "propagateCov2"
          @?= Right
            "forall n m d d1 d2 d3. (Mat n m (d1*d2*d3/d^2), Mat n m (d1*d3^2/d^2), Mat n m d2, Mat n m d3) -> Cov2 m (d/d2) (d/d3) -> Cov2 n (d1*d3/d) d"
        typeOfTextP "innovationCov2"
          @?= Right
            "forall n m d d1 d2. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Mat n n (d1^2*d2^2) -> Mat n n (d1^2*d2^2)"
        typeOfTextP "gain2"
          @?= Right
            "forall n m d d1 d2 s d3. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Tensor (n : s) d3 -> (Tensor (m : s) (d1^2*d2^2*d3/d), Tensor (m : s) (d1*d2^2*d3))"
        typeOfTextP "updateCov2"
          @?= Right
            "forall n m d d1 d2. (Mat n m d, Mat n m (d1^2/d2)) -> Mat m n (1/d) -> Mat m n (d2/d1^2) -> Cov2 n (d*d2/d1) d1 -> Cov2 n (d*d2/d1) d1"
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
    , testCase "points: charts, .+ and .-, printing on the written chart" $ do
        evalP "20 degC" @?= Right ["20 degC"]
        evalP "20 °C .+ 5 K" @?= Right ["25 degC"]
        evalP "20 degC .+ 9 deltaF" @?= Right ["25 degC"]
        evalP "77 °F .- 68 °F" @?= Right ["9 deltaF"]
        evalP "20 degC to degF" @?= Right ["68 degF"]
        evalP "(25 degC .- 20 degC) to K" @?= Right ["5 K"]
        evalP "100 degC .- (32 degF to degC)" @?= Right ["100 K"]
        evalP "0 kelvin to degC" @?= Right ["-273.15 degC"]
        evalP "0 J2000 to JD" @?= Right ["2451545 JD"]
        evalP "(0 J2000 .+ 365.25 day) .- 0 J2000" @?= Right ["365.25 day"]
        evalP "20 degC to kelvin" @?= Right ["293.15 kelvin"]
        -- Two frames are two types (design §3.10, F5): convert first.
        expectError
          (evalP "100 degC .- 32 degF")
          "points on degC and degF: convert one with `to`"
    , testCase "points over vectors: frames, projection, conversion between frames" $ do
        runLinesP
          [ "space Lab = Vec 3 m"
          , "chart site on Lab at [100, 200, 0] m"
          , "[1, 2, 3] site"
          , ":type [1, 2, 3] site"
          , "([1, 2, 3] site) .- ([0, 0, 0] site)"
          , "([1, 2, 3] site) .+ [1, 1, 1] km"
          , "([1, 2, 3] site).0"
          , ":type ([1, 2, 3] site).0"
          , "[1, 2, 3] site == [1, 2, 3] site"
          , -- a chart in km, translated from site, is on site's axes
            "chart ground on site at [-100, -200, 0] m step km"
          , "[7000, 0, 0] ground to site"
          , -- two roots on one space convert (design §3.10, F2)
            "chart bench on Lab"
          , "[0, 0, 0] site to bench"
          ]
          @?= Right
            [ "[1, 2, 3] site"
            , "Point site"
            , "[1, 2, 3] m"
            , "[1001, 1002, 1003] site"
            , "1 m"
            , "Num m"
            , "true"
            , "[6999900, -200, 0] site"
            , "[100, 200, 0] bench"
            ]
        -- Roots on two spaces never meet.
        expectError
          ( runLinesP
              [ "space Lab = Vec 3 m"
              , "space Sky = Vec 3 m"
              , "chart site on Lab at [100, 200, 0] m"
              , "chart eci on Sky step km"
              , "[7000, 0, 0] eci to site"
              ]
          )
          "frames of two spaces, Sky and Lab"
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "forall c. Point c -> Diff c -> Point c"
        case runLinesP
          ["space Lab = Vec 3 m", "chart site on Lab", "[1, 2, 3] site + [1, 1, 1] m"] of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case runLinesP
          ["space Lab = Vec 3 m", "chart site on Lab", "[1, 2, 3] site < [2, 3, 4] site"] of
          Left err -> T.isInfixOf "no ordering on Point site" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "points compare and have no sum" $ do
        evalP "20 degC < (70 degF to degC)" @?= Right ["true"]
        evalP "20 degC == (68 degF to degC)" @?= Right ["true"]
        evalP "0 J2000 < (0 MJD to J2000)" @?= Right ["false"]
        typeOfTextP "20 degC" @?= Right "Point degC"
        typeOfTextP "degC" @?= Right "Chart degC"
        typeOfTextP "\\p q -> p .- q"
          @?= Right "forall c. Point c -> Point c -> Diff c"
        typeOfTextP "\\p v -> p .+ v"
          @?= Right "forall c. Point c -> Diff c -> Point c"
        typeOfTextP "\\a b -> a < b" @?= Right "forall d. Num d -> Num d -> Bool"
        case evalP "20 degC + 5 degC" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "2 * (20 degC)" of
          Left err -> T.isInfixOf "a point has no sum" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "20 degC to K" of
          Left err -> T.isInfixOf "to with a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
        case evalP "[1, 2] < [1, 3]" of
          Left err -> T.isInfixOf "no ordering on Vec 2" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "chart declarations: user charts, :view and :edit read back as written" $ do
        runLinesP
          [ "unit mmHg = 133.322 Pa"
          , "space ISA = Num Pa"
          , "chart bp on ISA step mmHg"
          , "120 bp .+ 10 mmHg"
          , "(120 bp .- 80 bp)"
          ]
          @?= Right ["130 bp", "40 mmHg"]
        runLinesP ["let boil = 100 degC", ":view boil"] @?= Right ["boil = 100 degC"]
        -- The library lives in namespaces, so :edit prints its definitions in their block.
        runLinesP [":edit degC"]
          @?= Right ["namespace temperature", "  chart degC on ITS90 at 273.15 K"]
        runLinesP [":edit km"]
          @?= Right ["namespace si", "  unit km = kilo * 1 metre"]
    , testCase
        "chart is a keyword: a declaration, its type, :view and :ls"
        $ do
          runLinesP
            [ "unit mmHg = 133.322 Pa"
            , "space ISA = Num Pa"
            , "chart bp on ISA step mmHg"
            , "120 bp .+ 10 mmHg"
            , ":type bp"
            , ":view bp"
            , ":ls --charts bp"
            , "bp"
            ]
            @?= Right
              [ "130 bp"
              , "Chart bp"
              , "chart bp on ISA step mmHg"
              , "chart bp : Chart bp"
              , "chart bp"
              ]
          typeOfTextP "\\c -> (c :: Chart degC)"
            @?= Right "Chart degC -> Chart degC"
          -- `chart` is a keyword, not a name.
          case runLinesP ["let chart = 3"] of
            Left _ -> pure ()
            Right v -> assertFailure (show v)
          expectError
            (runLinesP ["chart bp at 0 K"])
            "name its space: `chart … on ITS90`"
    , testCase
        "mkRoot and mkChart: a frame, a parent, a list of generators, antisymmetry"
        $ do
          let inertial = "space GCRS = Vec 3 m"
              eci = "chart eci on GCRS"
          -- A chart's frame is its declaration's (design §3.10, F3): the
          -- primitive takes the minted constructor no source can write.
          expectError
            (runLinesP [inertial, eci, "data Eci = Eci", "mkChart {Eci} {} eci {} {} {} {}"])
            "mkChart takes the frame a chart declaration mints first"
          typeOfTextP "rotationOf"
            @?= Right "forall s (c : s). Chart c -> Mat s c"
          -- A generator: exact, or scaled by an approximate angle, is a bivector.
          let turnedBy gs = [inertial, eci, "chart t on eci at [1, 0, 0] m by " <> gs, "[0, 0, 0] t"]
          runLinesP (turnedBy "[0, -1, 0; 1, 0, 0; 0, 0, 0]") @?= Right ["[0, 0, 0] t"]
          runLinesP (turnedBy "[0, -1, 0; 1, 0, 0; 0, 0, 0] * pi / 6")
            @?= Right ["[0, 0, 0] t"]
          let refused lines' needle = case runLinesP lines' of
                Left err -> T.isInfixOf needle err @? T.unpack err
                Right v -> assertFailure (show v)
          refused
            (turnedBy "[0, 1, 0; 1, 0, 0; 0, 0, 0]")
            "the generator of a chart must be antisymmetric: a bivector, such as rotz θ or a ∧ b"
          -- Every generator of the list is checked.
          refused
            (turnedBy "rotz (30 deg) then [1, 0, 0; 0, 0, 0; 0, 0, 0]")
            "must be antisymmetric"
          -- The type cannot tell a turned chart from another, so `rotationOf`
          -- is exactly the identity on one that is not turned.
          runLinesP [inertial, eci, "rotationOf eci == [1, 0, 0; 0, 1, 0; 0, 0, 1]"]
            @?= Right ["true"]
          -- The parent's dimension and shape, and the generator's size, are the child's.
          refused
            [inertial, eci, "chart k on eci at 0 K"]
            "expected Vec GCRS m, got Num K"
          refused [inertial, eci, "chart k on eci at [1, 2] m"] "lengths differ: 3 and 2"
          refused (turnedBy "[0, 1; -1, 0]") "lengths differ: 3 and 2"
          -- A space of numbers has no axes to turn.
          refused
            ["chart tilt on degC by rotz (30 deg)"]
            "a chart on a space of numbers has no axes to turn"
    , testCase "charts with a parent: the translated tree, to and .- through it" $ do
        -- design §3.8's hierarchy without the rotations
        let tree =
              [ "space GCRS = Vec 3 m"
              , "chart eci on GCRS"
              , "chart site on eci at [6378, 0, 0] km"
              , "chart antenna on site at [2, 0, 1] m"
              ]
        runLinesP
          ( tree
              ++ [ "[1, 2, 3] antenna to eci"
                 , "([1, 2, 3] antenna to eci) to antenna"
                 , "[0, 0, 0] antenna to site"
                 , "[1, 2, 3] antenna .- [0, 0, 0] site on site"
                 , "([1, 2, 3] antenna to eci) == [6378003, 2, 4] eci"
                 , ":type antenna"
                 , ":view antenna"
                 , ":view site"
                 , ":ls --charts antenna"
                 , ":edit antenna"
                 , -- a temperature scale is untouched
                   "20 degC to degF"
                 , "77 °F .- 68 °F"
                 ]
          )
          @?= Right
            [ "[6378003, 2, 4] eci"
            , "[1, 2, 3] antenna"
            , "[2, 0, 1] site"
            , "[3, 2, 4] m"
            , "true"
            , "Chart antenna"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart site on eci at [6378, 0, 0] km"
            , "chart antenna : Chart antenna"
            , "chart antenna on site at [2, 0, 1] m"
            , "68 degF"
            , "9 deltaF"
            ]
        -- Two roots on one space have one set of axes and convert (design
        -- §3.10, F2); their points never mix unconverted.
        runLinesP
          ( tree
              ++ ["chart pad on GCRS at [6378000, 10, 0] m", "[1, 2, 3] antenna to pad"]
          )
          @?= Right ["[3, -8, 4] pad"]
        expectError
          ( runLinesP
              (tree ++ ["chart pad on GCRS", "[1, 2, 3] antenna .- [0, 0, 0] pad"])
          )
          "points on antenna and pad: convert one with `to`"
        -- :edit reads back to the same hash.
        let hashAfter def = runLinesP (take 3 tree ++ [def, ":hash antenna"])
        expecting (runLinesP (tree ++ [":edit antenna"])) $ \outs ->
          hashAfter (last outs) @?= hashAfter (tree !! 3)
        -- An origin that is a name, or an expression, runs to the next clause.
        runLinesP
          ( tree
              ++ [ -- a named value has a frame only when given one (design §3.9)
                   "let r0 = withAxes eci ([1, 0, 0] km)"
                 , "chart c1 on eci at r0"
                 , "chart c2 on site at r0 + r0"
                 , "[0, 0, 0] c1 to eci"
                 , "[0, 0, 0] c2 to eci"
                 , ":view c1"
                 , ":view c2"
                 ]
          )
          @?= Right
            [ "[1000, 0, 0] eci"
            , "[6380000, 0, 0] eci"
            , "chart c1 on eci at r0"
            , "chart c2 on site at r0 + r0"
            ]
        -- The parent's dimension is the child's.
        expectError
          (runLinesP (tree ++ ["chart t on site at 3 K", "t"]))
          "expected Vec GCRS m, got Num K"
        runLinesP ["chart warm on ITS90 at 300 K", "0 warm to degC"]
          @?= Right ["26.85 degC"]
    , testCase
        "a chart turned by a generator: by and then parse, and read back as written"
        $ do
          let eci = multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]
              turn = "[0, -1, 0; 1, 0, 0; 0, 0, 0]"
          runLinesP
            [ eci
            , "chart lvlh on eci by " <> turn
            , ":view lvlh"
            , ":type lvlh"
            ]
            @?= Right ["chart lvlh on eci by " <> turn, "Chart lvlh"]
          -- `by` runs to the next clause, so the generator is a whole expression.
          runLinesP
            [ eci
            , "chart lvlh on eci by " <> turn <> " * pi / 6"
            , ":view lvlh"
            ]
            @?= Right ["chart lvlh on eci by " <> turn <> " * pi / 6"]
          -- Several generators, applied in order, separated by `then`; an `if`
          -- inside one keeps its own `then`.
          runLinesP
            [ eci
            , "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
            , ":view pf"
            , "chart odd on eci by (if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
            , ":view odd"
            ]
            @?= Right
              [ "chart pf on eci by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)"
              , "chart odd on eci by (if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
              ]
          let hashOfChart c = runLinesP [eci, "chart odd on eci by " <> c, ":hash odd"]
          hashOfChart "if 1 < 2 then rotz (1 deg) else rotx (1 deg) then rotx (2 deg)"
            @?= hashOfChart "(if 1 < 2 then rotz (1 deg) else rotx (1 deg)) then rotx (2 deg)"
          -- Clauses come in any order and read back in one.
          hashOfChart "rotz (1 deg)"
            @?= runLinesP [eci, "chart odd on eci by rotz (1 deg)", ":hash odd"]
          runLinesP [eci, "chart o2 on eci step km at [1, 0, 0] m", ":view o2"]
            @?= Right ["chart o2 on eci at [1, 0, 0] m step km"]
          -- A coordinate of a point on a turned chart is along the chart's own
          -- axes (design §3.10, F5).
          let lvlh = "chart lvlh on eci by " <> turn
          runLinesP
            [ eci
            , lvlh
            , "([1, 2, 3] lvlh).0"
            , "([1, 2, 3] lvlh .- [0, 0, 0] lvlh) == [1, 2, 3] m"
            ]
            @?= Right ["1 m", "true"]
          expectError
            ( runLinesP
                [eci, "chart bad on eci by [0, 1, 0; 1, 0, 0; 0, 0, 0]", "bad"]
            )
            "the generator of a chart must be antisymmetric: a bivector, such as rotz θ or a ∧ b"
          -- A root may be turned too: its axes are its own.
          runLinesP
            [ eci
            , "chart free on GCRS by " <> turn
            , ":type [1, 2, 3] free .- [0, 0, 0] free"
            ]
            @?= Right ["Vec free m"]
          -- `by` stays a name everywhere else, and inside brackets here.
          runLinesP
            [ eci
            , "let by = 5"
            , "by + 1"
            , "chart c on eci at [by, 0, 0] m"
            , "[0, 0, 0] c to eci"
            ]
            @?= Right ["6", "[5, 0, 0] eci"]
          expectError
            (runLinesP [eci, "chart c on eci at [1, 0, 0] m at [2, 0, 0] m"])
            "a chart has one `at` clause"
    , testCase
        "charts in a namespace block resolve their parent; the parent survives :export"
        $ do
          let block =
                multiline
                  [ "namespace frames"
                  , "  space GCRS = Vec 3 m"
                  , "  chart eci on GCRS"
                  , "  chart site on eci at [6378, 0, 0] km"
                  , "  chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
                  ]
          runLinesP [block, "[1, 2, 3] frames.site to frames.eci", ":view frames.lvlh"]
            @?= Right
              [ "[6378001, 2, 3] frames.eci"
              , "chart frames.lvlh on frames.site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
              ]
          original <- either (assertFailure . T.unpack) pure (sessionP [block, ":add"])
          source <-
            either (assertFailure . T.unpack) pure (exportSource original (Just "frames"))
          reloaded <-
            either (assertFailure . T.unpack) pure (sessionP [source, ":add"])
          reloaded.codebase.names @?= original.codebase.names
          reloaded.codebase.charts @?= original.codebase.charts
          reloaded.codebase.typeNames @?= original.codebase.typeNames
    , testCase "display units of one dimension cancel against each other" $ do
        evalP "2 m * 90 deg / rad" @?= Right ["3.1415926535897932384… m"]
        evalP "3 h / min" @?= Right ["180"]
        evalP "1 km / m" @?= Right ["1000"]
        evalP "(2 km)^2 / 1 m" @?= Right ["4000 km"]
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
           in within caseLimit (abs (at x * at y - midpoint z) <= radius z)
    , testProperty "the integer square root under sqrt is the floor of the root"
        $ \(Positive a) (NonNegative k) ->
          -- a long integer, as an uncertain value's endpoints become
          let n = (a :: Integer) * 7 ^ (k `mod` 400 :: Int)
              s = isqrt n
           in within caseLimit (s * s <= n && n < (s + 1) * (s + 1))
    , -- A generated case that once took ten seconds: the integer square
      -- root started Newton's method from n itself, one step per halving
      -- of a numerator thousands of bits long.
      localOption (mkTimeout 3_000_000)
        . testCase "sqrt of a long rational is fast"
        $ case evalText "sqrt ((7 / cos (-4 rad))^2)" of
          Right [v] -> T.isPrefixOf "10.70919959526478302" v @? T.unpack v
          other -> assertFailure (show other)
    , -- Newton's method for Kepler's equation took ten times longer with
      -- every step (four steps took 110 s): nothing shortened the
      -- coefficients and remainders a non-linear operation produced, and a
      -- value fed back into several places multiplied their length.
      localOption (mkTimeout 5_000_000)
        . testCase "Newton's method for Kepler's equation iterates quickly"
        $ runLinesP [keplerIter, keplerAt 12]
          @?= Right ["220.51207476752206740… deg"]
    , localOption (mkTimeout 20_000_000)
        . testCase "an iteration's cost grows linearly with its steps"
        $ do
          let timed k = do
                start <- getPOSIXTime
                out <- evaluate (runLinesP [keplerIter, keplerAt k])
                _ <- evaluate (either T.length (sum . map T.length) out)
                end <- getPOSIXTime
                out @?= Right ["220.51207476752206740… deg"]
                pure (end - start)
          t10 <- timed 10
          t20 <- timed 20
          -- linear is 2; the suite runs tests in parallel, so allow noise
          t20 < 5 * t10 @? "10 steps took " <> show t10 <> ", 20 took " <> show t20
    , localOption (mkTimeout 10_000_000)
        . testCase "an iteration's rationals stay short"
        $ do
          let p = 24
              meanAnomaly =
                uncertain
                  Stat
                  (Tagged "m" 0)
                  (mulM p (Exact (1177 / 5)) (scaleM p (1 / 180) (piM p)))
                  (Exact (1 / 1000))
              step ea = do
                let e = Exact (2 / 5)
                    residual = subM p (subM p ea (mulM p e (sinM p ea))) meanAnomaly
                    den = subM p (Exact 1) (mulM p e (cosM p ea))
                subM p ea <$> divM p residual den
              steps k = foldM (\ea _ -> step ea) meanAnomaly [1 .. k :: Int]
          case (longestRational <$> steps 10, longestRational <$> steps 40) of
            (Right l10, Right l40) ->
              l40 <= 2 * l10 @? "10 steps: " <> show l10 <> " digits; 40: " <> show l40
            other -> assertFailure (show other)
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
           in within caseLimit . counterexample (show (r, v))
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
    m@(Affine mid _ _ _) -> mid + sum [c * eOf n | (c, n) <- nudges m]
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
        $ timedForAll (snd <$> genProgram)
        $ \e -> case desugarClosed noResolver e of
          Left _ -> discard
          Right (t, _) -> case decodeStored (encodeStored t) of
            Left err -> counterexample (T.unpack err) False
            Right t' ->
              counterexample
                (show t')
                (alphaEq t t' && encodeStored t' == encodeStored t && hashTerm t' == hashTerm t)
    , testCase "a chart's parent and generator survive a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ "space GCRS = Vec 3 m"
            , "chart eci on GCRS"
            , "chart site on eci at [6378, 0, 0] km"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
            , ":add"
            ]
        (loaded, notes) <- reload dir
        notes @?= []
        loaded.codebase.names @?= s.codebase.names
        loaded.codebase.charts @?= s.codebase.charts
        loaded.codebase.typeNames @?= s.codebase.typeNames
        linesIn
          loaded
          [ "[1, 2, 3] antenna to eci"
          , ":view antenna"
          , ":view lvlh"
          , ":type [1, 2, 3] lvlh"
          ]
          @?= Right
            [ "[6378003, 2, 4] eci"
            , "chart antenna on site at [2, 0, 1] m"
            , "chart lvlh on site by [0, -1, 0; 1, 0, 0; 0, 0, 0]"
            , "Point lvlh"
            ]
    , testCase "definitions, history, units, labels and cycles survive a reload" $ withTempStore $ \dir -> do
        s <-
          persistLines
            dir
            [ "let speed = 5 km / h"
            , ":prefer kPa"
            , "unit furlong = 201.168 m"
            , "let r = 10 mm ± 0.01 mm #batch7"
            , "let even n = if n == 0 then true else odd (n - 1); let odd n = if n == 0 then false else even (n - 1)"
            , "unit mmHg = 133.322 Pa"
            , "space ISA = Num Pa"
            , "chart bp on ISA step mmHg"
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
        loaded.codebase.charts @?= s.codebase.charts
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
            , -- These changed when km became kilo * metre and h an alias of hr,
              -- and when km was respelled kilo * 1 metre (design §3.10, U3), and
              -- again when units became a type: speed is the quantity 5 (km/h),
              -- scale of a unit quotient, and km and h are units by declaration.
              "#av4qv  (current)"
            , "#01d73"
            , "201.168 m"
            , "0 mm"
            , "true"
            , "false"
            , "r = 10 mm ± 0.01 mm #batch7"
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
          loaded.codebase.charts @?= s.codebase.charts
          loaded.codebase.uses @?= [S.Use u Nothing | u <- stdlibDefaultUses]
          linesIn loaded ["d", "astro.G"]
            @?= Right ["3 km", "6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2"]
          -- The seed is at time 0, before the user's lines.
          ls <- T.lines <$> TIO.readFile (dir </> "names.log")
          all (\u -> ("0 use " <> u) `elem` ls) stdlibDefaultUses
            @? "the stored uses are log lines"
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
            @?= withBuiltinTypes
              ( [ "[1, 0; 0, 1] m^2"
                , "[0, 0; 0, 0] m s"
                , "Cov2 {rr = [1, 0; 0, 1] m^2, rv = [0, 0; 0, 0] m s, vv = [1, 0; 0, 1] s^2}"
                , "rr [1, 0; 0, 1] m^2"
                , "rv [0, 0; 0, 0] m s"
                , "vv [1, 0; 0, 1] s^2"
                , "bound box ([0, 0] m, [0, 0] s)"
                ]
                  ++ astroTypes
                  ++ [ "data Cov2 n d d1 = Cov2 {rr :: Mat n n (d^2), rv :: Mat n n (d*d1), vv :: Mat n n (d1^2)}"
                     , "Cov2 : forall n d d1. Mat n n (d^2) -> Mat n n (d*d1) -> Mat n n (d1^2) -> Cov2 n d d1"
                     ]
              )
    , testCase
        "a root binding shadows the library's on reload; :use and :unuse persist"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir ["let c = 3e8 m / s", ":add", ":use physics", ":unuse si"]
          (loaded, _) <- reload dir
          loaded.codebase.uses
            @?= [S.Use u Nothing | u <- filter (/= "si") stdlibDefaultUses ++ ["physics"]]
          linesIn loaded ["c", "physics.c", "1 si.km", ":use si", "1 km"]
            @?= Right
              ["300000000 m s^-1", "299792458 m s^-1", "1 si.km", "stored use si", "1 km"]
          ls <- T.lines <$> TIO.readFile (dir </> "names.log")
          any (" unuse si" `T.isSuffixOf`) ls @? "an unuse line"
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
              [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
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
                , "  unit au = 149597870700 m"
                , "  space Distance = Num m"
                , "  chart tip on Distance step au"
                , "  data Body = Body {mass :: Num kg, dist :: Num m}"
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
        -- A chart re-hashes when it moves, its frame stamped with its path
        -- (design §3.10); the log keeps its new version, not the step between.
        let settled = Map.adjust (take 1) "mechanics.tip"
        settled loaded.codebase.history @?= settled s.codebase.history
        loaded.codebase.units @?= s.codebase.units
        loaded.codebase.charts @?= s.codebase.charts
        loaded.codebase.typeNames @?= s.codebase.typeNames
        loaded.codebase.conNames @?= s.codebase.conNames
        loaded.codebase.fieldNames @?= s.codebase.fieldNames
        Map.member "celestial.kepler.anomaly" loaded.codebase.names @? "renamed"
        Map.member "mechanics.mass" loaded.codebase.fieldNames @? "field path"
        Set.member "mechanics.au" loaded.codebase.units @? "unit path"
        Set.member "mechanics.tip" loaded.codebase.charts @? "chart path"
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
          Left err -> T.isInfixOf "`dozen` is a Num, not a unit or a chart" err @? T.unpack err
          Right v -> assertFailure (show v)
    , testCase "a type indexed by rank survives a reload" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["data Idx s = Idx (Vec (rank s))", ":add"]
        (loaded, notes) <- reload dir
        notes @?= []
        linesIn loaded [":view Idx", ":type Idx [0, 1, 2]"]
          @?= Right ["data Idx s = Idx (Vec (rank s))", "forall n m k. Idx [n, m, k]"]
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
    , testCase "a store of another format is refused with one line and left as it is"
        $ withTempStore
        $ \dir -> do
          _ <- persistLines dir ["let x = 1", ":add"]
          writeFile (dir </> "format") "metron codebase 10\n"
          before <- snapshot dir
          entries <- sort <$> listDirectory dir
          opened <- openStore theSeed dir
          case opened of
            Left err ->
              err
                @?= T.pack dir <> ": this codebase is format 10; this metron opens format 12"
            Right _ -> assertFailure "opened a store of another format"
          snapshot dir >>= (@?= before)
          listDirectory dir >>= (@?= entries) . sort
    , testCase "a store of the current format opens as it was seeded" $ withTempStore $ \dir -> do
        _ <- persistLines dir ["let x = 1", ":add"]
        readFile (dir </> "format")
          >>= (@?= "metron codebase " <> show formatVersion <> "\n")
        formatVersion @?= 12
        before <- snapshot dir
        (loaded, notes) <- reload dir
        notes @?= []
        -- Opening it writes nothing: it is not seeded again.
        snapshot dir >>= (@?= before)
        loaded.codebase.uses @?= [S.Use u Nothing | u <- stdlibDefaultUses]
        linesIn loaded ["x", "1 km"] @?= Right ["1", "1 km"]
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
              [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
              , "data Body = Body {mass :: Num kg}"
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
              ["1", "2 kg", "data Shape = Circle (Num m) | Rect (Num m) (Num m)"]
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
        "merging from what is not a store, or from a store of another format, is refused and touches nothing"
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
          refused plain "is not a metron codebase"
          listDirectory plain >>= (@?= ["notes.txt"])
          refused (root </> "missing") "no such directory"
          doesDirectoryExist (root </> "missing") >>= (@?= False)
          _ <- persistLines (root </> "future") ["let x = 1", ":add"]
          writeFile (root </> "future" </> "format") "metron codebase 99\n"
          refused
            (root </> "future")
            "this codebase is format 99; this metron opens format 12"
          readFile (root </> "future" </> "format") >>= (@?= "metron codebase 99\n")
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

-- | A fresh store directory for the length of a test.
withTempStore :: (FilePath -> IO a) -> IO a
withTempStore k = do
  tmp <- getTemporaryDirectory
  stamp <- getPOSIXTime
  let dir = tmp </> ("metron-test-" <> show (round (stamp * 1000000) :: Integer))
  createDirectoryIfMissing True dir
  r <- k dir
  removePathForcibly dir
  pure r

-- | Feed lines one at a time, persisting after each, as Main does.
persistLines :: FilePath -> [Text] -> IO Session
persistLines dir ls = do
  st <- either (error . T.unpack) id <$> openStore theSeed dir
  let go s [] = pure s
      go s (l : rest) = case feed s l of
        Left err -> error (T.unpack err)
        Right (s', _) -> sync st s.codebase s'.codebase >> go s' rest
  go seeded ls

-- | A session on the store as Main opens it.
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

-- | The output of lines fed to a session in turn.
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
        runLinesP [":set unicode on", ":type \\x -> x"] @?= Right ["forall a. a → a"]
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

-- | Text in an SGR colour, as "Metron.Repl" paints it.
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
                $ sessionP ["data Shape = Circle (Num m) | Rect (Num m) (Num m)"]
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
          [ "data Shape = Circle (Num m) | Rect (Num m) (Num m)"
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
      $ sessionP ["data Shape = Circle (Num m) | Rect (Num m) (Num m)"]
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
      , "unit furlong = 201.168 m"
      , "namespace orbital"
      , "  data Body = Body {mass :: Num kg, dist :: Num m}"
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
  a.charts @?= b.charts

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
        -- The same body under another keyword is another term: a unit's
        -- declaration makes its body a unit (design §3.10, U7).
        plain <- editFileOf s [] >>= replaceOnce "unit furlong" "let furlong"
        (s2, outs2) <- edited EditCodebase plain s
        outs2 @?= [movedLine "updated" s s2 "furlong"]
        expectError
          (snd <$> feed s2 "2 furlong")
          "`furlong` is a Num m, not a unit or a chart"
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
              >>= replaceOnce "dist :: Num m}" "dist :: Num s}"
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
              >>= replaceOnce "dist :: Num m}" "dist :: Num m, spin :: Num}"
              >>= replaceOnce "Body (6 kg) (1 km)" "Body (6 kg) (1 km) 3"
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
              >>= replaceOnce "dist :: Num m}" "dist :: Num m, spin :: Num}"
          (_, outs3) <- edited (EditName "orbital.Body") added s
          -- The two users left, in an order their hashes decide.
          take 1 outs3 @?= ["updated data orbital.Body"]
          sort (map (T.takeWhile (/= '#')) (drop 1 outs3))
            @?= ["left orbital.earth on ", "left orbital.weight on "]
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
    , testCase "(j) :edit si includes the library; :edit alone never touches it" $ do
        s <- editSession
        file <- editFileOf s ["si"]
        ("unit km = kilo * 1 metre" `T.isInfixOf` file) @? "si.km is in the file"
        file' <-
          replaceOnce "unit km = kilo * 1 metre\n" "unit km = 1001 m\n" file
        (s', outs) <- edited (EditNamespace "si") file' s
        -- The library's own users in si are in the file; the others are
        -- propagated, the user's and astro.de440's bodies (written in km),
        -- independent ones in an order their hashes decide.
        take 1 outs @?= [T.replace "si.km" "km" (movedLine "updated" s s' "si.km")]
        sort (drop 1 outs)
          @?= sort
            ( [ movedLine "upgraded" s s' "orbital.earth"
              , movedLine "upgraded" s s' "trip"
              ]
                ++ [ movedLine "upgraded" s s' ("astro.de440." <> b)
                   | b <-
                       [ "sun"
                       , "mercury"
                       , "venus"
                       , "earth"
                       , "moon"
                       , "mars"
                       , "jupiter"
                       , "saturn"
                       , "uranus"
                       , "neptune"
                       , "pluto"
                       ]
                   ]
            )
        snd <$> feed s' "trip to m" @?= Right ["2002 m"]
        -- The codebase without the library: nothing under si is removed.
        plain <- editFileOf s []
        ("unit km" `T.isInfixOf` plain) @?= False
        changed <- replaceOnce "let size = 10\n" "let size = 11\n" plain
        (s2, _) <- edited EditCodebase changed s
        let underSi c = Map.filterWithKey (\k _ -> "si." `T.isPrefixOf` k) c.names
        underSi s2.codebase @?= underSi s.codebase
    , testCase "(k) :edit --file resumes from a file" $ do
        s <- editSession
        dir <- getTemporaryDirectory
        let path = dir </> "metron-edit-test.metron"
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

stdlibTests :: TestTree
stdlibTests =
  testGroup
    "standard library"
    [ testCase "a name outside the namespaces used by default needs its namespace" $ do
        let inDefault n = any (\u -> (u <> ".") `T.isPrefixOf` n) stdlibDefaultUses
            defaultLast = Set.fromList (map S.lastSegment (filter inDefault stdlibNames))
            outside =
              Set.toList
                ( Set.fromList (map S.lastSegment (filter (not . inDefault) stdlibNames))
                    `Set.difference` defaultLast
                )
        -- The constants and AU among them (design §7.7).
        all (`elem` outside) ["AU", "G", "c", "planck", "g0"] @? show outside
        forM_ outside $ \n ->
          qualifyName TermLabel S.rootScope seeded.codebase n @?= NotFound
    , testCase "no name is ambiguous among the namespaces used by default" $ do
        let cb = seeded.codebase
            used n = any (\u -> (u <> ".") `T.isPrefixOf` n) stdlibDefaultUses
            check kind labels =
              forM_ (filter used labels) $ \n ->
                qualifyName kind S.rootScope cb (S.lastSegment n) @?= Found n
        check TermLabel (Map.keys cb.names ++ Map.keys cb.conNames)
        check TypeLabel (Map.keys cb.typeNames)
        check FieldLabel (Map.keys cb.fieldNames)
        -- The labels are the ones the source and its aliases declare.
        sort
          ( Map.keys cb.names
              ++ Map.keys cb.conNames
              ++ Map.keys cb.fieldNames
              -- A chart's frame is named as the chart (design §3.10, F3).
              ++ Map.keys (Map.difference (Map.difference cb.typeNames cb.conNames) cb.names)
          )
          @?= sort stdlibNames
    , testCase "a ± definition is stamped with its full path: astro.G is not a root G" $ do
        expecting (runLinesP [":use astro", ":hash G", ":hash astro.G"]) $ \case
          [_, g, astroG] -> g @?= astroG
          outs -> assertFailure (show outs)
        expecting
          ( runLinesP
              [ "let G = (6.67430e-11 ±σ 1.5e-15) * 1 m^3 kg^-1 s^-2"
              , ":add"
              , ":hash G"
              , ":hash astro.G"
              ]
          )
          $ \outs -> case lastN 2 outs of
            [g, astroG] -> (astroG /= g) @? "astro.G differs from the root G"
            other -> assertFailure (show other)
    , testCase "std names Bool, Pair and List, the declarations the compiler holds" $ do
        let cb = seeded.codebase
        lookupTypeName "std.Bool" cb @?= Just boolHash
        lookupTypeName "std.Pair" cb @?= Just pairHash
        lookupTypeName "std.List" cb @?= Just listHash
        Map.lookup boolHash cb.typeDefs @?= Just boolDef
        Map.lookup pairHash cb.typeDefs @?= Just pairDef
        Map.lookup listHash cb.typeDefs @?= Just listDef
        map
          (`lookupConName` cb)
          ["std.False", "std.True", "std.Pair", "std.Nil", "std.Cons"]
          @?= map
            (Just . (\(UserCon t i) -> (t, i)))
            [falseC, trueC, pairC, nilC, consC]
        runLinesP
          [ ":view std.Bool"
          , ":view std.Pair"
          , ":view std.List"
          , "true"
          , "True"
          , "std.False"
          , "Pair 1 2"
          , "Cons 1 (Cons 2 Nil)"
          , "if True then (1, {}) else (2, Cons 3 Nil)"
          , ":type Cons"
          , "case (1, true) of Pair a b -> if b then a else 0"
          ]
          @?= Right
            [ "structural data Bool = False | True"
            , "structural data Pair a b = Pair a b"
            , "structural data List a = Nil | Cons a (List a)"
            , "true"
            , "true"
            , "false"
            , "(1, 2)"
            , "{1, 2}"
            , "(1, {})"
            , "forall a. a -> {a} -> {a}"
            , "1"
            ]
    , testCase "the built-in types print by hash, whatever names them" $ do
        -- Renamed or unnamed, Bool is still Bool, and true still true.
        runLinesP
          [ ":rename std.Bool std.Truth"
          , ":rename std.True std.Yes"
          , "Yes"
          , ":type Yes"
          , ":unname std.List"
          , ":type {1}"
          , "(1, 2, 3, 4)"
          , ":type (1, true, {}, (2, 3))"
          ]
          @?= Right
            [ "renamed `std.Bool` to `std.Truth`"
            , "renamed `std.True` to `std.Yes`"
            , "true"
            , "Bool"
            , "removed the label `std.List`"
            , "{Num}"
            , "(1, 2, 3, 4)"
            , "forall a. (Num, Bool, {a}, (Num, Num))"
            ]
        -- The same declarations entered by a user are the same types.
        let mine =
              [ multiline
                  [ "namespace mine"
                  , "  structural data Bool = False | True"
                  , "  structural data Couple a b = Couple a b"
                  ]
              , ":add"
              ]
        s <- either (assertFailure . T.unpack) pure (sessionP mine)
        lookupTypeName "mine.Bool" s.codebase @?= Just boolHash
        lookupTypeName "mine.Couple" s.codebase @?= Just pairHash
        expecting
          ( runLinesP
              ( mine
                  ++ ["mine.True", "mine.Couple 1 true", "(1, true) == mine.Couple 1 mine.True"]
              )
          )
          $ \outs -> lastN 3 outs @?= ["true", "(1, true)", "true"]
        -- A structural type of Bool's shape is Bool.
        expecting
          (runLinesP ["structural data Color = Red | Green", "Red", ":type Green"])
          $ \outs -> lastN 2 outs @?= ["false", "Bool"]
        expectError (runLinesP ["data Bool = Yes | No"]) "`Bool` is a built-in type"
        expectError
          (evalP ("(" <> T.intercalate ", " (replicate 33 "1") <> ")"))
          "a tuple has at most 32 components"
    , testCase "units resolve through the stored uses and print bare" $ do
        evalP "5 km" @?= Right ["5 km"]
        runLinesP ["5 si.km", "1 km to m", "3 degC", "2 time.h"]
          @?= Right ["5 km", "1000 m", "3 degC", "2 h"]
        runLinesP [":type astro.G"] @?= Right ["Num (m^3/(kg*s^2))"]
        expectError (evalP "G") "unknown name `G`"
        evalU ["astro"] "1 AU to km" @?= Right ["149597870.7 km"]
    , testCase ":ls alone shows the root and a line per namespace; :ls si the SI" $ do
        runLinesP [":ls"] @?= Right libraryListing
        expecting (runLinesP [":ls si"]) $ \outs -> do
          length outs @?= librarySize "si"
          ("unit km : Unit m" `elem` outs) @? "km"
          ("unit newton : Unit (kg*m/s^2)" `elem` outs) @? "newton"
          ("kilo : Num" `elem` outs) @? "kilo"
        expecting (runLinesP [":ls temperature"]) $ \outs ->
          ("chart degC : Chart degC" `elem` outs) @? "degC"
        -- :ls lists a type and its constructor on two lines and no fields:
        -- linalg.Cov2, astro.State and std.Pair are one label and two lines
        -- each, the three fields of Cov2 and of State none.
        expecting (runLinesP [":ls linalg"]) $ \outs ->
          length outs @?= librarySize "linalg" + 1 - 3
        expecting (runLinesP [":ls --all"]) $ \outs -> do
          ("unit si.km : Unit m" `elem` outs) @? "full paths with --all"
          -- six records (Cov2, Pair, and astro's State, Body, Elements and
          -- Transfer) list two lines for one label, and their 21 fields none
          length outs @?= length stdlibNames + 6 - 21
        runLinesP [":ls --units furl"] @?= Right ["nothing matches"]
    , testCase "a root name shadows the library's: c and physics.c" $ do
        runLinesP
          [":use physics", "let c = 3e8 m/s", "c", "physics.c", ":add", "c", "physics.c"]
          @?= Right
            [ "stored use physics"
            , "300000000 m s^-1"
            , "299792458 m s^-1"
            , "added c"
            , "300000000 m s^-1"
            , "299792458 m s^-1"
            ]
        expecting
          ( runLinesP
              [":use physics", "let c = 3e8 m/s", "let x = c + physics.c", ":add", ":view x"]
          )
          $ \outs ->
            last outs @?= "x = c + physics.c"
    , testCase "library names are names: :rename, :unname, :edit" $ do
        runLinesP [":rename time.hr time.hour", "3 hour", "2 hour + 30 min", "3 h"]
          @?= Right ["renamed `time.hr` to `time.hour`", "3 hour", "150 min", "3 h"]
        expectError
          (runLinesP [":rename time.hr time.hour", "3 hr"])
          "unknown name `hr`"
        expectError
          (runLinesP [":use astro", ":unname astro.AU", "1 AU"])
          "unknown name `AU`"
        runLinesP [":edit si.km"]
          @?= Right ["namespace si", "  unit km = kilo * 1 metre"]
    , testCase ":uses, :unuse and :use for the stored uses" $ do
        let stored = ["use " <> u <> " (stored)" | u <- stdlibDefaultUses]
            withoutSi = ["use " <> u <> " (stored)" | u <- stdlibDefaultUses, u /= "si"]
        runLinesP [":uses"] @?= Right stored
        runLinesP [":unuse si", ":uses"]
          @?= Right ("removed the stored use si; :use si puts it back" : withoutSi)
        expectError (runLinesP [":unuse si", "5 km"]) "unknown name `km`"
        runLinesP [":unuse si", "5 si.km", ":use si", "5 km", ":uses"]
          @?= Right
            ( [ "removed the stored use si; :use si puts it back"
              , "5 si.km"
              , "stored use si"
              , "5 km"
              ]
                ++ withoutSi
                ++ ["use si (stored)"]
            )
        expectError (runLinesP [":use si"]) "use si is already stored"
        -- A session use and a stored one of the same path: the stored goes first.
        runLinesP ["use si", ":uses", ":unuse si", ":uses", ":unuse si", ":uses"]
          @?= Right
            ( stored
                ++ ["use si", "removed the stored use si; :use si puts it back"]
                ++ withoutSi
                ++ ["use si"]
                ++ withoutSi
            )
        -- The scratch must still check without it.
        expectError
          (runLinesP ["let d = 2 km", ":unuse si"])
          "the pending definitions would not check"
        -- × is the library's cross, so it needs linalg.
        evalP "[1, 0, 0] × [0, 1, 0]" @?= Right ["[0, 0, 1]"]
        expectError (runLinesP [":unuse linalg", "[1, 0, 0] × [0, 1, 0]"]) "cross"
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
                [ multiline ["namespace astro", "  let G = 1", "  let gone = 3"]
                , multiline ["namespace physics", "  let c = 2"]
                , ":add"
                , multiline ["namespace physics", "  let c = 5"]
                , "let twice = astro.G * 2"
                , ":update"
                ]
            )
        case stdlibUpgrade lib old of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added si.km" `elem` outs) @? "km added"
            ("added astro.AU" `elem` outs) @? "AU added"
            any ("updated astro.G " `T.isPrefixOf`) outs @? "G updated"
            ("kept physics.c (yours)" `elem` outs) @? "c kept"
            any ("upgraded twice " `T.isPrefixOf`) outs @? "twice upgraded"
            linesIn' s ["physics.c", "astro.gone", "twice", "1 si.km"]
              @?= Right ["5", "3", "1.33486e-10 ±σ 3e-15 m^3 kg^-1 s^-2", "1 si.km"]
            -- A library type comes with its constructor and field labels.
            ("added data linalg.Cov2" `elem` outs) @? "Cov2 added"
            ("added linalg.jointCovariance" `elem` outs) @? "jointCovariance added"
            -- An alias is a label like any other: added as a unit.
            ("added si.newton" `elem` outs) @? "newton added"
            linesIn'
              s
              -- A field is found through a use, as a bare name is.
              [ ":use linalg"
              , ":use si"
              , "(jointCovariance ([1, 2] m ±σ 1 m, [3, 4] m ±σ 1 m)).rv"
              , "2 newton"
              ]
              @?= Right ["stored use linalg", "stored use si", "[0, 0; 0, 0] m^2", "2 newton"]
        -- A type label the codebase has is left alone.
        old2 <-
          either
            (assertFailure . T.unpack)
            pure
            ( sessionWith
                emptySession
                [multiline ["namespace linalg", "  data Cov2 = Cov2"], ":add"]
            )
        case stdlibUpgrade lib old2 of
          Left err -> assertFailure (T.unpack err)
          Right (s, outs) -> do
            ("added data linalg.Cov2" `notElem` outs) @? "Cov2 kept"
            lookupTypeName "linalg.Cov2" s.codebase
              @?= lookupTypeName "linalg.Cov2" old2.codebase
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
          expecting
            ( runLinesP
                [ "use astro"
                , "let mEarth = iau2015.earth.mu / G"
                , ":add"
                , ":rename astro.G astro.Gn"
                , ":todo"
                ]
            )
            $ \outs ->
              map (T.unwords . take 2 . T.words) (drop 1 outs)
                @?= [ "renamed `astro.G`"
                    , "re-hashed Gn"
                    , "upgraded mEarth"
                    , "nothing to"
                    ]
    , testCase
        ":rename of a nominal type re-hashes it, its users and the types that use it"
        $ do
          let shapes =
                [ "data Shape = Circle (Num m) | Square (Num m)"
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
            @?= typeHash ["data Form = Circle (Num m) | Square (Num m)", ":add"] "Form"
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

-- | A session afterSetup some lines, or the test fails.
sessionOf :: [Text] -> IO Session
sessionOf ls = either (assertFailure . T.unpack) pure (sessionP ls)

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

-- | What @:ls --types@ lists of the library's declarations of the built-in types.
builtinTypeListing :: [Text]
builtinTypeListing =
  [ "structural data Bool = False | True"
  , "False : Bool"
  , "True : Bool"
  , "structural data List a = Nil | Cons a (List a)"
  , "Nil : forall a. {a}"
  , "Cons : forall a. a -> {a} -> {a}"
  , "structural data Pair a b = Pair a b"
  , "Pair : forall a b. a -> b -> (a, b)"
  ]

{- | A listing of types, then the library's own in the order of their
namespaces: the declarations of the built-in
types, then temperature's and time's (design §3.10, F2).
-}
withBuiltinTypes :: [Text] -> Either Text [Text]
withBuiltinTypes ts =
  Right
    ( ts
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

-- | How @:ls --types@ lists the library's @astro.State@ (design §3.8).

{- | The library's records in @astro@, as @:ls --types@ lists them: a body
of a constant set, the classical elements, a transfer, a body's state.
-}
astroTypes :: [Text]
astroTypes =
  [ "data astro.Body = astro.Body {mu :: Num (m^3/s^2), radius :: Num m, flattening :: Num, j2 :: Num, rate :: Num (rad/s)}"
  , "astro.Body : Num (m^3/s^2) -> Num m -> Num -> Num -> Num (rad/s) -> astro.Body"
  , "data astro.kepler.Elements = astro.kepler.Elements {a :: Num m, e :: Num, i :: Num rad, raan :: Num rad, argp :: Num rad, nu :: Num rad}"
  , "astro.kepler.Elements : Num m -> Num -> Num rad -> Num rad -> Num rad -> Num rad -> astro.kepler.Elements"
  , "data astro.maneuver.Transfer = astro.maneuver.Transfer {dv1 :: Num (m/s), dv2 :: Num (m/s), dv3 :: Num (m/s), tof :: Num s}"
  , "astro.maneuver.Transfer : Num (m/s) -> Num (m/s) -> Num (m/s) -> Num s -> astro.maneuver.Transfer"
  , "data astro.State c n = astro.State {epoch :: Point c, pos :: Vec n m, vel :: Vec n (m/s)}"
  , "astro.State : forall c n. Point c -> Vec n m -> Vec n (m/s) -> astro.State c n"
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

{- | Design §3.10, part F, from source: every decision and every example it
writes, with the library's spaces and charts.
-}
partFTests :: TestTree
partFTests =
  testGroup
    "spaces and frames (design §3.10, part F)"
    [ testCase "pointAt places an amount on a chart from its origin along its axes" $ do
        let setup =
              [ "space Shop = Vec 3 m"
              , "chart room on Shop"
              , "chart bench on room at [2, 1, 0] m by rotz (90 deg)"
              , "chart pf on room step km by rotz (30 deg) then rotx (45 deg)"
              ]
        runLinesP
          ( setup
              ++ [ ":type pointAt"
                 , "pointAt bench ([1, 2, 3] m)"
                 , -- the origin and the step apply; the axes are the chart's
                   "pointAt pf ([1, 2, 3] m)"
                 , "pointAt pf ([1, 2, 3] m) == [0, 0, 0] pf .+ withAxes pf ([1, 2, 3] m)"
                 , "pointAt bench ([1, 2, 3] m) .- [0, 0, 0] bench"
                 , "let q = (pointAt bench ([1, 0, 0] m) to room) .- [2, 2, 0] room"
                 , "q · q < 1e-40 m^2"
                 , -- a computed amount along the chart's axes
                   "let off = withAxes pf ([0, 0, 2] m)"
                 , "pointAt pf (off + off)"
                 , -- a scalar chart: degC's origin is 273.15 K
                   "pointAt degC (5 K)"
                 , "pointAt degF (9 deltaF) to degC"
                 ]
          )
          @?= Right
            [ "forall c. Chart c -> Diff c -> Point c"
            , "[1, 2, 3] bench"
            , "[0.001, 0.002, 0.003] pf"
            , "true"
            , "[1, 2, 3] m"
            , "true"
            , "[0, 0, 0.004] pf"
            , "5 degC"
            , "-12.777777777777777777… degC"
            ]
        -- An amount along another chart's axes is not silently relabelled.
        expectError
          (runLinesP (setup ++ ["pointAt pf (withAxes bench ([1, 2, 3] m))"]))
          "the axes of"
    , testCase "shared chart configurations cancel before uncertainty arithmetic" $ do
        runLinesP
          [ "space Review = Vec 3 m"
          , "chart root on Review"
          , "chart parent on root by rotz (30 deg ± 0.1 rad)"
          , "chart a on parent at [1, 0, 0] m"
          , "chart b on parent at [2, 0, 0] m"
          , "([0, 0, 0] a to b) == [-1, 0, 0] b"
          , "let v = withAxes parent ([1, 0, 0] m)"
          , "(v from parent to parent) == v"
          , "(v from a to b) == v"
          , "chart scaled on parent step km"
          , "(v from scaled to parent) == v"
          , "chart moving angle on root by rotz angle"
          , "let w = withAxes (moving (0 rad)) ([1, 0, 0] m)"
          , encloses
              "1e-20"
              "(w from (moving (0 rad)) to (moving (90 deg))) / 1 m"
              "[0, -1, 0]"
          , "chart child angle on (moving angle) at [1, 0, 0] m"
          , encloses
              "1e-20"
              "(([0, 0, 0] (child (0 rad)) from (child (0 rad)) to (moving (90 deg))) .- [0, 0, 0] (moving (90 deg))) / 1 m"
              "[0, -1, 0]"
          ]
          @?= Right (replicate 6 "true")
    , testCase "a chart whose step may be zero is refused by name" $ do
        let session =
              [ "unit zero = 0 m"
              , "unit fuzz = 0 m ± 1 m"
              , "unit wobble = 1 m ± 2 m"
              , "unit two = 2 m"
              , "space Length = Num m"
              , "chart origin on Length"
              , "chart collapsed on origin step zero"
              , "chart fuzzy on origin step fuzz"
              , "chart wide on origin step wobble"
              , "chart under on collapsed step two"
              , "chart root on Length step zero"
              ]
            refused use = runLines (session ++ [use])
        refused "1 collapsed == 2 collapsed"
          @?= Left "error: chart collapsed has no invertible coordinates: its step is zero"
        refused "1 fuzzy"
          @?= Left
            "error: chart fuzzy has no invertible coordinates: its step's enclosure reaches zero"
        refused "1 wide"
          @?= Left
            "error: chart wide has no invertible coordinates: its step's enclosure reaches zero"
        -- a chart on it inherits the refusal, which names the culprit
        refused "1 under"
          @?= Left "error: chart collapsed has no invertible coordinates: its step is zero"
        refused "1 root"
          @?= Left "error: chart root has no invertible coordinates: its step is zero"
    , testCase "a negative step reverses a chart's direction"
        $ runLines
          [ "unit back = -1 m"
          , "unit kback = -1000 m"
          , "space Length = Num m"
          , "chart origin on Length"
          , "chart flipped on origin step back"
          , "chart far on origin at 5 m step kback"
          , "3 flipped"
          , "(3 flipped) to origin"
          , "(3 origin) to flipped"
          , "(3 flipped) .- (1 flipped)"
          , "((3 flipped) .- (1 flipped)) to m"
          , "(1 origin) .- (3 flipped)"
          , "(3 flipped) .+ 1 m"
          , "(2 far) to origin"
          , "(2 far) to flipped"
          , "((2 far) to origin) == (-1995 origin)"
          ]
          @?= Right
            [ "3 flipped"
            , "-3 origin"
            , "-3 flipped"
            , "2 back"
            , "-2 m"
            , "4 m"
            , "2 flipped"
            , "-1995 origin"
            , "1995 flipped"
            , "true"
            ]
    , testCase
        "restricted frame types print signatures that preserve their constraints"
        $ do
          let body = "let shift q = q .+ [1, 0, 0] m"
          expecting (runLinesP [body, ":type shift"]) $ \outs -> case outs of
            [ty] -> do
              ty @?= "forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c"
              runLinesP [multiline ["shift :: " <> ty, body], ":type shift"] @?= Right [ty]
              expectError (runLinesP [body, "shift (20 degC)"]) "a vector against a number"
              expectError
                (runLinesP [body, "shift :: forall c. Point c -> Point c"])
                "Space (Vec 3 m)"
              withTempStore $ \dir -> do
                stored <- persistLines dir [multiline ["shift :: " <> ty, body], ":add"]
                (loaded, notes) <- reload dir
                notes @?= []
                loaded.codebase.signatures @?= stored.codebase.signatures
                linesIn loaded [":type shift"] @?= Right [ty]
                source <- either (assertFailure . T.unpack) pure (exportSource stored Nothing)
                restored <- either (assertFailure . T.unpack) pure (sessionP [source, ":add"])
                restored.codebase.signatures @?= stored.codebase.signatures
            _ -> assertFailure (show outs)
    , testCase "F1: kinds; a binder names its frame's space" $ do
        runLinesP
          [ multiline
              [ "diffK :: forall (c : ITS90). Point c -> Point c -> Num K"
              , "let diffK p q = p .- q"
              ]
          , "diffK (20 degC) (10 degC)"
          , "diffK (491.67 degR) (0 kelvin)"
          , ":ls diffK"
          , multiline
              [ "conv :: forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
              , "let conv p c = p to c"
              ]
          , "conv (20 degC) degF"
          , ":ls conv"
          , ":type \\p q -> p .- q"
          ]
          @?= Right
            [ "10 K"
            , "273.15 K"
            , "diffK : forall (c : ITS90). Point c -> Point c -> Num K"
            , "68 degF"
            , "conv : forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
            , "forall c. Point c -> Point c -> Diff c"
            ]
        -- A frame of one space is not a frame of another: a kind error.
        expectError
          ( runLinesP
              ( inertial
                  ++ [ multiline
                         [ "conv :: forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
                         , "let conv p c = p to c"
                         ]
                     , "conv (20 degC) eci"
                     ]
              )
          )
          "frames of two spaces, ITS90 and GCRS"
        expectError
          (runLinesP ["f :: forall (c : Kelvin). Point c -> Point c", "let f p = p"])
          "`Kelvin` is not a space"
    , testCase "F2: spaces are declared and nominal; a chart names its space" $ do
        runLinesP
          ( inertial
              ++ [ ":view ITS90"
                 , -- TT is also si.TT, the teratesla: both show
                   ":view TT"
                 , ":view UTC"
                 , ":view GCRS"
                 , ":type [1, 2, 3] eci .- [0, 0, 0] eci"
                 , "space Other = Num K"
                 , "chart oC on Other at 273.15 K"
                 , "20 oC .- 0 oC"
                 ]
          )
          @?= Right
            [ "space ITS90 = Num K"
            , "-- time.TT"
            , "space TT = Num s"
            , "-- si.TT"
            , "TT = tera * 1 T"
            , "space UTC = Num s"
            , "space GCRS = Vec 3 m"
            , "Vec GCRS m"
            , "20 K"
            ]
        -- Two spaces declared alike are two spaces: their points never convert.
        expectError
          (runLinesP ["space Other = Num K", "chart oC on Other", "20 degC to oC"])
          "frames of two spaces, ITS90 and Other"
        expectError
          (runLinesP (inertial ++ ["20 degC to eci"]))
          "frames of two spaces, ITS90 and GCRS"
        -- TT and UTC are two spaces with no chart between them (design
        -- §3.10, F2): a unix instant and a J2000 one never meet.
        expectError (runLinesP ["0 unix .- 0 J2000"]) "frames of two spaces, UTC and TT"
        expectError (runLinesP ["0 unix to J2000"]) "frames of two spaces, UTC and TT"
        -- No point is written on a space's base, and a chart names its space.
        expectError (runLinesP ["3 ITS90"]) "unknown name `ITS90`"
        expectError
          (runLinesP ["chart degC2 at 273.15 K"])
          "name its space: `chart … on ITS90`"
        expectError
          (runLinesP ["space Bad = Mat 2 2 m"])
          "a space is of numbers or of vectors"
    , testCase "F3: what a chart declaration says decides whether it mints a frame" $ do
        runLinesP
          ( inertial
              ++ [ -- a root, an origin, turned axes: each a frame
                   ":type 0 kelvin"
                 , "chart warm on degC at 10 K"
                 , ":type 0 warm"
                 , "0 warm .- (10 degC to warm)"
                 , "chart turned on eci by rotz (30 deg)"
                 , ":type [1, 2, 3] turned .- [0, 0, 0] turned"
                 , -- a step alone is a rescaling: its parent's frame
                   "chart mdegC on degC step mK"
                 , ":type 20 mdegC"
                 , "20000 mdegC .- 20 degC"
                 , "20000 mdegC"
                 , -- Rankine is kelvin rescaled: no `to` between them
                   ":type 491.67 degR"
                 , "491.67 degR .- 0 kelvin"
                 , "(0 kelvin .+ 1 K) to degR"
                 ]
          )
          @?= Right
            [ "Point kelvin"
            , "Point warm"
            , "0 K"
            , "Vec turned m"
            , "Point degC"
            , "0 K"
            , "20000 mdegC"
            , "Point kelvin"
            , "273.15 K"
            , "1.8 degR"
            ]
        -- Two charts declared alike are two frames, like two newtypes.
        expectError
          (runLinesP ["chart a1 on ITS90", "chart a2 on ITS90", "0 a1 .- 0 a2"])
          "points on a1 and a2: convert one with `to`"
        -- A chart with parameters is one frame for all its arguments.
        runLinesP
          ( earth
              ++ [ ":type ecef"
                 , ":type ecef (100 J2000)"
                 , ":type [1, 2, 3] (ecef (100 J2000)) .- [0, 0, 0] (ecef (200 J2000))"
                 ]
          )
          @?= Right ["Point J2000 -> Chart ecef", "Chart ecef", "Vec ecef m"]
    , testCase "F3: two bodies are two declarations; what they share is a function" $ do
        let siblings =
              inertial
                ++ [ "let posA t = withAxes eci ([7000, 0, 0] km)"
                   , "let posB t = withAxes eci ([0, 7000, 0] km)"
                   , "let lvlhTurn r = rotz (atan2 r.1 r.0)"
                   , "chart lvlhA t on eci at posA t by lvlhTurn (posA t)"
                   , "chart lvlhB t on eci at posB t by lvlhTurn (posB t)"
                   , "let t0 = 0 unix"
                   , "let a = [1, 0, 0] (lvlhA t0)"
                   , "let b = [0, 1, 0] (lvlhB t0)"
                   ]
        runLinesP (siblings ++ [":type a", ":type b", "b .- b"])
          @?= Right ["Point lvlhA", "Point lvlhB", "[0, 0, 0] m"]
        expectError
          (runLinesP (siblings ++ ["b .- a"]))
          "points on lvlhB and lvlhA: convert one with `to`"
        expectError
          (runLinesP (siblings ++ ["(a .- a) + (b .- b)"]))
          "the axes of lvlhA against the axes of lvlhB"
        -- Converted to one frame, they subtract.
        runLinesP
          ( siblings
              ++ [ encloses
                     "1e-15"
                     "((b from (lvlhB t0) to eci) .- (a from (lvlhA t0) to eci)) / 1 m"
                     "[-7000002, 7000000, 0]"
                 ]
          )
          @?= Right ["true"]
    , testCase "F4: Point, Chart, Diff and Axes; Diff reduces once the space is known" $ do
        runLinesP
          ( frame
              ++ [ ":type 20 degC .- 10 degC"
                 , ":type 20 degF .- 10 degF"
                 , ":type [1, 2, 3] lvlh .- [0, 0, 0] lvlh"
                 , "chart bench on GCRS at [1, 0, 0] m"
                 , ":type [1, 2, 3] bench .- [0, 0, 0] bench"
                 , multiline ["d :: Diff lvlh", "let d = [1, 0, 0] m"]
                 , ":type d"
                 , multiline ["k :: Coords lvlh", "let k = [1, 0, 0]"]
                 , ":type k"
                 , ":type \\p q -> p .- q"
                 , ":type \\c -> pointOn c"
                 , multiline
                     [ "good :: forall (c : GCRS). Point c -> Point c -> Num m"
                     , "let good p q = norm (p .- q)"
                     ]
                 , "good ([3, 4, 0] eci) ([0, 0, 0] eci)"
                 ]
          )
          @?= Right
            [ "Num K"
            , "Num K"
            , "Vec lvlh m"
            , "Vec GCRS m"
            , "Vec lvlh m"
            , "Vec lvlh"
            , "forall c. Point c -> Point c -> Diff c"
            , "forall c. Chart c -> Coords c -> Point c"
            , "5 m"
            ]
        -- Arithmetic on Diff of a frame whose space nothing says waits, and
        -- is refused when the definition is generalised.
        expectError
          (runLinesP ["let bad p q = vmap abs (p .- q)"])
          "the amount between points on a frame of a space not known here: give a signature naming the space"
    , testCase "F5: the primitives over frames; another frame is reported as one" $ do
        runLinesP
          ( frame
              ++ [ ":type pointOn"
                 , ":type toChart"
                 , ":type rotationOf"
                 , ":type withAxes"
                 , "([1.5, 2.25, 3] lvlh).0"
                 , ":type ([1.5, 2.25, 3] lvlh).2"
                 ]
          )
          @?= Right
            [ "forall c. Chart c -> Coords c -> Point c"
            , "forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1"
            , "forall s (c : s). Chart c -> Mat s c"
            , "forall (s : Space (Vec n d)) (c : s) (n : Len) d d1. Chart c -> Vec n d1 -> Vec c d1"
            , "1.5 m"
            , "Num m"
            ]
        expectError
          (evalP "20 degC .- 68 degF")
          "points on degC and degF: convert one with `to`"
        expectError (evalP "20 degC .+ (5 degC)") "an amount and a point"
    , testCase "F6: a point holds its coordinates on its frame, the step applied" $ do
        runLinesP
          ( frame
              ++ [ "20 degC .- 0 degC"
                 , -- printed on the chart it was written on, the step divided out
                   "chart ground on eci at [100, 200, 0] m step km"
                 , "[7, 0, 0] ground"
                 , "[7, 0, 0] ground .- [0, 0, 0] ground"
                 , -- inside a turned frame, exact: no rotation applies
                   "[1, 2, 3] lvlh .- [0, 5, 0] lvlh"
                 , "([1, 2, 3] lvlh .+ [1, 0, 0] m).0"
                 , -- a point fixed on a moving body is a constant
                   "chart spinner t on eci by rotz (1 rad/s * (t .- 0 unix)) spinning [0, 0, 1] rad/s"
                 , "[1, 2, 3] (spinner (0 unix)) == [1, 2, 3] (spinner (100 unix))"
                 ]
          )
          @?= Right
            [ "20 K"
            , "[7, 0, 0] ground"
            , "[7, 0, 0] km"
            , "[1, -3, 3] m"
            , "2 m"
            , "true"
            ]
    , testCase "F7: a chart with parameters is converted from a named configuration" $ do
        let sat =
              earth
                ++ [ ":add"
                   , "data Sat = Sat {epoch :: Point J2000, pos :: Vec ecef m}"
                   , "let lvlhTurn s = rotz (atan2 s.pos.1 s.pos.0)"
                   , -- linked: the parent applied to the child's own parameters
                     "chart lvlh s on (ecef s.epoch) at s.pos by lvlhTurn s"
                   , "let s = Sat {epoch = 0 J2000, pos = [7000, 0, 0] km}"
                   , "let t0 = 0 J2000"
                   , "let p = [1, 2, 3] (lvlh s)"
                   ]
        lastN 4
          <$> runLinesP
            ( sat
                ++ [ ":type p"
                   , encloses
                       "1e-12"
                       "((p from (lvlh s) to (ecef t0)) .- [7000000, 0, 0] (ecef t0)) / 1 m"
                       "[1, 2, 3]"
                   , -- the target applied
                     "let q = [6378000, 0, 0] eci"
                   , encloses
                       "1e-9"
                       "((q to (ecef t0)) .- [0, 0, 0] (ecef t0)) / 1 m"
                       "expm (-(rotz (gmst t0))) @ [6378000, 0, 0]"
                   , -- a point on a chart without parameters needs no from
                     "let r = [1, 2, 3] eci"
                   , "r to eci"
                   ]
            )
          @?= Right ["Point lvlh", "true", "true", "[1, 2, 3] eci"]
        -- The chart a point was written on is never used for a conversion.
        expectError
          (runLinesP (sat ++ ["p to eci"]))
          "lvlh takes arguments: write p from (lvlh …) to eci"
        expectError
          (runLinesP (sat ++ ["p from (ecef t0) to eci"]))
          "charts on lvlh and ecef"
        -- Writing a point needs an applied chart.
        expectError
          (runLinesP (sat ++ ["[1, 2, 3] ecef"]))
          "`ecef` takes arguments: a point is written on an applied chart, as in [1, 2, 3] (ecef t0)"
        -- Inherited: the parent's parameters become the child's.
        lastN 2
          <$> runLinesP
            ( sat
                ++ [ "chart arm q t on (ecef t) at [1, 0, 0] m by roty q"
                   , ":type arm"
                   , encloses
                       "1e-15"
                       "(([0, 0, 0] (arm (30 deg) t0) from (arm (30 deg) t0) to (ecef t0)) .- [0, 0, 0] (ecef t0)) / 1 m"
                       "[1, 0, 0]"
                   ]
            )
          @?= Right ["Num rad -> Point J2000 -> Chart arm", "true"]
    , testCase "F7: the three subtractions" $ do
        let cities =
              earth
                ++ [ "let t0 = 0 J2000"
                   , "let t1 = 0 J2000 .+ 1 s"
                   , "chart lvlhA t on eci at withAxes eci ([7000, 0, 0] km) by rotz (90 deg)"
                   , "let a = [6378000, 0, 0] (ecef t0)"
                   , "let b = [0, 6378000, 0] (ecef t0)"
                   , "let e0 = ecef t0"
                   , "let e1 = ecef t1"
                   , "let la = lvlhA t0"
                   ]
        runLinesP
          ( cities
              ++ [ -- 1. on one frame: relative to the frame, whatever the
                   -- configurations its points were written with
                   "b .- a"
                 , "[0, 6378000, 0] (ecef t1) .- a"
                 , -- 2. across the tree: a point on eci seen from one on ecef
                   encloses "1e-9" "(([0, 0, 0] eci to e0) .- a) / 1 m" "[-6378000, 0, 0]"
                 , -- 3. both in a third frame at one configuration: the
                   -- difference re-expressed
                   encloses
                     "1e-6"
                     "(((b from e0 to la) .- (a from e0 to la)) - ((b .- a) from e0 to la)) / 1 m"
                     "[0, 0, 0]"
                 , -- at two configurations: a new quantity, the frame's motion
                   -- between them included, about ω R δt
                   "let moved = (a from e1 to eci) .- (a from e0 to eci)"
                 , "let dist = mid (norm (mid moved) / 1 m)"
                 , "dist > 400 && dist < 500"
                 ]
          )
          @?= Right
            [ "[-6378000, 6378000, 0] m"
            , "[-6378000, 6378000, 0] m"
            , "true"
            , "true"
            , "true"
            ]
    , testCase
        "F8: any chart after a literal writes a point; one with parameters unapplied is refused"
        $ do
          runLinesP
            ( earth
                ++ [ "let c = degF"
                   , "3 c"
                   , "[1, 2, 3] (ecef (0 J2000))"
                   , multiline
                       ["pt :: forall (c : ITS90). Chart c -> Point c", "let pt c = 3 c"]
                   , "pt degF"
                   , "(\\c -> 3 c) degC"
                   ]
            )
            @?= Right ["3 degF", "[1, 2, 3] (ecef (0 J2000))", "3 degF", "3 degC"]
          expectError
            (runLinesP (earth ++ ["3 ecef"]))
            "`ecef` takes arguments: a point is written on an applied chart"
          runLinesP ["let pt c = 3 c", "pt degC"] @?= Right ["3 degC"]
          -- Written as F8 has it, over every space: a number is the coordinate
          -- of a point on a space of numbers only, so the definition is not as
          -- general as its signature (design §3.10, part F, as built).
          expectError
            (runLinesP [multiline ["pt :: forall c. Chart c -> Point c", "let pt c = 3 c"]])
            "not as general as its signature"
    , testCase "F9: printing and encoding" $ do
        runLinesP
          ( frame
              ++ [ ":type 20 degC"
                 , ":type degC"
                 , ":type [1, 2, 3] lvlh"
                 , "20 degC"
                 , "[1, 2, 3] lvlh"
                 ]
          )
          @?= Right ["Point degC", "Chart degC", "Point lvlh", "20 degC", "[1, 2, 3] lvlh"]
    , testCase "F10: a chart's clauses, to as the one conversion, on" $ do
        runLinesP
          [ ":view kelvin"
          , ":view degC"
          , ":view degF"
          , ":view degR"
          , ":view JD"
          , ":view MJD"
          , ":view J2000"
          , ":view unix"
          ]
          @?= Right
            [ "chart kelvin on ITS90"
            , "chart degC on ITS90 at 273.15 K"
            , "chart degF on ITS90 at 459.67 deltaF step deltaF"
            , "chart degR on kelvin step deltaF"
            , "chart JD on TT step day"
            , "chart MJD on TT at 2400000.5 day step day"
            , "chart J2000 on TT at 2451545 day step day"
            , "chart unix on UTC"
            ]
        -- step, by, then and spinning are names outside a chart; on is a keyword.
        runLinesP ["let step = 2", "let spinning = 3", "step + spinning"]
          @?= Right ["5"]
        expectError (runLinesP ["let on = 3"]) "unexpected"
        expectError (runLinesP ["let from = 3"]) "unexpected"
        -- along and inChart are retired into to; withAxes stays.
        expectError
          (runLinesP (frame ++ ["inChart lvlh ([1, 0, 0] m)"]))
          "unknown name `inChart`"
        expectError
          (runLinesP (frame ++ ["along lvlh ([1, 0, 0] m)"]))
          "unknown name `along`"
        -- on subtracts in a frame, and only a subtraction.
        runLinesP
          ( frame
              ++ [ encloses
                     "1e-15"
                     "(([1, 2, 3] eci .- [4, 5, 6] eci on lvlh) - (([1, 2, 3] eci to lvlh) .- ([4, 5, 6] eci to lvlh))) / 1 m"
                     "[0, 0, 0]"
                 , ":type [1, 2, 3] eci .- [4, 5, 6] eci on lvlh"
                 ]
          )
          @?= Right ["true", "Vec lvlh m"]
        expectError
          (runLinesP (frame ++ ["[1, 2, 3] eci on lvlh"]))
          "`on` subtracts two points in a frame: write b .- a on c"
    , testCase "F10: conversions and on read back to their hashes" $ do
        let stored =
              frame
                ++ [ "let viaOn a b = b .- a on lvlh"
                   , multiline
                       ["fromPt :: Point lvlh -> Point eci", "let fromPt p = p from lvlh to eci"]
                   , multiline
                       [ "fromAmt :: Vec lvlh m -> Vec GCRS m"
                       , "let fromAmt v = v from lvlh to eci"
                       ]
                   , multiline ["toAmt :: Vec GCRS m -> Vec lvlh m", "let toAmt v = v to lvlh"]
                   ]
        forM_ ["viaOn", "fromPt", "fromAmt", "toAmt"] $ \n ->
          expecting (runLinesP (stored ++ [":edit " <> n])) $ \outs ->
            runLinesP (frame ++ [multiline outs, ":hash " <> n])
              @?= runLinesP (stored ++ [":hash " <> n])
    , testCase
        "F7: with no type to say so, a frame with parameters is refused when converting"
        $ do
          -- A function over any frame cannot know statically: the conversion
          -- refuses at run time, never reading the chart a point was written on.
          let setup =
                earth
                  ++ [ multiline
                         ["toE :: forall (c : GCRS). Point c -> Point eci", "let toE p = p to eci"]
                     ]
          runLinesP (setup ++ [":type toE", "toE ([1, 2, 3] eci)"])
            @?= Right ["forall (c : GCRS). Point c -> Point eci", "[1, 2, 3] eci"]
          expectError
            (runLinesP (setup ++ ["toE ([1, 2, 3] (ecef (0 J2000)))"]))
            "ecef takes arguments: write p from (ecef …) to c"
    ]
 where
  inertial = [multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]]
  frame = inertial ++ ["chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"]
  earth =
    inertial
      ++ [ "let ω_e = 7.2921159e-5 rad/s"
         , "let gmst t = 280.46061837 deg + 360.98564736629 deg / day * (t .- 0 J2000)"
         , "chart ecef t on eci by rotz (gmst t) spinning [0, 0, 1] * ω_e"
         ]
