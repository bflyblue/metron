-- | Lexing, parsing, desugaring, printing and respelling.
module Lang.Syntax (
  lexerTests,
  parserTests,
  desugarTests,
  prettyTests,
  respellTests,
) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map (lookup)
import Data.Text (Text)
import Data.Text qualified as T (isInfixOf, unpack)
import Lang.Common (
  Tree (A, I, L, Lt, N, Ng, O, P, Pj, SL, SR, Sl, V, Vc),
  bool,
  desugarText,
  evalText,
  h,
  num,
  parseShape,
  runLinesP,
  shape,
  toks,
  v0,
  v1,
  v2,
  (*.),
  (+.),
  (-.),
 )
import Metron.Core (
  Nat (Z),
  Term (App, Lam, Let, PrimApp, Ref),
  alphaEq,
 )
import Metron.Desugar (
  Provenance (spans),
  Resolution (Resolution),
  Resolved (ATerm),
  desugarClosed,
  noResolver,
  renderDesugarError,
 )
import Metron.Lexer (
  Keyword (KFalse, KIn, KLet, KTrue, KWhere),
  Token (
    TArrow,
    TBlockEnd,
    TEquals,
    TField,
    TIdent,
    TKw,
    TLambda,
    TOp,
    TSep,
    TSup,
    TWild
  ),
 )
import Metron.Lexer qualified as L (Token (TNum, TProj))
import Metron.Parser (parseExpr, parseProgram)
import Metron.Pretty (renderRational, respell)
import Metron.Syntax qualified as S (
  Binding (body, name),
  Name (text),
  Op (
    Add,
    Compose,
    Div,
    Infix,
    Lt,
    On,
    Outer,
    PSub,
    Scale,
    Sub,
    To
  ),
  Pos (Pos),
  Span (Span),
  Statement (SExpr, SLet),
 )
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (
  Assertion,
  assertBool,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )

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
    , localOption (mkTimeout 10_000_000) $ testCase "an ASCII subscript is the unicode one (design §2.8)" $ do
        toks "v_0 x_12 a_1b _0 x_ x__1 e₁"
          @?= Right
            [ TIdent "v₀"
            , TIdent "x₁₂"
            , TIdent "a₁b"
            , TIdent "_0"
            , TIdent "x_"
            , TIdent "x_₁"
            , TIdent "e₁"
            ]
        -- It once lexed as an identifier of its own, which did not resolve.
        runLinesP
          ["let v₀ = 3", "v_0 + 1", "let w_1 = 2", "w₁", ":view v_0", ":view w₁"]
          @?= Right ["4", "2", "v₀ = 3", "w₁ = 2"]
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
    , testCase "removed uncertainty spellings are rejected"
        $ map (either (const True) (const False) . toks) ["a ± 1", "a ±σ 1"]
          @?= [True, True]
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
    , testCase "sqrt prefix"
        $ parseShape "√x" @?= Right (A (V "sqrt") (V "x"))
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
    , localOption (mkTimeout 10_000_000)
        $ testCase
          "a primitive used as a value prints eta-reduced and reads back (design §2.9)"
        -- `vmap sqrt` printed as `\x -> vmap (\x' -> sqrt x') x`.
        $ forM_
          [ ("vmap sqrt", "vmap sqrt")
          , ("foldr add 0", "foldr add 0")
          , ("map add", "map add")
          , ("outer 2", "outer 2")
          , ("slice 1 0", "slice 1 0")
          , ("\\y -> atan2 y", "\\y -> atan2 y")
          , -- a lambda the user wrote stays one, the binder's name kept
            ("\\x -> neg x", "\\x -> -x")
          , ("\\t -> slice 1 0 t", "\\t -> t._.0")
          , ("\\w h -> w * h", "\\w -> \\h -> w * h")
          , ("(2 *)", "\\x -> 2 * x")
          , -- applied, the lambda stays: `sqrt 4` would be another term
            ("(\\x -> vmap sqrt x) [4]", "(\\x -> vmap sqrt x) [4]")
          ]
        $ \(written, printed) ->
          case runLinesP ["let h = " <> written, ":view h", ":hash h"] of
            Right [view, hash] -> do
              view @?= "h = " <> printed
              runLinesP ["let h = " <> written, "let h' = " <> printed, ":hash h'"]
                @?= Right [hash]
            other -> assertFailure (show other)
    ]

-- The unicode echo ------------------------------------------------------------------

respellTests :: TestTree
respellTests =
  testGroup
    "unicode echo"
    [ testCase "an input line in its unicode spelling" $ do
        respell "sample (normal 2 0.1) * 3 km/h" @?= Nothing
        respell "\\x -> x^2 <= 4" @?= Just "λx → x² ≤ 4"
        respell "sample (uniform 0.9 1.1)" @?= Nothing
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
        respell "\\x y -> x^-2 <= y + 1 -> 2" @?= Just "λx y → x⁻² ≤ y + 1 → 2"
        respell "(\\x -> x)   >=   y -- a comment -> here"
          @?= Just "(λx → x)   ≥   y -- a comment -> here"
        -- a tab counts as the lexer counts it
        respell "x\t<= 1 ->\t2" @?= Just "x\t≤ 1 →\t2"
        -- `f\x` must not become the identifier `fλx`
        respell "f\\x -> x" @?= Just "f\\x → x"
    , testCase ":set unicode on echoes statement lines" $ do
        runLinesP [":set unicode on", "2^3"]
          @?= Right ["  ≡ 2³", "8"]
        runLinesP [":set unicode on", "let f x = x^2", "f 3"]
          @?= Right ["  ≡ let f x = x²", "9"]
        -- nothing to respell, a command, or unicode off: no echo
        runLinesP [":set unicode on", "1 + 2"] @?= Right ["3"]
        runLinesP [":set unicode on", ":type \\x -> x"] @?= Right ["forall a. a → a"]
        runLinesP ["2^3"] @?= Right ["8"]
    ]
