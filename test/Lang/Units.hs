-- | Units, display, readings and quantities.
module Lang.Units (
  unitTests,
  displayTests,
  readingTests,
  partUTests,
) where

import Control.Monad (forM_)
import Data.Bifunctor (first)
import Data.ByteString qualified as BS (
  drop,
  replicate,
  singleton,
  take,
  unpack,
 )
import Data.Text (Text)
import Data.Text qualified as T (
  concat,
  isInfixOf,
  isPrefixOf,
  pack,
  unpack,
 )
import Lang.Common (
  editFileOf,
  editSession,
  edited,
  evalP,
  evalText,
  evalU,
  expectError,
  expecting,
  lastN,
  multiline,
  num,
  runLines,
  runLinesP,
  toks,
  typeOfText,
  (*.),
  (+.),
  (/.),
 )
import Metron.Core (
  Fin (FS, FZ),
  Hash (Hash),
  Hint (Hint),
  Lit (LTensor),
  Term (App, Lam, Let, Lit, Pow, PrimApp, Ref, Var),
  Vec (VNil),
 )
import Metron.Dimension (
  DimAtom (Base),
  Spelling (Unicode),
  dimFromAtoms,
 )
import Metron.Dimension qualified as Dimension (
  BaseDim (L),
  dimPow,
  dimVar,
 )
import Metron.Driver (EditScope (EditNamespace))
import Metron.Hash (decodeTypeDef, encodeTypeDef)
import Metron.Infer (TypeError (..), elaborateClosed)
import Metron.Lexer (Token (TOp, TSup))
import Metron.Lexer qualified as L (Token (TNum))
import Metron.Limits (defaultLimits, limitSettings)
import Metron.Prelude (stdlibNamespaces)
import Metron.Pretty (renderTermIn)
import Metron.TCore (lintClosed)
import Metron.Type (
  Kind (KDim),
  Scheme (Forall),
  Shape (SNil),
  Type (TTensor, TUnit),
  TypeDef (TypeDef),
  TypeLookup (TypeLookup),
  numD,
  renderScheme,
  selfType,
  structuralLabel,
 )
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (
  Assertion,
  assertFailure,
  testCase,
  (@?),
  (@?=),
 )

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
    , localOption (mkTimeout 10_000_000) $ testCase "a role is neither a kind nor a type: their encodings are refused" $ do
        -- Roles were a kind (byte 7) and a quantity of a role variable a
        -- type (tag 0x2E). Nothing written could make either, so both are
        -- gone, and no stored type held them (design §3.10, U9).
        let def = TypeDef [(0, KDim)] [[TTensor SNil (Dimension.dimVar 0)]] structuralLabel
            bytes = encodeTypeDef def
            patched i b = BS.take i bytes <> BS.singleton b <> BS.drop (i + 1) bytes
        BS.unpack (BS.take 5 bytes) @?= [1, 3, 1, 1, 0x21]
        decodeTypeDef bytes @?= Right def
        expectLeft (decodeTypeDef (patched 1 7)) "unknown kind 7"
        expectLeft (decodeTypeDef (patched 4 0x2E)) "unknown type tag 46"
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
        -- The refusal of `Amount` suggests types that are accepted; it
        -- once suggested `Quantity Amount d`, itself refused.
        expectError
          (runLinesP ["f :: Amount -> Num m", "let f x = x"])
          "Amount is not a type: an amount is Num d, or Tensor s d"
        forM_ ["forall d. Num d -> Num d", "forall s d. Tensor s d -> Tensor s d"] $ \sig ->
          runLinesP
            [ multiline
                ["f :: " <> sig, "let f x = x"]
            , "f 2"
            ]
            @?= Right ["2"]
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
          [ "unit measured = sample (normal (1 m) (0.01 m))"
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
        $ case evalText "sample (normal (3 m) (1 s))" of
          Left err -> T.isInfixOf "dimensions differ" err @? T.unpack err
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

-- Display units ----------------------------------------------------------------------

displayTests :: TestTree
displayTests =
  testGroup
    "display units"
    [ testCase ":set unicode prints the unicode spellings, which read back" $ do
        let limits = [n <> " " <> v | (n, v) <- limitSettings defaultLimits]
        runLinesP [":set"]
          @?= Right
            ( [ "precision 20"
              , "unicode off"
              , "samples 32"
              , "seed 1"
              , "arithmetic rational"
              , "propagation montecarlo"
              , "roundingAnalysis off"
              , "roundingSamples 8"
              , "cores 1"
              ]
                ++ limits
            )
        runLinesP [":set unicode on", ":set", ":set unicode off", ":set"]
          @?= Right
            ( [ "precision 20"
              , "unicode on"
              , "samples 32"
              , "seed 1"
              , "arithmetic rational"
              , "propagation montecarlo"
              , "roundingAnalysis off"
              , "roundingSamples 8"
              , "cores 1"
              ]
                ++ limits
                ++ [ "precision 20"
                   , "unicode off"
                   , "samples 32"
                   , "seed 1"
                   , "arithmetic rational"
                   , "propagation montecarlo"
                   , "roundingAnalysis off"
                   , "roundingSamples 8"
                   , "cores 1"
                   ]
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
