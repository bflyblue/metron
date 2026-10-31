{-# LANGUAGE PatternSynonyms #-}

{- | User-facing rendering (design §3.2.10, §7.2): values as decimals, and
Core terms back to surface syntax for @:view@.
-}
module Metron.Pretty (
  renderRational,
  renderMagnitude,
  renderRough,
  renderValue,
  renderValueWith,
  displayParts,
  renderExact,
  renderBudget,
  renderNested,
  renderTerm,
  renderTermIn,
  renderTermUnits,
  renderParamsUnits,
  UnitRef,
  RefNamer,
  FieldNamer,
  Printer (..),
  plainPrinter,
  respell,
) where

import Control.Applicative ( (<|>) )
import Data.Char ( intToDigit, isAlphaNum )
import Data.Maybe ( fromMaybe, isJust, mapMaybe )
import Data.Ratio ( denominator, numerator, (%) )
import Data.Text ( Text )
import Metron.Affine
    ( decimalExponent,
      roundAt,
      sqrtApprox,
      collapse,
      divM,
      midpoint,
      nonLinearAt,
      nudges,
      sigmaOf,
      skewOf,
      Collapsed(variance, mid, bound),
      Magnitude(Affine, Exact),
      Nudge(origin, kind),
      Origin(Declared, Tagged),
      Skew(ratioSq, operation) )
import Metron.Builtin ( pattern ConsC, pattern FalseC, pattern NilC, pattern TrueC, pattern TupleC )
import Metron.Core
    ( renderLabel,
      showHash,
      vecAppend,
      vecMap,
      vecToList,
      Alt(Alt),
      ConRef(UserCon),
      Fin(..),
      Hash,
      Hint(Hint),
      Lit(LTensor),
      Nat(Z),
      NudgeKind(..),
      Term(..),
      Vec(..) )
import Metron.Dimension
    ( Spelling(..),
      arrowText,
      exponentText,
      productText,
      renderUnitsIn )
import Metron.UnitHint ( Preferences, UnitAtom(..), UnitFactor(power, atom), UnitHint(atoms, pinned, dim, factor) )
import Metron.Eval ( pattern VBool, coordinatesOn, Applied(Applied), Chart(dim, name, applied, step, dims, origin), EvalError(Internal), Value(..) )
import Metron.Primitive ( baseUnit )
import Metron.TCore ( patternText )
import Metron.Type ( conText )
import Metron.Affine qualified as A ( Origin(Builtin) )
import Metron.Lexer qualified as L
    ( prepare,
      tokenize,
      Keyword(KFalse, KTrue),
      Located(span, value),
      Token(TOp, TIdent, TRParen, TRBracket, TProj, TWild, TField, TAbs,
            TNum, TSup, TKw, TPlusMinus, TArrow, TLambda) )
import Data.Map.Strict qualified as Map ( lookup )
import Metron.Syntax qualified as S ( Pos(Pos), Span(from, to) )
import Data.Text qualified as T
    ( concat,
      all,
      any,
      drop,
      dropWhileEnd,
      intercalate,
      isPrefixOf,
      isSuffixOf,
      justifyLeft,
      justifyRight,
      length,
      null,
      replicate,
      splitOn,
      take,
      takeWhile,
      uncons,
      unsnoc,
      unwords,
      pack,
      unpack )
import Data.Vector qualified as V ( head, toList )

-- Numbers ------------------------------------------------------------------------

{- | @renderRational precision r@: an exact value in full, or truncated at
@precision@ significant digits with @…@ when the expansion goes on. The
integer part is always complete. Values below @10^-4@ are written in
scientific notation, so a Planck-scale quantity is not a row of zeros.
-}
renderRational :: Int -> Rational -> Text
renderRational scale = renderDecimal scale False

{- | As 'renderRational', optionally marking the value approximate even when
its digits end: the certain digits of an affine midpoint.
-}
renderDecimal :: Int -> Bool -> Rational -> Text
renderDecimal scale approx r
  | r < 0 = "-" <> renderDecimal scale approx (negate r)
  | r /= 0 && r < 1 % 10000 =
      let e = decimalExponent r
       in renderDecimal scale approx (r / 10 ^^ e) <> "e" <> tshow e
  | otherwise =
      let (whole, frac) = properFraction r :: (Integer, Rational)
          -- Significant digits left for the fraction after the integer part.
          (digits, exact) = fractionDigits (max 0 (scale - decimalExponent r - 1)) frac
       in tshow whole
            <> (if null digits then "" else "." <> T.pack digits)
            <> (if exact && not approx then "" else "…")
 where
  -- An approximate value shows all of its certain digits, zeros included.
  fractionDigits n frac
    | approx =
        let (ds, ex) = fractionDigitsOf n frac
         in (ds ++ replicate (n - length ds) '0', ex)
    | otherwise = fractionDigitsOf n frac

{- | Up to @n@ decimal digits of a fraction in @[0, 1)@, and whether they are
the whole expansion.
-}
fractionDigitsOf :: Int -> Rational -> (String, Bool)
fractionDigitsOf n frac
  | frac == 0 = ("", True)
  | n == 0 = ("", False)
  | otherwise =
      let scaled = frac * 10
          d = floor scaled :: Integer
          rest = scaled - fromInteger d
          (more, exact) = fractionDigitsOf (n - 1) rest
       in (intToDigit (fromInteger d) : more, exact)

{- | Print a magnitude at a scale (design §3.2.10). An affine value is
collapsed to a midpoint, a bound radius @r@ and a standard deviation @σ@:

* @σ = 0@ and @r@ below the last printed digit: @precision@ significant
  digits of the midpoint and @…@, each correct to within one unit in the
  last place;
* @σ = 0@ otherwise: @mid ± r@, @r@ to two significant digits and the
  midpoint to the same position;
* @σ > 0@: @mid ±σ σ@ the same way, then @(bound r)@ unless @r@ is
  negligible against @σ@. The marker is never omitted, so a 1σ band is
  never mistaken for a certainty.
-}
renderMagnitude :: Int -> Magnitude -> Text
renderMagnitude scale = \case
  Exact r -> renderRational scale r
  m ->
    let c = collapse m
        sigma = sigmaOf (scale + 4) c
        lastDigit = decimalExponent c.mid - scale + 1
     in if sigma == 0 && c.bound < 10 ^^ lastDigit
          then
            -- A first-order σ of zero after a non-linear statistical step
            -- (design §3.2) is no certainty: the midpoint alone, without
            -- the ellipsis that promises every digit.
            if isJust (skewOf m)
              then renderDecimal scale False c.mid
              else renderDecimal scale True c.mid
          else
            if sigma == 0
              then uncertainAt c.mid c.bound "±"
              else
                -- The midpoint goes to the last digit of the coarser of σ
                -- and the bound, so no digit beyond either is shown.
                let (q, _) = roundUncertainty (max sigma c.bound)
                 in renderFixed q (roundAt q c.mid)
                      <> " ±σ "
                      <> renderRadius sigma
                      <> (if c.bound * 100 >= sigma then " (bound " <> renderRadius c.bound <> ")" else "")

{- | @mid ± u@ with the uncertainty to two significant digits (one when the
second is zero) and the midpoint rounded to the same position. The
rounding of the midpoint widens the uncertainty, so it is folded in
before the uncertainty itself is rounded up.
-}
uncertainAt :: Rational -> Rational -> Text -> Text
uncertainAt mid u marker =
  let (q0, _) = roundUncertainty u
      mid' = roundAt q0 mid
      (q, u') = roundUncertainty (u + abs (mid - mid'))
      mid'' = roundAt q mid
   in renderFixed q mid'' <> " " <> marker <> " " <> renderRadius u'

{- | Round an uncertainty to two significant digits, or one when the second
is zero; returns the exponent of its last digit. Nearest, not up: the
printed radius is within half a unit in its last place of the true one.
-}
roundUncertainty :: Rational -> (Int, Rational)
roundUncertainty u =
  let e = decimalExponent u
      two = roundAt (e - 1) u
   in if roundAt e u == two then (e, two) else (e - 1, two)

-- | An uncertainty to two significant digits.
renderRadius :: Rational -> Text
renderRadius u = let (q, u') = roundUncertainty u in renderFixed q u'

{- | A value that is a multiple of @10^q@, with exactly the digits down to
@10^q@; scientific notation outside @[10^-4, 10^15)@.
-}
renderFixed :: Int -> Rational -> Text
renderFixed q v
  | v < 0 = "-" <> renderFixed q (negate v)
  | v /= 0 && (e < -4 || e >= 15) =
      plain (q - e) (v / 10 ^^ e) <> "e" <> tshow e
  | otherwise = plain q v
 where
  e = decimalExponent v
  plain q' x
    | q' >= 0 = tshow (round x :: Integer)
    | otherwise =
        let digits = negate q'
            scaled = round (x * 10 ^ digits) :: Integer
            (whole, frac) = scaled `divMod` (10 ^ digits)
         in tshow whole <> "." <> T.justifyRight digits '0' (tshow frac)

tshow :: (Show a) => a -> Text
tshow = T.pack . show

-- Values --------------------------------------------------------------------------

{- | The field names of a declared constructor (design §2.3): given the type's
hash, the constructor's index and its arity, a name or 'Nothing' for each
field in order.
-}
type FieldNamer = Hash -> Int -> Int -> [Maybe Text]

{- | What the value printer needs beyond the value: current names for
references (units, charts, nudge origins) and the field names of records,
both from the codebase, and the spelling of unit exponents (design §7.3).
-}
data Printer = Printer
  { refName :: RefNamer
  , fieldNames :: FieldNamer
  , spelling :: Spelling
  , unitName :: Text -> Text
  -- ^ how the full name of a unit or chart prints (design §7.6)
  , nonlinear :: Rational
  -- ^ the threshold over which a value prints marked non-linear (design §3.2)
  }

{- | A printer that knows no field names, for callers without a codebase:
records print positionally, in ASCII, with the default threshold.
-}
plainPrinter :: RefNamer -> Printer
plainPrinter namer =
  Printer
    { refName = namer
    , fieldNames = \_ _ n -> replicate n Nothing
    , spelling = Ascii
    , unitName = id
    , nonlinear = 1 / 100
    }

{- | A measure of non-linearity (design §3.2): the operation, and its
second-order statistical term as a percentage of the first-order σ.
-}
skewText :: Skew -> Text
skewText sk =
  sk.operation
    <> ", second-order term "
    <> maybe
      "unbounded"
      (\r -> renderRadius (100 * fst (sqrtApprox 4 r)) <> "% of the first-order σ")
      sk.ratioSq

-- | The warning a value prints with when a component is marked non-linear.
nonLinearNote :: Rational -> [Magnitude] -> Text
nonLinearNote threshold ms = case mapMaybe (nonLinearAt threshold) ms of
  [] -> ""
  sk : _ -> " (non-linear: " <> skewText sk <> "; a mean and a σ do not describe it)"

{- | Print a value. A tensor with a display unit whose dimension matches
prints its magnitudes in that unit (design §3.2.12); otherwise in SI base
units. Unit names go through the namer so that a renamed unit prints under
its current name.
-}
renderValue :: Printer -> Int -> Preferences -> Value -> Either EvalError Text
renderValue printer scale prefs = renderValueWith printer scale prefs (renderMagnitude scale)

-- | 'renderValue' with a chosen rendering for each magnitude.
renderValueWith ::
  Printer ->
  Int ->
  Preferences ->
  (Magnitude -> Text) ->
  Value ->
  Either EvalError Text
renderValueWith printer scale prefs showMagnitude = \case
  VBool True -> Right "true"
  VBool False -> Right "false"
  VClosure _ -> Right "<function>"
  -- Unreachable: a polymorphic value is instantiated before it is printed.
  VTyAbs{} -> Right "<polymorphic value>"
  -- Tuples as written; a list by walking its spine.
  VData (TupleC _) fields -> do
    parts <- mapM (>>= recur) fields
    pure ("(" <> T.intercalate ", " parts <> ")")
  v@(VData c _) | c == ConsC || c == NilC -> do
    items <- listItems v
    parts <- mapM recur items
    pure ("{" <> T.intercalate ", " parts <> "}")
  -- A record, when every field of its constructor is named, prints as it is
  -- built (design §2.3); braces delimit each field, so none needs parentheses.
  VData c@(UserCon h i) fields
    | not (null fields)
    , Just names <- sequence (printer.fieldNames h i (length fields)) -> do
        parts <- mapM (>>= recur) fields
        pure
          ( conText c
              <> " {"
              <> T.intercalate ", " (zipWith (\n s -> n <> " = " <> s) names parts)
              <> "}"
          )
  VData c fields -> do
    parts <- mapM (>>= \v -> fieldText v <$> recur v) fields
    pure (T.unwords (conText c : parts))
  -- A point prints on the chart it was written on (design §3.10, F6):
  -- its coordinates, the step divided out, then the chart's name; on a
  -- chart with no name, as coordinates in base units from its origin.
  VPoint dims d s buf -> do
    xs <- sequence (V.toList buf)
    pure $ case (chartName s, coordinatesOn (scale + 4) s xs) of
      (Just named, Right steps) ->
        renderNested showMagnitude dims steps
          <> " "
          <> named
          <> nonLinearNote printer.nonlinear steps
      _ ->
        renderNested showMagnitude dims xs
          <> unitSuffix d
          <> " (point)"
          <> nonLinearNote printer.nonlinear xs
  VChart s ->
    Right $ case chartName s of
      Just named -> "chart " <> named
      Nothing ->
        "chart: step "
          <> showMagnitude s.step
          <> " at "
          <> renderNested showMagnitude s.dims (V.toList s.origin)
          <> unitSuffix s.dim
  -- A unit prints as its unit expression, written as a type's dimension is
  -- (design §3.10, U8), so that it reads back as unit arithmetic: `km`,
  -- `km/h`, `kg*m/s^2`; one whose units all cancel keeps them as written,
  -- `km/km` (U9). One whose expression does not give its size, its hint
  -- lost, prints as the amount of one of it, marked.
  VUnit v -> case v of
    VTensor [] d (Just h) buf
      | h.dim == d
      , not (null h.atoms)
      , Right m <- V.head buf
      , midpoint m == midpoint h.factor ->
          Right (unitExpressionText printer h)
    _ -> (<> " (a unit)") <$> recur v
  v -> do
    (dims, scaled, units) <- displayParts printer scale prefs v
    pure
      ( renderNested showMagnitude dims scaled
          <> (if T.null units then "" else " " <> units)
          <> nonLinearNote printer.nonlinear scaled
      )
 where
  recur = renderValueWith printer scale prefs showMagnitude
  -- A chart's name; an instant of a moving chart is the chart applied, as
  -- it is written, @(ecef (100 unix))@ (design §3.8).
  chartName s = case (s.name, s.applied) of
    (Just atom, Applied []) -> Just (atomNameWith printer.unitName atom)
    (Just atom, Applied args)
      | Right texts <- mapM (>>= recur) args ->
          Just
            ( "("
                <> T.unwords (atomNameWith printer.unitName atom : map argument texts)
                <> ")"
            )
    _ -> Nothing
  argument t = if T.any (== ' ') t then "(" <> t <> ")" else t
  unitSuffix d = case renderUnitsIn printer.spelling d of
    "" -> ""
    units -> " " <> units

{- | A unit's hint as unit arithmetic (design §3.10, U8): the units with
positive powers in the order written, joined by @*@ (@·@ in unicode),
then @/@ and those with negative powers, grouped when there are several;
@s^-1@ when there are only negative powers, since @1/s@ would be an
amount over a unit.
-}
unitExpressionText :: Printer -> UnitHint -> Text
unitExpressionText printer h = case (ups, downs) of
  ([], _) -> product' [(u, k) | (u, k) <- [(u.atom, u.power) | u <- h.atoms]]
  (_, []) -> product' ups
  (_, [one]) -> product' ups <> "/" <> product' [one]
  _ -> product' ups <> "/(" <> product' downs <> ")"
 where
  ups = [(u.atom, u.power) | u <- h.atoms, u.power > 0]
  downs = [(u.atom, negate u.power) | u <- h.atoms, u.power < 0]
  product' = T.intercalate (productText printer.spelling) . map factor
  factor (atom, k) =
    atomNameWith printer.unitName atom
      <> (if k == 1 then "" else exponentText printer.spelling (toInteger k))

-- | The current name of a unit or chart atom.
atomNameWith :: (Text -> Text) -> UnitAtom -> Text
atomNameWith named = \case
  UnitNamed n -> named n
  UnitBase u -> u

{- | What a tensor prints as: its shape, its magnitudes in the display unit
(or in base units), and the unit text. Forces every element.
-}
displayParts ::
  Printer ->
  Int ->
  Preferences ->
  Value ->
  Either EvalError ([Int], [Magnitude], Text)
displayParts printer scale prefs = \case
  VTensor dims d hint buf -> do
    rs <- sequence (V.toList buf)
    -- The display rule of design §3.2.12, in order: a unit chosen with `to`;
    -- a declared preference for this exact dimension; the units the value
    -- was written in; base units.
    let chosen = case hint of
          Just h | h.pinned -> Just h
          _ -> Map.lookup d prefs <|> hint
    pure $ case chosen of
      Just h
        | h.dim == d
        , midpoint h.factor /= 0
        , Right converted <- mapM (\r -> divM (scale + 4) r h.factor) rs ->
            (dims, converted, renderHint h)
      _ -> (dims, rs, renderUnitsIn printer.spelling d)
  _ -> Left (Internal "expected a tensor")
 where
  -- Positive exponents first, otherwise in the order the units appeared.
  renderHint h =
    T.unwords
      [ atomNameWith printer.unitName u.atom
          <> (if u.power == 1 then "" else exponentText printer.spelling u.power)
      | u <- filter ((> 0) . (.power)) h.atoms ++ filter ((< 0) . (.power)) h.atoms
      ]

{- | The raw form of a magnitude for @:exact@ (design §3.2.10): the rational,
or the midpoint, every nudge with its kind and origin, and the slack.
-}
renderExact :: RefNamer -> Int -> Magnitude -> Text
renderExact namer scale = \case
  Exact r -> renderRational scale r
  m@(Affine mid _ slack _) ->
    renderRational scale mid
      <> T.concat
        [ " + " <> renderRational 6 c <> "·e[" <> renderNudge namer n <> "]"
        | (c, n) <- nudges m
        ]
      <> (if slack > 0 then "  ± " <> renderRational 6 slack else "")

renderNudge :: RefNamer -> Nudge -> Text
renderNudge namer n = kindName n.kind <> ", " <> originName namer n.origin

kindName :: NudgeKind -> Text
kindName = \case
  Bound -> "bound"
  Stat -> "σ"

originName :: RefNamer -> Origin -> Text
originName namer = \case
  Tagged l i -> l <> (if i == 0 then "" else "." <> tshow i)
  Declared h path i ->
    namer h Nothing ""
      <> (if null path then "" else " @" <> T.intercalate "." (map tshow path))
      <> (if i == 0 then "" else "." <> tshow i)
  A.Builtin name -> name

{- | The error budget of a magnitude (design §3.2.6): the collapsed value,
then every nudge with its contribution and share, largest first. Bound
nudges share the bound radius, statistical nudges the variance.
-}
renderBudget :: RefNamer -> Int -> Rational -> Text -> Magnitude -> [Text]
renderBudget namer scale threshold units m = case m of
  Exact _ -> [renderMagnitude scale m <> suffix, "exact"]
  _ ->
    let c = collapse m
        rows =
          [ (kindName n.kind, originName namer n.origin, contribution, share)
          | (coeff, n) <- nudges m
          , let contribution = renderRadius (abs coeff) <> suffix
          , let share = case n.kind of
                  Bound -> percent (abs coeff) c.bound <> " of bound"
                  Stat -> percent (coeff * coeff) c.variance <> " of σ²"
          ]
        slackRow = case m of
          Affine _ _ s _
            | s > 0 ->
                [("bound", "slack", renderRadius s <> suffix, percent s c.bound <> " of bound")]
          _ -> []
        -- The operation that marked it, which no nudge holds (design §3.2).
        marked = case nonLinearAt threshold m of
          Just sk ->
            ["  non-linear: " <> skewText sk <> "; a mean and a σ do not describe it"]
          Nothing -> []
     in (renderMagnitude scale m <> suffix)
          : table (("kind", "source", "contribution", "share") : rows ++ slackRow)
          ++ marked
 where
  suffix = if T.null units then "" else " " <> units
  percent part whole
    | whole == 0 = "0%"
    | otherwise = tshow (round (100 * part / whole) :: Integer) <> "%"
  table rows =
    let (wa, wb, wc) =
          foldr
            ( \(a, b, c, _) (x, y, z) -> (max x (T.length a), max y (T.length b), max z (T.length c))
            )
            (0, 0, 0)
            rows
     in [ "  "
            <> T.justifyLeft wa ' ' a
            <> "  "
            <> T.justifyLeft wb ' ' b
            <> "  "
            <> T.justifyLeft wc ' ' c
            <> "  "
            <> d
        | (a, b, c, d) <- rows
        ]

-- | Print a flat row-major buffer as nested brackets according to its shape.
renderNested :: (a -> Text) -> [Int] -> [a] -> Text
renderNested showElem dims xs = case dims of
  [] -> case xs of
    x : _ -> showElem x
    [] -> "[]"
  -- Rows with ;, planes with ;; (§2.4). A tensor whose outermost axis has
  -- length one would read back with a lower rank, so it stays nested.
  d : _
    | d /= 1 || length dims == 1 -> "[" <> separated dims xs <> "]"
  d : rest ->
    let stride = product rest
     in "["
          <> T.intercalate
            ", "
            [ renderNested showElem rest (take stride (drop (i * stride) xs))
            | i <- [0 .. d - 1]
            ]
          <> "]"
 where
  separated ds es = case ds of
    [_] -> T.intercalate ", " (map showElem es)
    d : rest ->
      let stride = product rest
       in T.intercalate
            (T.replicate (length rest) ";" <> " ")
            [separated rest (take stride (drop (i * stride) es)) | i <- [0 .. d - 1]]
    [] -> T.intercalate ", " (map showElem es)

-- Terms --------------------------------------------------------------------------

{- | How to print a reference: the codebase decides between a current name,
a stale @name#hash@, and a bare @#hash@ (design §7.2).
-}
type RefNamer = Hash -> Maybe Int -> Text -> Text

{- | Print a term as surface syntax, given names for the variables in scope
(innermost first). Binder hints become names; de Bruijn indices make
shadowing faithful even when hints repeat.
-}
renderTerm :: RefNamer -> Vec n Text -> Term n -> Text
renderTerm = renderTermIn Ascii

{- | 'renderTerm' in a chosen spelling (design §7.3): in unicode, @λx → x²@
for @\\x -> x^2@, and @≤ ≥ ≠ ∨@ for @<= >= /= ||@.
-}
renderTermIn :: Spelling -> RefNamer -> Vec n Text -> Term n -> Text
renderTermIn spelling namer = renderTermUnits spelling namer (\_ _ _ -> False)

{- | A definition as its parameters and its body (design §3.8): the leading
lambdas of a moving chart are its parameters, written before the @=@ as a
function's are, @chart ecef t = …@, since a chart's right-hand side is not
an expression and a lambda before it would not read back.
-}
renderParamsUnits :: Spelling -> RefNamer -> UnitRef -> Term Z -> ([Text], Text)
renderParamsUnits spelling namer isUnitRef = peel VNil []
 where
  peel :: Vec n Text -> [Text] -> Term n -> ([Text], Text)
  peel ctx acc = \case
    Lam (Hint h) b -> let h' = fresh h ctx in peel (VCons h' ctx) (acc ++ [h']) b
    t -> (acc, renderTermUnits spelling namer isUnitRef ctx t)
  fresh :: Text -> Vec n Text -> Text
  fresh h ctx
    | T.null h || "§" `T.isPrefixOf` h || h == "_" = fresh "x" ctx
    | h `elem` vecToList ctx = fresh (h <> "'") ctx
    | otherwise = h

{- | Whether a reference, written under a name, is a declared unit: what the
printer needs to write a chart's origin as a quantity, @[2, 0, 1] km site@,
which only reads back when @km@ is a unit (design §3.8).
-}
type UnitRef = Hash -> Maybe Int -> Text -> Bool

{- | 'renderTermIn' that knows which references are units. Without that
knowledge a chart's origin before its parent is parenthesised, which reads
back the same.
-}
renderTermUnits ::
  Spelling -> RefNamer -> UnitRef -> Vec n Text -> Term n -> Text
renderTermUnits spelling namer isUnitRef = go 0
 where
  arrow = arrowText spelling
  go :: Int -> Vec m Text -> Term m -> Text
  go prec ctx t = case t of
    Var i -> lookupVar i ctx
    Ref h idx (Hint written) ->
      let name = namer h idx written
       in paren (prec > 10 && T.any (== '#') name) name
    Lit (LTensor ([], [r]))
      | r < 0 -> paren (prec > 8) (renderRational 20 r)
      | otherwise -> renderRational 20 r
    Lit (LTensor (dims, rs)) -> renderNested (renderRational 20) dims rs
    Lam (Hint h) b ->
      let h' = freshen h ctx
          lambda = if spelling == Unicode then "λ" else "\\"
       in paren (prec > 0) (lambda <> h' <> arrow <> go 0 (VCons h' ctx) b)
    App f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
    Let (Hint h) e b ->
      let h' = freshen h ctx
       in paren
            (prec > 0)
            ("let " <> h' <> " = " <> go 0 ctx e <> " in " <> go 0 (VCons h' ctx) b)
    Con c args -> case (c, args) of
      (TrueC, []) -> "true"
      (FalseC, []) -> "false"
      (TupleC _, _) -> "(" <> T.intercalate ", " (map (go 0 ctx) args) <> ")"
      (NilC, []) -> "{}"
      (ConsC, [x, xs]) -> case listSpine xs of
        Just items -> "{" <> T.intercalate ", " (map (go 0 ctx) (x : items)) <> "}"
        Nothing -> paren (prec > 4) (go 5 ctx x <> " : " <> go 4 ctx xs)
      _ ->
        paren
          (prec > 10 && not (null args))
          (T.unwords (conText c : map (go 11 ctx) args))
    -- A case on Bool reads back as the if it came from.
    Case sc [Alt FalseC VNil el, Alt TrueC VNil th] ->
      paren
        (prec > 0)
        ("if " <> go 0 ctx sc <> " then " <> go 0 ctx th <> " else " <> go 0 ctx el)
    Case sc alts ->
      paren
        (prec > 0)
        ("case " <> go 0 ctx sc <> " of " <> T.intercalate "; " (map alt alts))
     where
      alt (Alt c hs b) =
        let names = freshenAll (vecMap (\(Hint h) -> h) hs) ctx
            ctx' = vecAppend names ctx
         in patternText c (vecToList names) <> arrow <> go 0 ctx' b
    -- A superscript must be glued to the atom it raises (§2.8); after
    -- anything else, a `#label` or a stale `x#hash` included, the power
    -- keeps its caret.
    Pow b n ->
      let base = go 10 ctx b
          word c = isAlphaNum c || c == '_' || c == '\''
          glues = case T.unsnoc base of
            Just (_, c)
              | c == ')' || c == ']' -> True
              | word c -> not ("#" `T.isSuffixOf` T.dropWhileEnd word base)
            _ -> False
       in paren
            (prec > 9)
            (base <> exponentText (if glues then spelling else Ascii) n)
    Noise Bound l n -> "noise " <> tshow n <> renderLabel l
    Noise Stat l n -> "gauss " <> tshow n <> renderLabel l
    Uncertain k l x e ->
      paren
        (prec > 5)
        ( go 6 ctx x
            <> (if k == Bound then " ± " else " ±σ ")
            <> go 6 ctx e
            <> renderLabel l
        )
    Pack ts -> "[" <> T.intercalate ", " (map (go 0 ctx) ts) <> "]"
    Proj b i -> go 11 ctx b <> "." <> tshow i
    Cycle hints bodies ->
      -- Only reached when a whole cycle is printed; members are normally
      -- viewed one at a time through 'renderTerm' on a body.
      let ctx' = vecAppend (vecMap (\(Hint h) -> h) hints) ctx
       in T.intercalate
            "; "
            [ h <> " = " <> go 0 ctx' b
            | (Hint h, b) <- zip (vecToList hints) (vecToList bodies)
            ]
    PrimApp p args -> prim prec ctx p args

  prim :: Int -> Vec m Text -> Text -> [Term m] -> Text
  prim prec ctx p args = case (binary p, args) of
    -- A quantity reads back as one (design §3.10, U4, U5): its unit written
    -- after the literal, bare when it is one unit or a chain of declared
    -- units that the quantity takes in (`9.81 m / s^2`), in parentheses
    -- otherwise (`3 (km * (m / s))`, `3 (u / s)`).
    -- A negative number is written before the quantity, `-3 K`, which
    -- reads back as the same term.
    (_, [x, rawUnit])
      | p == "scale" ->
          let u = fromMaybe rawUnit (unitSyntax rawUnit)
              (lit, level) = case x of
                Lit (LTensor ([], [r])) | r < 0 -> (renderRational 20 r, 8)
                -- Below an application: raised, it is parenthesised.
                _ -> (go 11 ctx x, 9)
           in if unitLeaf u || isLocal u
                then paren (prec > level) (lit <> " " <> go 9 ctx u)
                else
                  if unitChain u
                    then paren (prec > 7) (lit <> " " <> go 7 ctx u)
                    else paren (prec > level) (lit <> " (" <> go 0 ctx u <> ")")
    -- A unit's declaration prints as its body (U7): `unit km = kilo * 1 metre`.
    (_, [x]) | p == "unit" -> go prec ctx (fromMaybe x (compoundSyntax x))
    -- Points and charts read back as they are written (design §3.6, §3.8).
    (_, [s, Lit (LTensor ([], [r]))])
      | p == "pointOn" ->
          paren (prec > 10) (renderRational 20 r <> " " <> go 11 ctx s)
    -- A chart reads back as its clauses (design §3.10, F10): its parent
    -- after `on`, a space by its type's name, then each clause written,
    -- in the order @at@, @step@, @by@, @spinning@. The frame and axes it
    -- mints are its declaration's, not written.
    (_, [_, _, Con (UserCon h 0) [], st, o, g, w])
      | p == "mkRoot"
      , Just cl <- clauses ctx st o g w ->
          paren (prec > 0) (T.unwords ("on" : showHash h : cl))
    (_, [_, _, par, st, o, g, w])
      | p == "mkChart"
      , Just cl <- clauses ctx st o g w ->
          paren (prec > 0) (T.unwords ("on" : go 11 ctx par : cl))
    -- A conversion from a configuration (design §3.10, F7).
    (_, [a, b, c])
      | p `elem` ["fromTo", "axesFromTo"] ->
          paren
            (prec > 1)
            (go 2 ctx a <> " from " <> go 2 ctx b <> " to " <> go 2 ctx c)
    (Just (sym, lvl, assoc), [a, b]) ->
      let (lp, rp) = case assoc of
            L -> (lvl, lvl + 1)
            R -> (lvl + 1, lvl)
            N -> (lvl + 1, lvl + 1)
       in paren (prec > lvl) (go lp ctx a <> " " <> spellOp sym <> " " <> go rp ctx b)
    _ -> case (p, args) of
      -- `-3` reads back as the constant minus three (core.md §6), so the
      -- primitive applied to a constant keeps its name.
      ("neg", [a@(Lit _)]) -> paren (prec > 10) ("neg " <> go 11 ctx a)
      -- So does a quantity of a constant, which `-` would fold into it.
      ("neg", [a@(PrimApp "scale" [Lit _, _])]) ->
        paren (prec > 10) ("neg " <> go 11 ctx a)
      ("neg", [a]) -> paren (prec > 8) ("-" <> go 9 ctx a)
      -- A slice along a later axis reads back as its wildcards, `m._.0`
      -- (design §2.10); along axis 0 it keeps its name, since `m.0` is a
      -- projection, another term.
      ("slice", [Lit (LTensor ([], [rk])), Lit (LTensor ([], [ri])), t])
        | denominator rk == 1
        , rk >= 1
        , denominator ri == 1
        , ri >= 0 ->
            go 11 ctx t
              <> T.replicate (fromIntegral (numerator rk)) "._"
              <> "."
              <> tshow (numerator ri)
      (_, []) -> p
      _ -> paren (prec > 10) (T.unwords (p : map (go 11 ctx) args))

  paren b s = if b then "(" <> s <> ")" else s

  -- A chart's clauses (design §3.10, F10), each a list of none or one
  -- (the generators of any number), each running to the next clause word,
  -- so none needs parentheses.
  clauses :: Vec m Text -> Term m -> Term m -> Term m -> Term m -> Maybe [Text]
  clauses ctx st o g w = do
    sts <- listSpine st
    os <- listSpine o
    gs <- listSpine g
    ws <- listSpine w
    let one word = map (\x -> word <> " " <> go 1 ctx x)
    pure
      ( one "at" os
          ++ one "step" sts
          ++ ["by " <> T.intercalate " then " (map (go 1 ctx) gs) | not (null gs)]
          ++ one "spinning" ws
      )
  -- A declared unit, or one to a power: what a quantity takes in (U5).
  -- Invert the internal construction of compound units. In particular,
  -- scale 1 is scaffolding here, not a literal in the printed unit syntax.
  unitSyntax :: Term m -> Maybe (Term m)
  unitSyntax u = case u of
    PrimApp "unit" [x] -> compoundSyntax x
    _ | unitAtom u -> Just u
    _ -> Nothing
  compoundSyntax :: Term m -> Maybe (Term m)
  compoundSyntax x = case x of
    PrimApp op [_, _] | op `elem` ["outer", "div"] -> amountSyntax x
    Pow{} -> amountSyntax x
    _ -> Nothing
  amountSyntax :: Term m -> Maybe (Term m)
  amountSyntax = \case
    PrimApp "scale" [Lit (LTensor ([], [1])), u] -> unitSyntax u
    PrimApp op [a, b]
      | op `elem` ["outer", "div"] ->
          (\x y -> PrimApp op [x, y]) <$> amountSyntax a <*> amountSyntax b
    Pow a n -> (`Pow` n) <$> amountSyntax a
    _ -> Nothing

  unitLeaf :: Term m -> Bool
  unitLeaf = \case
    Pow b _ -> unitAtom b
    u -> unitAtom u
  -- Units joined by * and /, each joined on the right a unit leaf: a chain
  -- the quantity takes in when written bare.
  unitChain :: Term m -> Bool
  unitChain = \case
    PrimApp op [l, r]
      | op `elem` ["outer", "div"] -> unitLeaf r && (unitLeaf l || unitChain l)
    _ -> False
  isLocal :: Term m -> Bool
  isLocal = \case
    Var _ -> True
    _ -> False
  unitAtom :: Term m -> Bool
  unitAtom = \case
    PrimApp u [] -> isJust (baseUnit u)
    Ref h idx (Hint w) -> isUnitRef h idx w
    _ -> False

  -- The operators with a unicode spelling the printer does not already use
  -- (§2.8); `*` stays, since `×` is the cross product.
  spellOp sym = case spelling of
    Ascii -> sym
    Unicode -> case sym of
      "<=" -> "≤"
      ">=" -> "≥"
      "/=" -> "≠"
      "||" -> "∨"
      _ -> sym

  -- A hint that is already in scope would capture an outer variable the
  -- body may still refer to, so the printed binder gets a prime (or a
  -- name if the hint is blank, or one the desugarer made up for a section
  -- or a composition, `§s0`, which is not an identifier). De Bruijn
  -- indices make the term itself unambiguous; this keeps the printed text
  -- so.
  -- Fresh names for a group of binders entering scope together.
  freshenAll :: forall j m. Vec j Text -> Vec m Text -> Vec j Text
  freshenAll hs ctx = case hs of
    VNil -> VNil
    VCons h rest ->
      let h' = freshen h (vecAppend rest ctx)
       in VCons h' (freshenAll rest (VCons h' ctx))
  freshen :: Text -> Vec m Text -> Text
  freshen h ctx
    | h == "_" = h -- binds nothing, so it never captures
    | T.null h || "§" `T.isPrefixOf` h = freshen "x" ctx
    | h `elem` vecToList ctx = freshen (h <> "'") ctx
    | otherwise = h

  lookupVar :: Fin m -> Vec m Text -> Text
  lookupVar i ctx = case (i, ctx) of
    (FZ, VCons x _) -> x
    (FS j, VCons _ xs) -> lookupVar j xs

data Assoc = L | R | N

{- | Operator symbol, precedence level (as in design §2.5) and associativity
for the binary primitives.
-}
binary :: Text -> Maybe (Text, Int, Assoc)
binary = \case
  "outer" -> Just ("*", 7, L)
  "dot" -> Just ("·", 7, L)
  "wedge" -> Just ("∧", 7, L)
  "emul" -> Just ("⊙", 7, L)
  "ediv" -> Just ("⊘", 7, L)
  "div" -> Just ("/", 7, L)
  "add" -> Just ("+", 6, L)
  "sub" -> Just ("-", 6, L)
  -- A point and an amount (design §3.6): `.+` and `.-` are the primitives
  -- always, so they read back as they are written.
  "pointAdd" -> Just (".+", 6, L)
  "pointSub" -> Just (".-", 6, L)
  "eq" -> Just ("==", 4, N)
  "ne" -> Just ("/=", 4, N)
  "lt" -> Just ("<", 4, N)
  "le" -> Just ("<=", 4, N)
  "gt" -> Just (">", 4, N)
  "ge" -> Just (">=", 4, N)
  "and" -> Just ("&&", 3, R)
  "or" -> Just ("||", 2, R)
  "to" -> Just ("to", 1, N)
  -- A point or an amount to a chart (design §3.10, F5, F10).
  "toChart" -> Just ("to", 1, N)
  "toAxes" -> Just ("to", 1, N)
  _ -> Nothing

-- | A magnitude to two significant digits, for radii and bias boxes.
renderRough :: Magnitude -> Text
renderRough m = renderRadius (abs (midpoint m))

-- | The elements of a list value, forcing its spine.
listItems :: Value -> Either EvalError [Value]
listItems = \case
  VData NilC [] -> Right []
  VData ConsC [x, xs] -> do
    x' <- x
    rest <- xs >>= listItems
    pure (x' : rest)
  _ -> Left (Internal "not a list")

-- | The remaining elements of a literal list spine, if it ends in @{}@.
listSpine :: Term n -> Maybe [Term n]
listSpine = \case
  Con NilC [] -> Just []
  Con ConsC [x, xs] -> (x :) <$> listSpine xs
  _ -> Nothing

{- | A field of a printed data value must read back as one argument: anything
but a single token goes in parentheses, @Rect (1 m) (2 m)@, since @m s^-1@
after an argument would raise the whole application to the power.
-}
fieldText :: Value -> Text -> Text
fieldText v s
  | selfDelimited s = s
  | VData _ (_ : _) <- v = paren
  | T.isPrefixOf "-" s || T.any (== ' ') s = paren
  | otherwise = s
 where
  paren = "(" <> s <> ")"

{- | A bracketed group that closes at its last character, @ or @(a, b)@,
needs no parentheses; @[1, 2] km@ does.
-}
selfDelimited :: Text -> Bool
selfDelimited s = case (T.uncons s, T.unsnoc s) of
  (Just (open, _), Just (_, close))
    | Just close' <- lookup open [('(', ')'), ('[', ']'), ('{', '}')]
    , close == close' ->
        closesAtEnd 0 (T.unpack s)
  _ -> False
 where
  closesAtEnd :: Int -> String -> Bool
  closesAtEnd depth = \case
    [] -> False
    [c] -> depth == 1 && c `elem` (")]}" :: String)
    c : rest
      | c `elem` ("([{" :: String) -> closesAtEnd (depth + 1) rest
      | c `elem` (")]}" :: String) -> depth > 1 && closesAtEnd (depth - 1) rest
      | otherwise -> closesAtEnd depth rest

-- Re-spelling input ---------------------------------------------------------------

{- | An input line in its unicode spelling (design §2.8, §7.3), for the echo
under @:set unicode on@: the tokens as written, each one with a unicode form
re-spelled at its span, every other character kept. @2 +-s 0.1@ becomes
@2 ±σ 0.1@ and @\\x -> x^2 <= 4@ becomes @λx → x² ≤ 4@. Names keep their
spelling, @sqrt@ included, since @√@ is a prefix operator that would bind
differently, and so do @*@, @/@ and @&&@. A caret power becomes a
superscript only when it is glued to an atom and its exponent is an integer
literal. 'Nothing' when the input does not lex, nothing changes, or the
result would not lex to the same tokens.
-}
respell :: Text -> Maybe Text
respell src = do
  let text = L.prepare src
  toks <- either (const Nothing) Just (L.tokenize text)
  let edits = respellEdits text toks
      out = applyEdits text edits
  toks' <- either (const Nothing) Just (L.tokenize out)
  -- A superscript stands for its caret form, and `·` for the `@` it
  -- replaces (an expression's matrix product); nothing else may differ.
  let caret = concatMap $ \case
        L.TSup n -> [L.TOp "^"] ++ [L.TOp "-" | n < 0] ++ [L.TNum (fromInteger (abs n))]
        L.TOp "·" -> [L.TOp "@"]
        t -> [t]
  if not (null edits) && caret (map (.value) toks') == caret (map (.value) toks)
    then Just out
    else Nothing

-- | Replacements as character offsets @[from, to)@ into the text, in order.
respellEdits :: Text -> [L.Located L.Token] -> [(Int, Int, Text)]
respellEdits text = go Nothing
 where
  go :: Maybe (L.Located L.Token) -> [L.Located L.Token] -> [(Int, Int, Text)]
  go _ [] = []
  go prev (t : ts)
    -- A caret power with an integer literal exponent, glued throughout.
    | L.TOp "^" <- t.value
    , Just p <- prev
    , p.span.to == t.span.from
    , endsAtom p.value
    , (neg, rest) <- case ts of
        m : more | m.value == L.TOp "-", m.span.from == t.span.to -> (Just m, more)
        _ -> (Nothing, ts)
    , n : rest' <- rest
    , L.TNum r <- n.value
    , denominator r == 1
    , n.span.from == maybe t.span.to (\m -> m.span.to) neg
    , T.all (`elem` ("0123456789" :: String)) (slice n.span) =
        let k = numerator r * maybe 1 (const (-1)) neg
         in (offset t.span.from, offset n.span.to, exponentText Unicode k)
              : go (Just n) rest'
    | Just (ascii, uni) <- spelled t.value
    , slice t.span == ascii
    , not (gluedLambda t) =
        (offset t.span.from, offset t.span.to, uni) : go (Just t) ts
    | otherwise = go (Just t) ts

  -- `f\x` must not become the one identifier `fλx`.
  gluedLambda t =
    t.value == L.TLambda
      && maybe False (isIdentChar . snd) (T.unsnoc (T.take (offset t.span.from) text))
  isIdentChar c = isAlphaNum c || c == '_' || c == '\''

  slice sp = T.take (offset sp.to - offset sp.from) (T.drop (offset sp.from) text)

  -- Megaparsec's columns: a tab advances to the next multiple of eight.
  lineStarts = scanl (\acc l -> acc + T.length l + 1) 0 (T.splitOn "\n" text)
  offset (S.Pos l c) =
    let start = lineStarts !! (l - 1)
        walk col i s
          | col >= c = i
          | otherwise = case T.uncons s of
              Nothing -> i
              Just ('\t', s') -> walk (col + 8 - ((col - 1) `rem` 8)) (i + 1) s'
              Just (_, s') -> walk (col + 1) (i + 1) s'
     in start + walk (1 :: Int) 0 (T.takeWhile (/= '\n') (T.drop start text))

  -- The atoms a superscript may be glued to, as the lexer allows.
  endsAtom = \case
    L.TIdent _ -> True
    L.TRParen -> True
    L.TRBracket -> True
    L.TProj _ -> True
    L.TWild -> True
    L.TField _ -> True
    L.TAbs _ -> True
    L.TNum _ -> True
    L.TSup _ -> True
    L.TKw L.KTrue -> True
    L.TKw L.KFalse -> True
    _ -> False

  -- Tokens with a unicode form (design §2.8): the ASCII text and its replacement.
  spelled :: L.Token -> Maybe (Text, Text)
  spelled = \case
    L.TPlusMinus Stat -> Just ("+-s", "±σ")
    L.TPlusMinus Bound -> Just ("+-", "±")
    L.TArrow -> Just ("->", "→")
    L.TLambda -> Just ("\\", "λ")
    L.TOp "<=" -> Just ("<=", "≤")
    L.TOp ">=" -> Just (">=", "≥")
    L.TOp "/=" -> Just ("/=", "≠")
    L.TOp "||" -> Just ("||", "∨")
    L.TOp "@" -> Just ("@", "·")
    L.TOp "×" -> Just ("><", "×")
    L.TOp "/\\" -> Just ("/\\", "∧")
    L.TOp ".*" -> Just (".*", "⊙")
    L.TOp "./" -> Just ("./", "⊘")
    L.TOp "." -> Just (".", "∘")
    _ -> Nothing

-- | Splice replacements, given in order as offsets @[from, to)@, into a text.
applyEdits :: Text -> [(Int, Int, Text)] -> Text
applyEdits text = go 0
 where
  go at [] = T.drop at text
  go at ((from, to, new) : rest) = T.take (from - at) (T.drop at text) <> new <> go to rest
