{- | User-facing rendering (design §3.2.10, §7.2): values as decimals, and
Core terms back to surface syntax for @:view@.
-}
module Eval.Pretty (
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
  RefNamer,
) where

import Data.Char (intToDigit)
import Data.Map.Strict qualified as Map
import Data.Ratio ((%))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Eval.Affine hiding (Builtin)
import Eval.Affine qualified as A
import Eval.Core
import Eval.Dimension (renderUnits)
import Eval.Eval
import Eval.TCore (patternText)
import Eval.Type (conText)

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
          then renderDecimal scale True c.mid
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

{- | Print a value. A tensor with a display unit whose dimension matches
prints its magnitudes in that unit (design §3.2.12); otherwise in SI base
units. Unit names go through the namer so that a renamed unit prints under
its current name.
-}
renderValue :: RefNamer -> Int -> Preferences -> Value -> Either EvalError Text
renderValue namer scale prefs = renderValueWith namer scale prefs (renderMagnitude scale)

-- | 'renderValue' with a chosen rendering for each magnitude.
renderValueWith ::
  RefNamer ->
  Int ->
  Preferences ->
  (Magnitude -> Text) ->
  Value ->
  Either EvalError Text
renderValueWith namer scale prefs showMagnitude = \case
  VBool True -> Right "true"
  VBool False -> Right "false"
  VClosure _ -> Right "<function>"
  -- Tuples as written; a list by walking its spine.
  VData (Builtin "Tuple") fields -> do
    parts <- mapM (>>= renderValueWith namer scale prefs showMagnitude) fields
    pure ("(" <> T.intercalate ", " parts <> ")")
  v@(VData c _) | c == Builtin "Cons" || c == Builtin "Nil" -> do
    items <- listItems v
    parts <- mapM (renderValueWith namer scale prefs showMagnitude) items
    pure ("{" <> T.intercalate ", " parts <> "}")
  VData c fields -> do
    parts <-
      mapM
        (>>= \v -> fieldText v <$> renderValueWith namer scale prefs showMagnitude v)
        fields
    pure (T.unwords (conText c : parts))
  -- A point prints on the scale it was written on (design §3.6): steps from
  -- the origin, then the scale's name; without a scale, as an amount from
  -- the base origin in base units.
  VPoint dims d sc buf -> do
    xs <- sequence (V.toList buf)
    pure $ case sc of
      Just s
        | Just atom <- s.name
        , Right steps <-
            mapM
              (\(x, o) -> divM (scale + 4) (subM x o) s.step)
              (zip xs (V.toList s.origin)) ->
            renderNested showMagnitude dims steps <> " " <> atomNameWith namer atom
      _ ->
        renderNested showMagnitude dims xs
          <> (if T.null (renderUnits d) then "" else " " <> renderUnits d)
          <> " (point)"
  VScale s ->
    Right $ case s.name of
      Just atom -> "scale " <> atomNameWith namer atom
      Nothing ->
        "scale: step "
          <> showMagnitude s.step
          <> " at "
          <> renderNested showMagnitude s.dims (V.toList s.origin)
          <> (if T.null (renderUnits s.dim) then "" else " " <> renderUnits s.dim)
  v -> do
    (dims, scaled, units) <- displayParts namer scale prefs v
    pure
      ( renderNested showMagnitude dims scaled
          <> (if T.null units then "" else " " <> units)
      )

-- | The current name of a unit or scale atom.
atomNameWith :: RefNamer -> UnitAtom -> Text
atomNameWith _ = \case
  UnitNamed n -> n
  UnitBase u -> u

{- | What a tensor prints as: its shape, its magnitudes in the display unit
(or in base units), and the unit text. Forces every element.
-}
displayParts ::
  RefNamer ->
  Int ->
  Preferences ->
  Value ->
  Either EvalError ([Int], [Magnitude], Text)
displayParts namer scale prefs = \case
  VTensor dims d hint buf -> do
    rs <- sequence (V.toList buf)
    -- The display rule of design §3.2.12, in order: a unit chosen with `to`;
    -- a declared preference for this exact dimension; the units the value
    -- was written in; base units.
    let chosen = case hint of
          Just h | h.pinned -> Just h
          _ -> case Map.lookup d prefs of
            Just pref -> Just pref
            Nothing -> hint
    pure $ case chosen of
      Just h
        | h.dim == d
        , midpoint h.factor /= 0
        , Right converted <- mapM (\r -> divM (scale + 4) r h.factor) rs ->
            (dims, converted, renderHint h)
      _ -> (dims, rs, renderUnits d)
  _ -> Left (Internal "expected a tensor")
 where
  -- Positive exponents first, otherwise in the order the units appeared.
  renderHint h =
    T.unwords
      [ atomNameWith namer u.atom <> (if u.power == 1 then "" else "^" <> tshow u.power)
      | u <- filter ((> 0) . (.power)) h.atoms ++ filter ((< 0) . (.power)) h.atoms
      ]

{- | The raw form of a magnitude for @:exact@ (design §3.2.10): the rational,
or the midpoint, every nudge with its kind and origin, and the slack.
-}
renderExact :: RefNamer -> Int -> Magnitude -> Text
renderExact namer scale = \case
  Exact r -> renderRational scale r
  m@(Affine mid _ slack) ->
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
renderBudget :: RefNamer -> Int -> Text -> Magnitude -> [Text]
renderBudget namer scale units m = case m of
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
          Affine _ _ s
            | s > 0 ->
                [("bound", "slack", renderRadius s <> suffix, percent s c.bound <> " of bound")]
          _ -> []
     in (renderMagnitude scale m <> suffix)
          : table (("kind", "source", "contribution", "share") : rows ++ slackRow)
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
renderTerm namer = go 0
 where
  go :: Int -> Vec m Text -> Term m -> Text
  go prec ctx t = case t of
    Var i -> lookupVar i ctx
    Ref h idx (Hint written) -> namer h idx written
    Lit (LTensor ([], [r]))
      | r < 0 -> paren (prec > 8) (renderRational 20 r)
      | otherwise -> renderRational 20 r
    Lit (LTensor (dims, rs)) -> renderNested (renderRational 20) dims rs
    Lam (Hint h) b ->
      let h' = freshen h ctx
       in paren (prec > 0) ("\\" <> h' <> " -> " <> go 0 (VCons h' ctx) b)
    App f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
    Let (Hint h) e b ->
      let h' = freshen h ctx
       in paren
            (prec > 0)
            ("let " <> h' <> " = " <> go 0 ctx e <> " in " <> go 0 (VCons h' ctx) b)
    Con c args -> case (c, args) of
      (Builtin "True", []) -> "true"
      (Builtin "False", []) -> "false"
      (Builtin "Tuple", _) -> "(" <> T.intercalate ", " (map (go 0 ctx) args) <> ")"
      (Builtin "Nil", []) -> "{}"
      (Builtin "Cons", [x, xs]) -> case listSpine xs of
        Just items -> "{" <> T.intercalate ", " (map (go 0 ctx) (x : items)) <> "}"
        Nothing -> paren (prec > 4) (go 5 ctx x <> " : " <> go 4 ctx xs)
      _ ->
        paren
          (prec > 10 && not (null args))
          (T.unwords (conText c : map (go 11 ctx) args))
    -- A case on Bool reads back as the if it came from.
    Case sc [Alt (Builtin "False") VNil el, Alt (Builtin "True") VNil th] ->
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
         in patternText c (vecToList names) <> " -> " <> go 0 ctx' b
    Pow b n -> paren (prec > 9) (go 10 ctx b <> "^" <> tshow n)
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
    -- Points and scales read back as they are written (design §3.6).
    (_, [s, Lit (LTensor ([], [r]))])
      | p == "pointOn" ->
          paren (prec > 10) (renderRational 20 r <> " " <> go 11 ctx s)
    (_, [a, b]) | p == "mkScale" -> paren (prec > 0) (go 1 ctx a <> " at " <> go 1 ctx b)
    (Just (sym, lvl, assoc), [a, b]) ->
      let (lp, rp) = case assoc of
            L -> (lvl, lvl + 1)
            R -> (lvl + 1, lvl)
            N -> (lvl + 1, lvl + 1)
       in paren (prec > lvl) (go lp ctx a <> " " <> sym <> " " <> go rp ctx b)
    _ -> case (p, args) of
      -- `-3` reads back as the constant minus three (core.md §6), so the
      -- primitive applied to a constant keeps its name.
      ("neg", [a@(Lit _)]) -> paren (prec > 10) ("neg " <> go 11 ctx a)
      ("neg", [a]) -> paren (prec > 8) ("-" <> go 9 ctx a)
      (_, []) -> p
      _ -> paren (prec > 10) (T.unwords (p : map (go 11 ctx) args))

  paren b s = if b then "(" <> s <> ")" else s

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
  "eq" -> Just ("==", 4, N)
  "ne" -> Just ("/=", 4, N)
  "lt" -> Just ("<", 4, N)
  "le" -> Just ("<=", 4, N)
  "gt" -> Just (">", 4, N)
  "ge" -> Just (">=", 4, N)
  "and" -> Just ("&&", 3, R)
  "or" -> Just ("||", 2, R)
  "to" -> Just ("to", 1, N)
  _ -> Nothing

-- | A magnitude to two significant digits, for radii and bias boxes.
renderRough :: Magnitude -> Text
renderRough m = renderRadius (abs (midpoint m))

-- | The elements of a list value, forcing its spine.
listItems :: Value -> Either EvalError [Value]
listItems = \case
  VData (Builtin "Nil") [] -> Right []
  VData (Builtin "Cons") [x, xs] -> do
    x' <- x
    rest <- xs >>= listItems
    pure (x' : rest)
  _ -> Left (Internal "not a list")

-- | The remaining elements of a literal list spine, if it ends in @{}@.
listSpine :: Term n -> Maybe [Term n]
listSpine = \case
  Con (Builtin "Nil") [] -> Just []
  Con (Builtin "Cons") [x, xs] -> (x :) <$> listSpine xs
  _ -> Nothing

{- | A field of a printed data value must read back as one argument: anything
but a single token goes in parentheses, @Rect (1 m) (2 m)@, since @m s^-1@
after an argument would raise the whole application to the power.
-}
fieldText :: Value -> Text -> Text
fieldText v s
  | VData _ (_ : _) <- v = paren
  | T.isPrefixOf "-" s || T.any (== ' ') s = paren
  | otherwise = s
 where
  paren = "(" <> s <> ")"
