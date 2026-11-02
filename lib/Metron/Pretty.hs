{-# LANGUAGE PatternSynonyms #-}

{- | User-facing rendering (design §3.2.10, §7.2): values as decimals, and
Core terms back to surface syntax for @:view@.
-}
module Metron.Pretty (
  renderRational,
  renderValue,
  renderValueWith,
  Display (..),
  displayParts,
  renderTerm,
  renderTermIn,
  renderTermUnits,
  renderParamsUnits,
  UnitRef,
  RefNamer,
  FieldNamer,
  Printer (..),
  respell,
) where

import Control.Applicative ((<|>))
import Control.Monad (when)
import Data.Char (intToDigit, isAlphaNum)
import Data.Either (fromRight)
import Data.List (sortOn, unsnoc)
import Data.Map.Strict qualified as Map (lookup)
import Data.Maybe (fromMaybe, isJust)
import Data.Ratio (denominator, numerator, (%))
import Data.Text (Text)
import Data.Text qualified as T (
  all,
  any,
  concat,
  drop,
  dropWhileEnd,
  intercalate,
  isPrefixOf,
  isSuffixOf,
  justifyLeft,
  justifyRight,
  length,
  null,
  pack,
  replicate,
  splitOn,
  take,
  takeWhile,
  uncons,
  unpack,
  unsnoc,
  unwords,
 )
import Data.Vector qualified as V (empty, fromList, head, length, toList, (!))
import Data.Vector.Unboxed qualified as VU (
  Vector,
  enumFromN,
  filter,
  fromList,
  length,
  map,
  null,
  toList,
 )
import Metron.Builtin (
  pattern ConsC,
  pattern FalseC,
  pattern NilC,
  pattern TrueC,
  pattern TupleC,
 )
import Metron.Core (
  Alt (Alt),
  ConRef (UserCon),
  Fin (..),
  Hash,
  Hint (Hint),
  Lit (LTensor),
  Nat (S, Z),
  Term (..),
  Vec (..),
  etaHint,
  renderLabel,
  showHash,
  strengthen,
  vecAppend,
  vecMap,
  vecToList,
 )
import Metron.Dimension (
  Spelling (..),
  arrowText,
  exponentText,
  productText,
  renderUnitsIn,
 )
import Metron.Double (
  Dbl (..),
  Estimate (..),
  Layout (rounds),
  clusterNote,
  originNote,
  sampleNote,
  showDouble,
 )
import Metron.Eval (
  Applied (Applied),
  ChartOf (applied, dim, dims, name, origin, step),
  EvalError (Exceeded, Internal),
  Mixture (..),
  Narrowing (..),
  Option (..),
  ValueOf (..),
  coordinatesOn,
  narrow,
  placesWithin,
  pattern VBool,
 )
import Metron.Fixity (Assoc (..), Fixity (..), fixityOfPrim)
import Metron.Lexer qualified as L (
  Keyword (KFalse, KTrue),
  Located (span, value),
  Token (
    TAbs,
    TArrow,
    TField,
    TIdent,
    TKw,
    TLambda,
    TNum,
    TOp,
    TProj,
    TRBracket,
    TRParen,
    TSup,
    TWild
  ),
  prepare,
  tokenize,
 )
import Metron.Limits (Limit (OutcomeCount), inSorted)
import Metron.Numerical.Approx (Precision, decimalExponent)
import Metron.Numerical.Statistics qualified as Statistics
import Metron.Primitive (baseUnit)
import Metron.Rational (Rat (..))
import Metron.Scalar (
  Scalar (hintFactor, scatterM),
  Settings (inputSampling),
  settingsAt,
 )
import Metron.Syntax qualified as S (Pos (Pos), Span (from, to))
import Metron.TCore (patternText)
import Metron.Type (conText)
import Metron.UnitHint (
  Preferences,
  UnitAtom (..),
  UnitFactor (atom, power),
  UnitHint (atoms, dim, factor, pinned),
 )
import Numeric (showFFloat)

-- Numbers ------------------------------------------------------------------------

{- | @renderRational precision r@: an exact value in full, or truncated at
@precision@ significant digits with @…@ when the expansion goes on. The
integer part is always complete. Values below @10^-4@ are written in
scientific notation, so a Planck-scale quantity is not a row of zeros.
-}
renderRational :: Int -> Rational -> Text
renderRational scale = renderDecimal scale False

{- | As 'renderRational', optionally marking the value approximate even when
its digits end: the selected display precision.
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
  , samples :: Int
  -- ^ the double backend's copies, of which a mixture's outcomes are groups (design §8.2)
  , roundingRuns :: Int
  , samplingInputs :: Bool
  , outcomes :: Int
  -- ^ the most outcomes a mixture may print with (@:set outcomes@)
  , typeNames :: Text -> Text
  -- ^ declared types and constructors written by hash, named (design §7.2)
  }

{- | How a backend's numbers print (design §8.2): the rest of a value, its
shape, units, charts and data, prints the same under every backend.
-}
class (Scalar s) => Display s where
  {- | The numbers of one value, a tensor's components in order, at a
  scale, in significant digits: together, since a backend may print all
  of a value's numbers alike when one of them asks it to.
  -}
  renderNumbers :: Int -> [s] -> [Text]

  -- | A number in a display unit: divided by the unit's factor, at a working precision.
  inUnit :: Precision -> Rational -> s -> Maybe s

  {- | What a value adds after its numbers and its unit: a mark of
  non-linearity over the threshold, the kind of an error estimate, a
  sample. The function lays out one text per number as the value's
  numbers are laid out, in its shape and with its unit.
  -}
  numbersNote :: Rational -> ([Text] -> Text) -> [s] -> Text

  {- | A number as its nominal value alone, without what it carries: how a
  mixture's nominal value prints (design §8.2).
  -}
  nominalOnly :: s -> s
  nominalOnly = id

  inputRunsOnly :: s -> s
  inputRunsOnly = id

  {- | What an outcome of a mixture shows of its numbers (design §8.2): the
  copies' mean and deviation, laid out as the numbers are.
  -}
  clusterText :: ([Text] -> Text) -> [s] -> Text
  clusterText _ _ = ""

instance Display Rat where
  renderNumbers scale = map (renderRational scale . (.value))
  inUnit _ f x
    | f == 0 = Nothing
    | otherwise =
        Just
          x{value = x.value / f, samples = fmap (fmap (/ f)) x.samples}
  numbersNote _ layout xs = case [V.length values | x <- xs, Just values <- [x.samples]] of
    [] -> ""
    n : _ ->
      " (Monte Carlo: "
        <> rationalCluster layout xs
        <> ", "
        <> tshow n
        <> " input samples)"
  nominalOnly x = Rat x.value Nothing
  clusterText = rationalCluster

rationalCluster :: ([Text] -> Text) -> [Rat] -> Text
rationalCluster layout xs =
  "mean "
    <> layout means
    <> ", sd "
    <> layout deviations
    <> ", outcome 95% ["
    <> layout (map (shown . fmap (.lower95)) summaries)
    <> ", "
    <> layout (map (shown . fmap (.upper95)) summaries)
    <> "]"
 where
  shown = either (const "unavailable") (renderRational 12)
  n = maximum (1 : [V.length values | x <- xs, Just values <- [x.samples]])
  summary x =
    Statistics.summariseInputs 24 (maybe (replicate n x.value) V.toList x.samples)
  summaries = map summary xs
  means =
    map
      (either (const "unavailable") (renderRational 12 . (.mean)))
      summaries
  deviations =
    map
      ( either
          (const "unavailable")
          (maybe "unavailable" (renderRational 12) . (.deviation))
      )
      summaries

instance Display Dbl where
  renderNumbers _ = map (showDouble . (.value))
  inUnit _ f x
    | fd == 0 || isNaN fd || isInfinite fd = Nothing
    | otherwise =
        Just
          x
            { value = x.value / fd
            , estimate = case x.estimate of
                NoSamples -> NoSamples
                Copies sp cs -> Copies sp (VU.map (/ fd) cs)
            }
   where
    fd = fromRational f
  numbersNote _ layout xs =
    T.concat
      [ " (" <> t <> ")"
      | t <- maybe [] pure (sampleNote layout xs) ++ maybe [] pure (originNote xs)
      ]
  nominalOnly x = x{estimate = NoSamples}
  inputRunsOnly x =
    x
      { estimate = case x.estimate of
          NoSamples -> NoSamples
          Copies l cs -> Copies l{rounds = 0} cs
      }
  clusterText = clusterNote

{- | Print a value. A tensor with a display unit whose dimension matches
prints its magnitudes in that unit (design §3.2.12); otherwise in SI base
units. Unit names go through the namer so that a renamed unit prints under
its current name.
-}
renderValue ::
  (Display s) =>
  Printer -> Int -> Preferences -> ValueOf s -> Either EvalError Text
renderValue printer scale prefs v = do
  mixed <- hasMixture v
  if mixed
    then renderMixture printer scale prefs v
    else renderValueWith printer scale prefs (renderNumbers scale) v

-- Mixtures ----------------------------------------------------------------------------

-- | Whether a value holds a mixture anywhere (design §8.2): forces its data.
hasMixture :: ValueOf s -> Either EvalError Bool
hasMixture = \case
  VMixture _ -> Right True
  VData _ fields -> anyM fields
  VUnit v -> hasMixture v
  _ -> Right False
 where
  anyM = \case
    [] -> Right False
    f : rest -> f >>= hasMixture >>= \found -> if found then Right True else anyM rest

{- | One outcome of a value whose samples differ in what it is: the copies
that have it, by global number, whether it is the nominal value's, and
the value for those copies, with no mixture in it.
-}
data Outcome s = Outcome {members :: VU.Vector Int, nominal :: Bool, value :: ValueOf s}

{- | A value's outcomes (design §8.2): a mixture's options, and the data
around and inside them taken apart, the copies of each the ones its
parts share.
-}
outcomesOf ::
  (Scalar s) => VU.Vector Int -> Bool -> ValueOf s -> Either EvalError [Outcome s]
outcomesOf ms nominal = \case
  VMixture m ->
    concat
      <$> sequence
        [ outcomesOf o.members (nominal && m.nominal == Just i) o.value
        | (i, o) <- zip [0 :: Int ..] m.options
        ]
  VData c fields -> do
    perField <- mapM (>>= outcomesOf ms nominal) fields
    pure
      [ Outcome both n (VData c [Right (narrowed both n o) | o <- parts])
      | (both, n, parts) <- foldl' combine [(ms, nominal, [])] perField
      ]
  v -> Right [Outcome ms nominal v]
 where
  combine acc outs =
    [ (both, n && o.nominal, parts ++ [o])
    | (shared, n, parts) <- acc
    , o <- outs
    , let both = VU.filter (inSorted o.members) shared
    , not (VU.null both) || (n && o.nominal)
    ]
  narrowed both n o = narrow (Narrowing (placesWithin o.members both) both n) o.value

{- | A mixture printed (design §8.2): its nominal value, then a table of
its outcomes, the ten commonest, each with its samples, its share and
the mean and deviation of each number it holds, the nominal one marked.
-}
renderMixture ::
  (Display s) =>
  Printer -> Int -> Preferences -> ValueOf s -> Either EvalError Text
renderMixture printer scale prefs v = do
  allOuts <- outcomesOf (VU.enumFromN 0 printer.samples) True v
  let stride = printer.roundingRuns + 1
      select o =
        let members = VU.filter (\i -> i `mod` stride == 0) o.members
            value =
              mapNumbers
                inputRunsOnly
                (narrow (Narrowing (placesWithin o.members members) members o.nominal) o.value)
         in Outcome members o.nominal value
      outs = filter (\o -> o.nominal || not (VU.null o.members)) (map select allOuts)
      diagnosticRows =
        [ "  " <> printer.typeNames (outcomeLabel printer o.value) <> ": " <> tshow count
        | o <- allOuts
        , let count = VU.length (VU.filter (\i -> i `mod` stride /= 0) o.members)
        , count > 0
        ]
      diagnostics =
        if printer.roundingRuns == 0
          then ""
          else
            "\nstochastic rounding outcomes (diagnostic runs only; numeric summaries unavailable for mixed constructors):\n"
              <> T.intercalate "\n" diagnosticRows
  let byLabel =
        foldl'
          ( \acc o ->
              let label = printer.typeNames (outcomeLabel printer o.value)
               in case break ((== label) . fst) acc of
                    (before, (l, os) : after) -> before ++ (l, os ++ [o]) : after
                    _ -> acc ++ [(label, [o])]
          )
          []
          outs
      total = sum [VU.length o.members | o <- outs]
  when (length byLabel > printer.outcomes)
    $ Left
      ( Exceeded
          OutcomeCount
          ("the value has more than " <> tshow printer.outcomes <> " outcomes")
      )
  rows <- traverse summary byLabel
  shownNominal <- case [o | o <- outs, o.nominal] ++ outs of
    o : _ -> renderValueWith printer scale prefs (renderNumbers scale) (stripped o.value)
    [] -> Left (Internal "a mixture with no outcome")
  let ordered = sortOn (\(label, count, _, _) -> (negate count, label)) rows
      shown = take 10 ordered
      others = length ordered - length shown
      anyFields = any (\(_, _, _, fs) -> not (T.null fs)) shown
      wLabel = maximum (T.length "outcome" : [T.length l | (l, _, _, _) <- shown])
      wCount = maximum (T.length "samples" : [T.length (tshow c) | (_, c, _, _) <- shown])
      share c =
        T.pack
          ( showFFloat
              (Just 1)
              (100 * fromIntegral c / fromIntegral (max 1 total) :: Double)
              ""
          )
          <> "%"
      wShare = maximum (T.length "share" : [T.length (share c) | (_, c, _, _) <- shown])
      line label count sh fields mark =
        T.dropWhileEnd
          (== ' ')
          ( "  "
              <> T.justifyLeft wLabel ' ' label
              <> "   "
              <> T.justifyRight wCount ' ' count
              <> "   "
              <> T.justifyRight wShare ' ' sh
              <> (if anyFields then "   " <> fields else "")
          )
          <> mark
  pure
    ( T.intercalate
        "\n"
        ( ( shownNominal
              <> ( if printer.samplingInputs
                     then " (Monte Carlo over "
                     else " (ordinary baseline over "
                 )
              <> tshow total
              <> (if printer.samplingInputs then " input samples, " else " run, ")
              <> tshow (length byLabel)
              <> " outcomes):"
          )
            : line "outcome" "samples" "share" "fields" ""
            : [ line
                  label
                  (tshow count)
                  (share count)
                  fields
                  (if isNominal then "   ← nominal" else "")
              | (label, count, isNominal, fields) <- shown
              ]
            ++ ["  and " <> tshow others <> " others" | others > 0]
        )
        <> diagnostics
    )
 where
  -- An outcome's copies and the summary of each number it holds, over
  -- every path that gives it.
  summary (label, os) = do
    let union' = VU.fromList (sortOn id (concat [VU.toList o.members | o <- os]))
        leafLists = map (leavesOf printer . (.value)) os
    fields <- case leafLists of
      first' : _ ->
        sequence
          [ (path,)
              <$> clusterOf
                union'
                [ (o.members, leaf)
                | (o, leaves) <- zip os leafLists
                , (p, leaf) <- leaves
                , p == path
                ]
          | (path, _) <- first'
          ]
      [] -> pure []
    pure
      ( label
      , VU.length union'
      , any (.nominal) os
      , T.intercalate
          "; "
          [if T.null path then t else path <> ": " <> t | (path, t) <- fields]
      )
  -- A number's samples across the outcomes that hold it, as its mean and
  -- deviation in its unit.
  clusterOf union' parts = case parts of
    (_, VUnit _) : _ -> clusterOf union' [(ms, unwrapped leaf) | (ms, leaf) <- parts]
    (_, VTensor dims d hint buf) : _ -> do
      elements <-
        traverse
          ( \k ->
              scatterM
                (settingsAt (scale + 4)){inputSampling = True}
                (VU.length union')
                Nothing
                <$> traverse
                  (\(ms, leaf) -> (placesWithin union' ms,) <$> (bufferOf leaf V.! k))
                  parts
          )
          [0 .. V.length buf - 1]
      (shape, scaled, units) <-
        displayParts
          printer
          scale
          prefs
          (VTensor dims d hint (V.fromList (map Right elements)))
      let laid ts = renderNested id shape ts <> (if T.null units then "" else " " <> units)
      pure (clusterText laid scaled)
    _ -> pure ""
  unwrapped = \case
    VUnit w -> w
    w -> w
  bufferOf = \case
    VTensor _ _ _ buf -> buf
    VPoint _ _ _ buf -> buf
    VUnit u -> bufferOf u
    _ -> V.empty

{- | What an outcome is, as a label: its data as written, with @_@ for each
number, and a record by its constructor alone, its fields' numbers shown
beside it.
-}
outcomeLabel :: Printer -> ValueOf s -> Text
outcomeLabel printer = \case
  VBool True -> "true"
  VBool False -> "false"
  VData (TupleC _) fields -> "(" <> T.intercalate ", " (map field fields) <> ")"
  v@(VData c _)
    | c == ConsC || c == NilC ->
        "{"
          <> T.intercalate ", " (map (outcomeLabel printer) (fromRight [] (listItems v)))
          <> "}"
  VData c@(UserCon h i) fields
    | not (null fields)
    , Just _ <- sequence (printer.fieldNames h i (length fields)) ->
        conText c
  VData c fields -> T.unwords (conText c : map (paren . field) fields)
  VClosure _ -> "<function>"
  VChart _ -> "chart"
  VTyAbs{} -> "<polymorphic value>"
  VMixture _ -> "<mixture>"
  _ -> "_"
 where
  field = either (const "_") (outcomeLabel printer)
  paren t = if T.any (== ' ') t then "(" <> t <> ")" else t

{- | The numbers an outcome holds, each by its path: a record's field by
its name, any other field or item by its place.
-}
leavesOf :: Printer -> ValueOf s -> [(Text, ValueOf s)]
leavesOf printer = go ""
 where
  go path = \case
    v@VTensor{} -> [(path, v)]
    v@VUnit{} -> [(path, v)]
    v@VPoint{} -> [(path, v)]
    v@(VData c _)
      | c == ConsC || c == NilC ->
          concat
            ( zipWith
                (go . at path . tshow)
                [0 :: Int ..]
                (fromRight [] (listItems v))
            )
    VData (UserCon h i) fields
      | not (null fields)
      , Just names <- sequence (printer.fieldNames h i (length fields)) ->
          concat (zipWith (either (const []) . go . at path) names fields)
    VData _ fields ->
      concat
        ( zipWith
            (either (const []) . go . at path . tshow)
            [0 :: Int ..]
            fields
        )
    _ -> []
  at path n = if T.null path then n else path <> "." <> n

-- | A value's numbers as their nominal values alone.
stripped :: (Display s) => ValueOf s -> ValueOf s
stripped = mapNumbers nominalOnly

mapNumbers :: (s -> s) -> ValueOf s -> ValueOf s
mapNumbers f = \case
  VTensor dims d hint buf -> VTensor dims d hint (fmap (fmap f) buf)
  VPoint dims d c buf -> VPoint dims d c (fmap (fmap f) buf)
  VUnit v -> VUnit (mapNumbers f v)
  VData c fields -> VData c (map (fmap (mapNumbers f)) fields)
  v -> v

{- | 'renderValue' with a chosen rendering for the magnitudes of one value,
a tensor's components in order.
-}
renderValueWith ::
  (Display s) =>
  Printer ->
  Int ->
  Preferences ->
  ([s] -> [Text]) ->
  ValueOf s ->
  Either EvalError Text
renderValueWith printer scale prefs showMagnitudes = \case
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
    pure $ case (chartName s, coordinatesOn (settingsAt (scale + 4)) s xs) of
      (Just named, Right steps) ->
        let laid ts = renderNested id dims ts <> " " <> named
         in laid (showMagnitudes steps) <> numbersNote 0 laid steps
      _ ->
        let laid ts = renderNested id dims ts <> unitSuffix d
         in laid (showMagnitudes xs) <> " (point)" <> numbersNote 0 laid xs
  VChart s ->
    Right $ case chartName s of
      Just named -> "chart " <> named
      Nothing ->
        "chart: step "
          <> T.concat (showMagnitudes [s.step])
          <> " at "
          <> renderNested id s.dims (showMagnitudes (V.toList s.origin))
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
      , hintFactor m == h.factor ->
          Right (unitExpressionText printer h)
    _ -> (<> " (a unit)") <$> recur v
  v -> do
    (dims, scaled, units) <- displayParts printer scale prefs v
    let laid ts = renderNested id dims ts <> (if T.null units then "" else " " <> units)
    pure (laid (showMagnitudes scaled) <> numbersNote 0 laid scaled)
 where
  recur = renderValueWith printer scale prefs showMagnitudes
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
  (Display s) =>
  Printer ->
  Int ->
  Preferences ->
  ValueOf s ->
  Either EvalError ([Int], [s], Text)
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
        , h.factor /= 0
        , Just converted <- mapM (inUnit (scale + 4) h.factor) rs ->
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
    -- A primitive used as a value was eta-expanded to its arity (design
    -- §2.9). It prints as written, `vmap sqrt`, `foldr add 0`, which reads
    -- back as the same term.
    Lam{}
      | Just (p, leading) <- etaPrimitive t
      , byName ctx p ->
          if null leading
            then p
            else paren (prec > 10) (T.unwords (p : map (go 11 ctx) leading))
    Lam h b -> lambda prec ctx h b
    -- A lambda applied keeps its binder: `round e` would read back as the
    -- primitive applied to `e`, not the lambda that applies it.
    App (Lam h b) a ->
      paren (prec > 10) (lambda 10 ctx h b <> " " <> go 11 ctx a)
    App f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
    Let (Hint h) e b ->
      let h' = freshen h ctx
       in paren
            (prec > 0)
            ("let " <> h' <> " = " <> unclosed ctx e <> " in " <> go 0 (VCons h' ctx) b)
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
        ( "if "
            <> unclosed ctx sc
            <> " then "
            <> unclosed ctx th
            <> " else "
            <> go 0 ctx el
        )
    Case sc alts ->
      paren
        (prec > 0)
        ( "case "
            <> unclosed ctx sc
            <> " of "
            <> T.intercalate "; " (zipWith alt [1 ..] alts)
        )
     where
      alt k (Alt c hs b) =
        let names = freshenAll (vecMap (\(Hint h) -> h) hs) ctx
            ctx' = vecAppend names ctx
            body = if k == length alts then go 0 ctx' b else unclosed ctx' b
         in patternText c (vecToList names) <> arrow <> body
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
    Sample l x -> paren (prec > 10) ("sample " <> go 11 ctx x <> renderLabel l)
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
  prim prec ctx p args = case (fixityOfPrim p, args) of
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
    -- A binary operator as the parser reads it ("Metron.Fixity"). `*`
    -- keeps its spelling in unicode, since `×` is the cross product.
    (Just f, [a, b]) ->
      let lvl = f.level
          (lp, rp) = case f.assoc of
            L -> (lvl, lvl + 1)
            R -> (lvl + 1, lvl)
            N -> (lvl + 1, lvl + 1)
          sym = if spelling == Unicode then f.unicode else f.ascii
       in paren (prec > lvl) (go lp ctx a <> " " <> sym <> " " <> go rp ctx b)
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

  lambda :: Int -> Vec m Text -> Hint -> Term (S m) -> Text
  lambda prec ctx (Hint h) b =
    let h' = freshen h ctx
        backslash = if spelling == Unicode then "λ" else "\\"
     in paren (prec > 0) (backslash <> h' <> arrow <> go 0 (VCons h' ctx) b)

  -- Lambdas the desugarer made for a primitive used with fewer arguments
  -- than its arity (design §2.9), with 'etaHint' on their binders: the
  -- primitive and the arguments it was written with, outside the
  -- lambdas. The body applies it to those arguments, then to the binders
  -- in order, which nothing else mentions.
  etaPrimitive :: Term m -> Maybe (Text, [Term m])
  etaPrimitive = \case
    Lam h b | h == etaHint -> do
      (p, args) <- case b of
        PrimApp p args -> Just (p, args)
        _ -> etaPrimitive b
      (leading, final) <- unsnoc args
      case final of
        Var FZ -> (p,) <$> traverse strengthen leading
        _ -> Nothing
    _ -> Nothing
  -- Whether a primitive reads back by its name: an identifier that no
  -- local shadows.
  byName :: Vec m Text -> Text -> Bool
  byName ctx p =
    fmap (map (.value)) (L.tokenize p) == Right [L.TIdent p]
      && p `notElem` vecToList ctx

  -- A case's alternatives run to the end of the expression, so a term that
  -- ends in one is parenthesised where more text follows it: a let's
  -- bound value, an if's condition and then-branch, a scrutinee, an
  -- alternative before another. `let x = r.f in …` is such a term, since
  -- a field access is a case.
  unclosed :: Vec m Text -> Term m -> Text
  unclosed ctx e = paren (endsInCase e) (go 0 ctx e)
  endsInCase :: Term m -> Bool
  endsInCase = \case
    Case _ [Alt FalseC VNil el, Alt TrueC VNil _] -> endsInCase el
    Case _ _ -> True
    Let _ _ b -> endsInCase b
    Lam _ b -> endsInCase b
    _ -> False

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

-- | A magnitude to two significant digits, for radii and bias boxes.

-- | The elements of a list value, forcing its spine.
listItems :: ValueOf s -> Either EvalError [ValueOf s]
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
fieldText :: ValueOf s -> Text -> Text
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
