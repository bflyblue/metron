{- | The REPL's pure parts (design §7.3): tab completion and output colour,
a syntax-highlighting theme that follows the lexer. The executable wires
them into haskeline; they live here so the test suite can reach them.
Nothing here changes what 'Eval.Driver.feed' prints.
-}
module Eval.Repl (
  -- * Completion
  Completion (..),
  complete,
  completions,
  loadsFile,
  commands,
  keywords,

  -- * Colour
  Names (..),
  namesOf,
  Kind (..),
  classify,
  paint,
  render,
  echoInput,
  highlight,
  highlightType,
  splitUnits,
) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Char (isAlphaNum, isDigit, isLetter, isSpace)
import Data.List (isPrefixOf, nub, sort, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase (Codebase (..))
import Eval.Dimension (baseSymbol)
import Eval.Driver (Session (..))
import Eval.Lexer (Keyword (..), Located (..), Token (..), prepare, tokenize)
import Eval.Syntax (Pos (..), Span (..))
import Eval.Unicode qualified as U

-- Completion ------------------------------------------------------------------

{- | A candidate, as haskeline's @Completion@: the text that replaces the
word, what the candidate list shows, and whether a space follows a unique
match.
-}
data Completion = Completion
  { replacement :: String
  , display :: String
  , isFinished :: Bool
  }
  deriving stock (Eq, Show)

-- | The commands completed after a @:@ at the start of a line.
commands :: [String]
commands =
  [ ":add"
  , ":update"
  , ":upgrade"
  , ":todo"
  , ":scratch"
  , ":forget"
  , ":edit"
  , ":type"
  , ":ls"
  , ":view"
  , ":core"
  , ":lint"
  , ":hash"
  , ":names"
  , ":history"
  , ":dependents"
  , ":alias"
  , ":unname"
  , ":exact"
  , ":budget"
  , ":covariance"
  , ":set"
  , ":prefer"
  , ":unprefer"
  , ":load"
  , ":quit"
  , ":store"
  , ":colour"
  ]

-- | The lexer's keywords ("Eval.Lexer").
keywords :: [String]
keywords =
  [ "let"
  , "unit"
  , "scale"
  , "at"
  , "data"
  , "case"
  , "of"
  , "in"
  , "where"
  , "if"
  , "then"
  , "else"
  , "to"
  , "true"
  , "false"
  ]

{- | Whether the cursor is at a file name: the argument of @:load@. The
REPL completes it with haskeline's file name completion.
-}
loadsFile :: String -> Bool
loadsFile line = ":load " `isPrefixOf` dropWhile isSpace line

{- | A completion function in haskeline's shape: the text left of the
cursor, reversed, and the text right of it. The result is the reversed
text that stays and the candidates for the word that is replaced;
'Nothing' asks for file name completion instead.

The word is a backslash name (@\\mu@, @\\^2@) when one ends at the cursor,
otherwise the identifier ending at the cursor, with a @.@ before it for a
field and a @:@ before it at the start of a line for a command.
-}
complete :: Session -> (String, String) -> Maybe (String, [Completion])
complete session (leftRev, _)
  | loadsFile (reverse leftRev) = Nothing
  | (nameRev, '\\' : prev) <- span isNameChar leftRev =
      Just (prev, completions session prev ('\\' : reverse nameRev))
  | otherwise =
      let (fragRev, before) = span identChar leftRev
          -- A number glued to a name is not part of it: @3kilo@.
          (digits, frag) = span isDigit (reverse fragRev)
          prev0 = reverse digits ++ before
          (word, prev) = case prev0 of
            '.' : p | null digits -> ('.' : frag, p)
            ':' : p | null digits, all isSpace p -> (':' : frag, p)
            _ -> (frag, prev0)
       in Just (prev, completions session prev word)
 where
  isNameChar c = isLetter c || isDigit c || c `elem` ("^-_" :: String)

{- | The candidates for one word, given the reversed text before it, as
haskeline's @completeWordWithPrev@ passes them.

* @\\name@: entries of "Eval.Unicode" and nothing else; an exact name
  becomes its text, a partial one lists the names it starts.
* @:cmd@ at the start of a line: commands.
* After @:set@ or @:colour@: their arguments.
* @.f@: record fields.
* Otherwise: names, type names, constructor names and keywords.
-}
completions :: Session -> String -> String -> [Completion]
completions session prev word = case word of
  '\\' : name -> case U.matching (T.pack name) of
    [(_, t)] -> [Completion (T.unpack t) (T.unpack t) False]
    many ->
      [ Completion ('\\' : T.unpack k) ('\\' : T.unpack k <> " " <> T.unpack t) False
      | (k, t) <- many
      ]
  ':' : _ | all isSpace prev -> plain commands
  '.' : f ->
    [ Completion ('.' : n) n True
    | n <- sorted (map T.unpack (Map.keys cb.fieldNames))
    , f `isPrefixOf` n
    ]
  _ -> case words (reverse prev) of
    [":set"] -> plain ["precision", "sigma", "unicode"]
    [":set", "unicode"] -> plain ["on", "off"]
    [c] | c `elem` [":colour", ":color"] -> plain ["on", "off"]
    _
      | null word -> []
      | otherwise ->
          plain
            ( sorted
                ( map
                    T.unpack
                    (Map.keys cb.names ++ Map.keys cb.typeNames ++ Map.keys cb.conNames)
                    ++ keywords
                )
            )
 where
  cb = session.staging
  sorted = nub . sort
  plain xs = [Completion x x True | x <- xs, word `isPrefixOf` x]

identChar :: Char -> Bool
identChar x =
  (isAlphaNum x && not (isSuperscript x))
    || x == '_'
    || x == '\''
    || (x >= '₀' && x <= '₉')

isSuperscript :: Char -> Bool
isSuperscript = (`elem` ("⁰¹²³⁴⁵⁶⁷⁸⁹" :: String))

-- Colour -----------------------------------------------------------------------

{- | The theme (design §7.3): the 16 ANSI colours only, so it survives any
terminal. Plain text (numbers, operators, brackets, variables) gets no code.
-}
data Colour
  = -- | errors: SGR 31
    Red
  | -- | carets: SGR 1;31
    BoldRed
  | -- | notes, comments, hashes: bright black, SGR 90
    Grey
  | -- | keywords: SGR 35
    Magenta
  | -- | units and scales: SGR 36
    Cyan
  | -- | types and constructors: SGR 33
    Yellow
  | -- | the prompt: SGR 1
    Bold
  deriving stock (Eq, Show)

-- | Text in a colour, reset after it. Empty text gets no codes.
sgr :: Colour -> Text -> Text
sgr c s
  | T.null s = s
  | otherwise = "\ESC[" <> code <> "m" <> s <> "\ESC[0m"
 where
  code = case c of
    Red -> "31"
    BoldRed -> "1;31"
    Grey -> "90"
    Magenta -> "35"
    Cyan -> "36"
    Yellow -> "33"
    Bold -> "1"

{- | The names the painter colours by, taken from a session: units, the
SI base units and scales (cyan), type names and the built-in heads
(yellow), constructors (yellow).
-}
data Names = Names
  { unitWords :: Set Text
  , typeWords :: Set Text
  , conWords :: Set Text
  }
  deriving stock (Eq, Show)

-- | The names of the session's staging codebase, pending declarations included.
namesOf :: Session -> Names
namesOf session =
  Names
    { unitWords =
        cb.units <> cb.scales <> Set.fromList (map baseSymbol [minBound .. maxBound])
    , typeWords = Map.keysSet cb.typeNames <> Set.fromList builtinTypes
    , conWords = Map.keysSet cb.conNames
    }
 where
  cb = session.staging
  builtinTypes = ["Num", "Vec", "Mat", "Tensor", "Point", "Scale", "Bool"]

-- | What a printed line is, for colour.
data Kind
  = -- | printed as is
    Plain
  | -- | a note about what a command did: grey
    Note
  | -- | the @≡@ echo of an input in its unicode spelling: grey mark, highlighted
    Echo
  | -- | @name : type@: the type highlighted as a type
    Signature
  | -- | a type on its own (@:type@ of a function): highlighted as a type
    Type
  | -- | a value or a definition: highlighted, else its trailing unit cyan
    Value
  | -- | the source excerpt of an error: highlighted, else as is
    Source
  | -- | an error's position line and message: red
    Problem
  | -- | an error's carets: bold red
    Caret
  deriving stock (Eq, Show)

{- | Split what 'Eval.Driver.feed' returned into physical lines, each with
its kind. Joining the texts with newlines gives back what was printed.
-}
classify :: Either Text [Text] -> [(Kind, Text)]
classify = \case
  Right outs -> [(kindOf l, l) | out <- outs, l <- T.splitOn "\n" out]
  Left err -> errorLines (T.splitOn "\n" err)
 where
  errorLines = \case
    h : src : rest
      | "error at " `T.isPrefixOf` h -> (Problem, h) : (Source, src) : errorLines rest
    l : rest
      | T.any (== '^') l && T.all (\c -> c == ' ' || c == '^') l ->
          (Caret, l) : errorLines rest
      | otherwise -> (Problem, l) : errorLines rest
    [] -> []
  kindOf l
    | isNote l = Note
    | "  ≡ " `T.isPrefixOf` l = Echo
    | isSignature l = Signature
    | isType l = Type
    | otherwise = Value
  isNote l =
    any
      (`T.isPrefixOf` l)
      [ "pending: "
      , "added "
      , "updated "
      , "upgraded "
      , "left "
      , "removed "
      , "replaced "
      , "forgot "
      , "stale:"
      , "nothing "
      , "note:"
      , "no preferences"
      , "values of dimension "
      , "dependents left "
      , "(input abandoned)"
      ]
      || ("(" `T.isPrefixOf` l && "prelude names hidden" `T.isInfixOf` l)
      || ("`" `T.isPrefixOf` l && "` now also names " `T.isInfixOf` l)
  -- @area : …@, @unit km : …@; not a cons pattern inside a :view.
  isSignature l = case T.breakOn " : " l of
    (lhs, rhs) | not (T.null rhs) -> isName (dropFlag lhs)
    _ -> False
  -- What @:type@ prints for a function: a value never shows an arrow, a
  -- definition (@:view@, @:core@) has an @=@, and its later lines are
  -- indented.
  isType l =
    (T.isInfixOf "->" l || T.isInfixOf "→" l)
      && not (T.isInfixOf " = " l)
      && not (" " `T.isPrefixOf` l)
  dropFlag lhs = fromMaybe lhs (T.stripPrefix "unit " lhs <|> T.stripPrefix "scale " lhs)
  isName n = case T.uncons n of
    Just (c, rest) -> (isLetter c || c == '_') && T.all identChar rest
    Nothing -> False

{- | A line with ANSI SGR codes for its kind (design §7.3). Source text is
highlighted token by token ('highlight'); where it does not lex, the
line is painted by its kind alone. Only escape codes are added: removing
them gives back the line.
-}
paint :: Names -> Kind -> Text -> Text
paint names kind t = case kind of
  Plain -> t
  Note -> sgr Grey t
  Problem -> sgr Red t
  Caret -> sgr BoldRed t
  Echo -> case T.stripPrefix "  ≡ " t of
    Just rest -> "  " <> sgr Grey "≡" <> " " <> paint names Value rest
    Nothing -> paint names Value t
  Signature -> case T.breakOn " : " t of
    (lhs, rhs)
      | Just ty <- T.stripPrefix " : " rhs ->
          flagged lhs <> " : " <> asType ty
    _ -> t
  Type -> asType t
  Value ->
    fromMaybe
      (let (body, units) = splitUnits t in body <> sgr Cyan units)
      (tryHighlight Expression names t)
  Source -> fromMaybe t (tryHighlight Expression names t)
 where
  asType ty = fromMaybe (sgr Yellow ty) (tryHighlight TypeLevel names ty)
  -- The name of a signature stays plain; its @unit@ or @scale@ is a keyword.
  flagged lhs = case T.breakOn " " lhs of
    (flag, name)
      | flag `elem` ["unit", "scale"], not (T.null name) -> sgr Magenta flag <> name
    _ -> lhs

{- | What the REPL prints for one result: as 'Eval.Driver.feed' returned it
without colour, painted line by line with it.
-}
render :: Bool -> Names -> Either Text [Text] -> [Text]
render colour names result
  | colour = map (uncurry (paint names)) (classify result)
  | otherwise = either pure id result

{- | The echo of an input line in scripted mode (@eval -i@): @> @ and the
line. With colour the @> @ is bold, like the prompt, and the line is
highlighted; a command only past its name, and only when it takes an
expression (@:type@, @:exact@, @:budget@, @:covariance@).
-}
echoInput :: Bool -> Names -> Text -> Text
echoInput colour names input
  | not colour = "> " <> input
  | otherwise = sgr Bold "> " <> body
 where
  body = case T.breakOn " " input of
    (cmd, rest)
      | cmd `elem` [":type", ":exact", ":budget", ":covariance"] ->
          cmd <> highlight names rest
      | ":" `T.isPrefixOf` cmd -> input
    _ -> highlight names input

{- | Source text coloured token by token: keywords magenta, units and
scales cyan, types and constructors yellow, @#hash@ and @#label@ grey,
comments grey, everything else (numbers, powers, operators, variables)
plain. A @data@ declaration is coloured as a type ('highlightType'). Text
that does not lex comes back unchanged.
-}
highlight :: Names -> Text -> Text
highlight names t = fromMaybe t (tryHighlight Expression names t)

{- | A type coloured token by token: type names, constructors and the
built-in heads yellow, units cyan inside @[…]@, everything else plain, so
a type variable named like a unit (@m@, @g@) stays plain.
-}
highlightType :: Names -> Text -> Text
highlightType names t = fromMaybe t (tryHighlight TypeLevel names t)

-- | Whether text is an expression or a type, for colour.
data Level = Expression | TypeLevel

{- | Lex the text and colour each token by its span; 'Nothing' when it does
not lex.

Spans index the original text directly: 'prepare' (which the lexer
applies) must keep the length, which it does unless NFC composes
characters, and there must be no tab, which Megaparsec counts as up to
eight columns. Otherwise the text counts as not lexing. Two things that
print but do not lex are made lexable first, keeping every offset: a
value's @…@ becomes a space, and the @.@ of a cycle member's @#hash.1@ an
@_@, so the reference is one token. What lies between tokens is
whitespace or a comment, so its non-blank part is painted as a comment.
-}
tryHighlight :: Level -> Names -> Text -> Maybe Text
tryHighlight level names t = do
  let p = prepare t
      src = lexable p
  guard (T.length p == T.length t && not (T.any (== '\t') t))
  toks <- either (const Nothing) Just (tokenize src)
  let starts = scanl (\n l -> n + T.length l + 1) 0 (T.splitOn "\n" p)
      offset pos = (starts !! (pos.line - 1)) + pos.col - 1
      located =
        [ (offset tok.span.from, offset tok.span.to, tok.value)
        | tok <- toks
        , tok.span.from /= tok.span.to
        ]
      level' = if declaresData [tok | (_, _, tok) <- located] then TypeLevel else level
      runs = colourTokens level' names located ++ comments src located
  pure (applyRuns t (sortOn (\(s, _, _) -> s) runs))
 where
  declaresData = \case
    TKw KData : _ -> True
    TIdent "structural" : TKw KData : _ -> True
    _ -> False

-- | A copy that lexes where the printed text does not; offsets are kept.
lexable :: Text -> Text
lexable = T.pack . go False . T.unpack
 where
  go _ [] = []
  go inHash (c : cs)
    | c == '…' = ' ' : go False cs
    | c == '#' = c : go True cs
    | inHash, c == '.', d : _ <- cs, isDigit d = '_' : go True cs
    | inHash, isAlphaNum c || c == '_' = c : go True cs
    | otherwise = c : go False cs

{- | The coloured tokens, as (start, end, colour). In a type, the name after
@data@ and after @=@ or @|@ is the type or a constructor being declared:
yellow even before the session knows it.
-}
colourTokens :: Level -> Names -> [(Int, Int, Token)] -> [(Int, Int, Colour)]
colourTokens level names located = go (0 :: Int) Nothing located
 where
  shadowed = case level of
    Expression -> binders [tok | (_, _, tok) <- located]
    TypeLevel -> Set.empty
  go _ _ [] = []
  go depth prev ((s, e, tok) : rest) =
    let depth' = case tok of
          TLBracket -> depth + 1
          TRBracket -> max 0 (depth - 1)
          _ -> depth
        next = case rest of
          (_, _, n) : _ -> Just n
          [] -> Nothing
     in [(s, e, c) | Just c <- [colourOf depth prev next tok]]
          ++ go depth' (Just tok) rest
  colourOf depth prev next = \case
    TKw _ -> Just Magenta
    TIdent "structural" | next == Just (TKw KData) -> Just Magenta
    THashLabel _ -> Just Grey
    TIdent n -> case level of
      Expression
        | n `Set.member` names.conWords -> Just Yellow
        | n `Set.member` names.unitWords, n `Set.notMember` shadowed -> Just Cyan
        | n `Set.member` names.typeWords -> Just Yellow
      TypeLevel
        | depth > 0 -> if n `Set.member` names.unitWords then Just Cyan else Nothing
        | n `Set.member` names.typeWords || n `Set.member` names.conWords -> Just Yellow
        | prev `elem` map Just [TKw KData, TEquals, TBar] -> Just Yellow
      _ -> Nothing
    _ -> Nothing

{- | Names a line binds, which shadow a unit of the same name on it: those
between @let@, @where@, @\\@, @of@ or @;@ and the next @=@ or @->@, outside
square brackets (@\\s -> …@, @case s of Rect w h -> …@). The highlighter
does not resolve scope: a name bound anywhere on the line is a variable
everywhere on it.
-}
binders :: [Token] -> Set Text
binders = \case
  [] -> Set.empty
  t : ts
    | opens t
    , (region, closer : _) <- break (\x -> opens x || closes x) ts
    , closes closer ->
        Set.fromList (bound (0 :: Int) region) <> binders ts
    | otherwise -> binders ts
 where
  opens = (`elem` [TKw KLet, TKw KWhere, TLambda, TKw KOf, TSep])
  closes = (`elem` [TEquals, TArrow])
  bound depth = \case
    [] -> []
    TLBracket : rest -> bound (depth + 1) rest
    TRBracket : rest -> bound (max 0 (depth - 1)) rest
    TIdent n : rest | depth == 0 -> n : bound depth rest
    _ : rest -> bound depth rest

{- | Comments, as (start, end, 'Grey'): the non-blank part of the text
between two tokens, before the first or after the last. The lexer skips
only whitespace and comments there.
-}
comments :: Text -> [(Int, Int, Token)] -> [(Int, Int, Colour)]
comments src located =
  [ (a + lead, b - trail, Grey)
  | (a, b) <- zip (0 : ends) (starts ++ [T.length src])
  , b > a
  , let gap = T.take (b - a) (T.drop a src)
        lead = T.length (T.takeWhile isSpace gap)
        trail = T.length (T.takeWhileEnd isSpace gap)
  , lead < T.length gap
  ]
 where
  starts = [s | (s, _, _) <- located]
  ends = [e | (_, e, _) <- located]

-- | Wrap the given runs (sorted, disjoint) of the text in their colours.
applyRuns :: Text -> [(Int, Int, Colour)] -> Text
applyRuns t0 = T.concat . go 0 t0
 where
  go _ rest [] = [rest]
  go i rest ((s, e, c) : more) =
    let (before, from) = T.splitAt (s - i) rest
        (tok, after) = T.splitAt (e - s) from
     in before : sgr c tok : go e after more

{- | A value's trailing unit, split off: the longest run of unit words at
the end (identifiers with an optional @^n@ or superscript power, joined by
@/@, and @(point)@), when what precedes it ends a number or a bracket
(a digit, @…@, @]@, @)@ or @}@). The two parts concatenate to the input;
the second is empty when there is no unit. The fallback for a value that
does not lex.
-}
splitUnits :: Text -> (Text, Text)
splitUnits t =
  let ws = reverse (T.splitOn " " t)
      (us, rest) = span isUnitWord ws
      body = T.intercalate " " (reverse rest)
   in case T.unsnoc body of
        Just (_, c)
          | not (null us)
          , c `elem` ("0123456789…])}" :: String) ->
              (body <> " ", T.intercalate " " (reverse us))
        _ -> (t, "")
 where
  isUnitWord w = w == "(point)" || (not (T.null w) && all isUnitAtom (T.splitOn "/" w))
  isUnitAtom a = case T.uncons a of
    Just (c, rest) | isLetter c -> power (T.dropWhile identChar rest)
    _ -> False
  power p
    | T.null p = True
    | Just n <- T.stripPrefix "^" p = integer n
    | otherwise =
        let digits = fromMaybe p (T.stripPrefix "⁻" p)
         in not (T.null digits) && T.all isSuperscript digits
  integer n =
    let ds = fromMaybe n (T.stripPrefix "-" n)
     in not (T.null ds) && T.all isDigit ds
