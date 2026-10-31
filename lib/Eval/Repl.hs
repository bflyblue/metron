{- | The REPL's pure parts (design §7.3): tab completion, output colour as a
syntax-highlighting theme that follows the lexer, and whether an input goes
on at a continuation line. The executable wires them into haskeline; they
live here so the test suite can reach them. Nothing here changes what
'Eval.Driver.feed' prints.
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
  echoInputAt,
  highlight,
  highlightType,
  splitUnits,

  -- * Continuation lines
  Continuation (..),
  continuation,
  needsMore,
) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Char (isAlphaNum, isDigit, isLetter, isSpace)
import Data.List (isPrefixOf, nub, sort, sortOn)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase (Codebase (..))
import Eval.Dimension (baseSymbol)
import Eval.Driver (Session (..))
import Eval.Lexer (
  Keyword (..),
  Located (..),
  Token (..),
  prepare,
  showToken,
  tokenize,
 )
import Eval.Resolve (LabelKind (..), shortestName, shortestNameOf)
import Eval.Syntax (Pos (..), Span (..), lastSegment)
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
  , ":rename"
  , ":move"
  , ":namespace"
  , ":uses"
  , ":use"
  , ":unuse"
  , ":export"
  , ":stdlib"
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
  , "chart"
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
  , "namespace"
  , "use"
  , "forall"
  ]

{- | Whether the cursor is at a file name: the argument of @:load@ or of
@:edit --file@. The REPL completes it with haskeline's file name
completion.
-}
loadsFile :: String -> Bool
loadsFile line = any (`isPrefixOf` dropWhile isSpace line) [":load ", ":edit --file "]

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
            -- A dotted name, @orbital.pe@, when some name starts so (design §7.6).
            '.' : p
              | null digits
              , (chainRev@(c : _), p') <- span (\x -> identChar x || x == '.') p
              , identChar c
              , let qualified = reverse chainRev ++ "." ++ frag
              , any (qualified `isPrefixOf`) (nameCandidates session) ->
                  (qualified, p')
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
  -- A field is written by its last segment (design §7.6).
  '.' : f ->
    [ Completion ('.' : n) n True
    | n <- sorted (map (T.unpack . lastSegment) (Map.keys cb.fieldNames))
    , f `isPrefixOf` n
    ]
  _ -> case words (reverse prev) of
    [":set"] -> plain ["precision", "sigma", "unicode"]
    [":set", "unicode"] -> plain ["on", "off"]
    [c] | c `elem` [":colour", ":color"] -> plain ["on", "off"]
    _
      | null word -> []
      -- After @::@ in the statement, a type (design §4.8).
      | typeOpenAt (reverse (takeWhile (/= ';') prev)) ->
          plain
            ( sorted
                ( ["Bool", "Num", "Vec", "Mat", "Tensor", "Point", "Chart"]
                    ++ map T.unpack (types ++ map (shortestNameOf TypeLabel session.scope cb) types)
                )
            )
      | otherwise -> plain (sorted (nameCandidates session ++ keywords))
 where
  cb = session.staging
  types = Map.keys cb.typeNames
  sorted = nub . sort
  plain xs = [Completion x x True | x <- xs, word `isPrefixOf` x]

{- | Whether the end of a statement's text is inside a type (design §4.8):
after a @::@ that no parenthesis has closed since, as 'tokenLevels' reads
it, so @(3 m :: Num m) + spe@ is an expression again.
-}
typeOpenAt :: String -> Bool
typeOpenAt = go (0 :: Int) Nothing
 where
  go _ open [] = isJust open
  go depth _ (':' : ':' : rest) = go depth (Just depth) rest
  go depth open ('(' : rest) = go (depth + 1) open rest
  go depth open (')' : rest) =
    let depth' = max 0 (depth - 1)
     in go depth' (if maybe False (> depth') open then Nothing else open) rest
  go depth open (_ : rest) = go depth open rest

{- | The names a session sees, for completion: definitions, types and
constructors by their full paths, and also as the scope spells them, so a
name from a @use@d namespace or the current one completes bare (design
§7.6).
-}
nameCandidates :: Session -> [String]
nameCandidates session =
  map
    T.unpack
    ( full
        ++ map (shortestName session.scope cb) terms
        ++ map (shortestNameOf TypeLabel session.scope cb) types
    )
 where
  cb = session.staging
  terms = Map.keys cb.names ++ Map.keys cb.conNames
  types = Map.keys cb.typeNames
  full = terms ++ types

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
  | -- | units and charts: SGR 36
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
SI base units and charts (cyan), type names and the built-in heads
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
        spelled shortestName (Set.toList (cb.units <> cb.scales))
          <> Set.fromList (map baseSymbol [minBound .. maxBound])
    , typeWords =
        spelled (shortestNameOf TypeLabel) (Map.keys cb.typeNames)
          <> Set.fromList builtinTypes
    , conWords = spelled shortestName (Map.keys cb.conNames)
    }
 where
  cb = session.staging
  -- Each label by its full path and as the scope spells it, so that the
  -- library's `si.km` is a unit written `km` (design §7.6, §7.7).
  spelled short ns = Set.fromList ns <> Set.fromList (map (short session.scope cb) ns)
  builtinTypes = ["Num", "Vec", "Mat", "Tensor", "Point", "Chart", "Scale", "Bool"]

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
      , "renamed "
      , "moved "
      , "stale:"
      , "nothing "
      , "note:"
      , "no preferences"
      , "values of dimension "
      , "dependents left "
      , "(input abandoned)"
      , "kept "
      , "re-hashed "
      , "stored use "
      , "the library is up to date"
      ]
      -- The namespaces under the current one, in a bare :ls.
      || ("namespace " `T.isPrefixOf` l && " name" `T.isInfixOf` l && ")" `T.isSuffixOf` l)
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
  dropFlag lhs = fromMaybe lhs (T.stripPrefix "unit " lhs <|> T.stripPrefix "chart " lhs)
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
  -- The name of a signature stays plain; its @unit@ or @chart@ is a keyword.
  flagged lhs = case T.breakOn " " lhs of
    (flag, name)
      | flag `elem` ["unit", "chart"], not (T.null name) -> sgr Magenta flag <> name
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
echoInput = echoInputAt "> "

-- | 'echoInput' after a given prompt: @"… "@ for a continuation line.
echoInputAt :: Text -> Bool -> Names -> Text -> Text
echoInputAt p colour names input
  | not colour = p <> input
  | otherwise = sgr Bold p <> body
 where
  body = case T.breakOn " " input of
    (cmd, rest)
      | cmd `elem` [":type", ":exact", ":budget", ":covariance"] ->
          cmd <> highlight names rest
      | ":" `T.isPrefixOf` cmd -> input
    _ -> highlight names input

{- | Source text coloured token by token: keywords magenta, units and
charts cyan, types and constructors yellow, @#hash@ and @#label@ grey,
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
yellow even before the session knows it. A unit is cyan where a dimension
goes (design §4.1): as an argument, @Num m@, or in a product, @(m/s^2)@;
elsewhere a name named like a unit is a type, @(g → m) → {g}@.
-}
colourTokens :: Level -> Names -> [(Int, Int, Token)] -> [(Int, Int, Colour)]
colourTokens level names located =
  go Nothing (zip located (tokenLevels level [tok | (_, _, tok) <- located]))
 where
  shadowed = case level of
    Expression -> binders [tok | (_, _, tok) <- located]
    TypeLevel -> Set.empty
  -- A type's variables shadow units of their names (design §4.8).
  bound = typeBinders [tok | (_, _, tok) <- located]
  go _ [] = []
  go prev (((s, e, tok), here) : rest) =
    let next = case rest of
          ((_, _, n), _) : _ -> Just n
          [] -> Nothing
     in [(s, e, c) | Just c <- [colourOf here prev next tok]]
          ++ go (Just tok) rest
  colourOf here prev next = \case
    TKw _ -> Just Magenta
    TIdent "structural" | next == Just (TKw KData) -> Just Magenta
    THashLabel _ -> Just Grey
    TIdent n -> case here of
      Expression
        | n `Set.member` names.conWords -> Just Yellow
        | n `Set.member` names.unitWords, n `Set.notMember` shadowed -> Just Cyan
        | n `Set.member` names.typeWords -> Just Yellow
      TypeLevel
        | n `Set.member` bound -> Nothing
        | n `Set.member` names.typeWords || n `Set.member` names.conWords -> Just Yellow
        | prev `elem` map Just [TKw KData, TEquals, TBar] -> Just Yellow
        | n `Set.member` names.unitWords
        , maybe False argument prev
            || maybe False multiplies prev
            || maybe False powered next ->
            Just Cyan
      _ -> Nothing
    _ -> Nothing
  -- What a type argument follows: the name it is applied to, or an argument.
  argument = \case
    TIdent _ -> True
    TNum _ -> True
    TRParen -> True
    TRBracket -> True
    _ -> False
  multiplies = (`elem` [TOp "*", TOp "·", TOp "/"])
  powered t = multiplies t || t == TOp "^" || case t of TSup _ -> True; _ -> False

{- | The variables a line's types bind (design §4.8): the names between
@forall@ and the next @.@, and a @data@ declaration's parameters. As for
'binders', a name bound anywhere on the line is a variable everywhere in
its types.
-}
typeBinders :: [Token] -> Set Text
typeBinders = \case
  [] -> Set.empty
  TKw KForall : rest ->
    let (region, after) = break (== TOp ".") rest
     in Set.fromList [n | TIdent n <- region] <> typeBinders after
  TKw KData : TIdent _ : rest ->
    let (region, after) = break (== TEquals) rest
     in Set.fromList [n | TIdent n <- region] <> typeBinders after
  _ : rest -> typeBinders rest

{- | Each token's level. In an expression, what follows @::@ is a type
(design §4.8): to the end of the statement for a signature, @area ::
Shape -> Num (m^2)@, and to the closing parenthesis for an ascription,
@(e :: Num m)@. The @::@ itself is plain.
-}
tokenLevels :: Level -> [Token] -> [Level]
tokenLevels = \case
  TypeLevel -> map (const TypeLevel)
  Expression -> go (0 :: Int) Nothing
 where
  go _ _ [] = []
  go parens typeFrom (t : ts) = case t of
    TOp "::" -> Expression : go parens (Just parens) ts
    TSep -> Expression : go parens Nothing ts
    TLParen -> levelOf typeFrom : go (parens + 1) typeFrom ts
    TRParen ->
      let parens' = max 0 (parens - 1)
          typeFrom' = if maybe False (> parens') typeFrom then Nothing else typeFrom
       in levelOf typeFrom' : go parens' typeFrom' ts
    _ -> levelOf typeFrom : go parens typeFrom ts
  levelOf = maybe Expression (const TypeLevel)

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

-- Continuation lines -------------------------------------------------------------

-- | Why an input goes on at a continuation line (design §7.3).
data Continuation
  = -- | a @(@, @[@ or @{@ is not closed yet
    Unclosed
  | {- | a line ends in @of@ or @where@: the block's entries are on the
    lines that follow, and a blank line ends it
    -}
    Block
  | -- | the last token cannot end an input: @=@, an operator, @then@, @,@ …
    Trailing Text
  deriving stock (Eq, Show)

{- | Whether the REPL input so far, its lines joined by newlines, goes on at
a continuation line, and why. 'Nothing' means feed it now.

* A @:@ command never goes on.
* After the first line, a blank line ends the input as it stands.
* Text that does not lex is fed as it stands, so the lexer's error shows.
* Otherwise, by the lexer's tokens, comments already gone: an unclosed
  bracket, a line that ends in @of@ or @where@, a line that is a
  @namespace@ and its path (design §7.6), or a last token that cannot
  end an input (@=@, @->@, @\\@, @|@, @,@, @;@, @`@, @√@, an infix operator,
  @±@, or a keyword other than @true@ and @false@).

A field access glued to a value, @b.mass@, is one token and ends an input;
a @.@ with nothing after it is composition and does not.
-}
continuation :: Text -> Maybe Continuation
continuation src
  | ":" `T.isPrefixOf` T.stripStart src = Nothing
  | T.any (== '\n') src && T.all isSpace (T.takeWhileEnd (/= '\n') src) = Nothing
  | otherwise = case tokenize src of
      Left _ -> Nothing
      Right located ->
        let
          -- Layout's separators and block ends are empty; written ones are not.
          toks = [t | t <- located, t.span.from /= t.span.to]
          depth = sum (map (bracket . (.value)) toks)
          lineGroups = NE.groupWith (\t -> t.span.from.line) toks
          lineEnds = map NE.last lineGroups
          -- A line that is only @namespace a.b@ opens a block (design §7.6).
          namespaceHeader g = case map (.value) (NE.toList g) of
            TKw KNamespace : path -> not (null path) && all isPathTok path
            _ -> False
         in
          case reverse toks of
            _ | depth > 0 -> Just Unclosed
            _ | any (opensBlock . (.value)) lineEnds -> Just Block
            _ | any namespaceHeader lineGroups -> Just Block
            t : _ | cannotEnd t.value -> Just (Trailing (showToken t.value))
            _ -> Nothing
 where
  isPathTok = \case
    TIdent _ -> True
    TField _ -> True
    _ -> False
  bracket :: Token -> Int
  bracket = \case
    TLParen -> 1
    TLBracket -> 1
    TLBrace -> 1
    TRParen -> -1
    TRBracket -> -1
    TRBrace -> -1
    _ -> 0
  opensBlock = \case
    TKw KOf -> True
    TKw KWhere -> True
    _ -> False
  cannotEnd = \case
    TKw KTrue -> False
    TKw KFalse -> False
    TKw _ -> True
    TEquals -> True
    TArrow -> True
    TLambda -> True
    TBar -> True
    TComma -> True
    TSep -> True
    TSemis _ -> True
    TBacktick -> True
    TSqrt -> True
    TOp _ -> True
    TPlusMinus _ -> True
    _ -> False

-- | Whether the input so far goes on at a continuation line: 'continuation'.
needsMore :: Text -> Bool
needsMore = isJust . continuation
