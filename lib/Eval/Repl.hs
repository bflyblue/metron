{- | The REPL's pure parts (design §7.3): tab completion, output colour, and
whether an input goes on at a continuation line. The executable wires them
into haskeline; they live here so the test suite can reach them. Nothing
here changes what 'Eval.Driver.feed' prints.
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
  Kind (..),
  classify,
  paint,
  splitUnits,

  -- * Continuation lines
  Continuation (..),
  continuation,
  needsMore,
) where

import Control.Applicative ((<|>))
import Data.Char (isAlphaNum, isDigit, isLetter, isSpace)
import Data.List (isPrefixOf, nub, sort)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase (Codebase (..))
import Eval.Driver (Session (..))
import Eval.Lexer (Keyword (..), Located (..), Token (..), showToken, tokenize)
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

-- | What a printed line is, for colour.
data Kind
  = -- | printed as is
    Plain
  | -- | a note about what a command did: dim
    Note
  | -- | @name : type@: the type dim
    Signature
  | -- | a value: its trailing unit dim
    Value
  | -- | the source excerpt of an error: as is
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
    | isSignature l = Signature
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
      ]
      || ("(" `T.isPrefixOf` l && "prelude names hidden" `T.isInfixOf` l)
  -- @area : …@, @unit km : …@; not a cons pattern inside a :view.
  isSignature l = case T.breakOn " : " l of
    (lhs, rhs) | not (T.null rhs) -> isName (dropFlag lhs)
    _ -> False
  dropFlag lhs = fromMaybe lhs (T.stripPrefix "unit " lhs <|> T.stripPrefix "scale " lhs)
  isName n = case T.uncons n of
    Just (c, rest) -> (isLetter c || c == '_') && T.all identChar rest
    Nothing -> False

-- | A line with ANSI SGR codes for its kind. Empty text gets none.
paint :: Kind -> Text -> Text
paint kind t = case kind of
  Plain -> t
  Source -> t
  Note -> dim t
  Problem -> sgr "31" t
  Caret -> sgr "1;31" t
  Signature -> case T.breakOn " : " t of
    (lhs, rhs) | not (T.null rhs) -> lhs <> " : " <> dim (T.drop 3 rhs)
    _ -> t
  Value -> let (body, units) = splitUnits t in body <> dim units
 where
  dim = sgr "2"
  sgr code s
    | T.null s = s
    | otherwise = "\ESC[" <> code <> "m" <> s <> "\ESC[0m"

{- | A value's trailing unit, split off: the longest run of unit words at
the end (identifiers with an optional @^n@ or superscript power, joined by
@/@, and @(point)@), when what precedes it ends a number or a bracket
(a digit, @…@, @]@, @)@ or @}@). The two parts concatenate to the input;
the second is empty when there is no unit.
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
  bracket, a line that ends in @of@ or @where@, or a last token that cannot
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
          lineEnds = map NE.last (NE.groupWith (\t -> t.span.from.line) toks)
         in
          case reverse toks of
            _ | depth > 0 -> Just Unclosed
            _ | any (opensBlock . (.value)) lineEnds -> Just Block
            t : _ | cannotEnd t.value -> Just (Trailing (showToken t.value))
            _ -> Nothing
 where
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
