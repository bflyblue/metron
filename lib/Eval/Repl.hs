{- | The REPL's pure parts (design §7.3): tab completion.
The executable wires them into haskeline; they live here so the test suite
can reach them. Nothing here changes what 'Eval.Driver.feed' prints.
-}
module Eval.Repl (
  -- * Completion
  Completion (..),
  complete,
  completions,
  loadsFile,
  commands,
  keywords,
) where

import Data.Char (isAlphaNum, isDigit, isSpace)
import Data.List (isPrefixOf, nub, sort)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Eval.Codebase (Codebase (..))
import Eval.Driver (Session (..))

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

The word is the identifier ending at the cursor, with a @.@ before it for a
field and a @:@ before it at the start of a line for a command.
-}
complete :: Session -> (String, String) -> Maybe (String, [Completion])
complete session (leftRev, _)
  | loadsFile (reverse leftRev) = Nothing
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

{- | The candidates for one word, given the reversed text before it, as
haskeline's @completeWordWithPrev@ passes them.

* @:cmd@ at the start of a line: commands.
* After @:set@: its arguments.
* @.f@: record fields.
* Otherwise: names, type names, constructor names and keywords.
-}
completions :: Session -> String -> String -> [Completion]
completions session prev word = case word of
  ':' : _ | all isSpace prev -> plain commands
  '.' : f ->
    [ Completion ('.' : n) n True
    | n <- sorted (map T.unpack (Map.keys cb.fieldNames))
    , f `isPrefixOf` n
    ]
  _ -> case words (reverse prev) of
    [":set"] -> plain ["precision", "sigma", "unicode"]
    [":set", "unicode"] -> plain ["on", "off"]
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
