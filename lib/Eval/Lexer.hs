{- | The lexer (design §2.1, §2.8) and the layout pass.

Source text is NFC-normalised, confusable characters are folded, and the
unicode spellings of §2.8 are mapped to canonical tokens as they are read,
so spans refer to the normalised text. Every token records whether it was
glued to the previous one (no whitespace between), which the superscript
and projection rules need. The layout pass then turns newlines into
statement separators and @where@ blocks into delimited groups.
-}
module Eval.Lexer (
  Token (..),
  Keyword (..),
  Located (..),
  tokenize,
  prepare,
  showToken,
) where

import Data.Char (isAlphaNum, isDigit, isLetter)
import Data.Functor (($>))
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Normalize (NormalizationMode (NFC), normalize)
import Data.Void (Void)
import Eval.Core (NudgeKind (..))
import Eval.Syntax (Pos (..), Span (..))
import Text.Megaparsec hiding (Pos, Token, Tokens)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

data Keyword
  = KLet
  | KUnit
  | KChart
  | KAt
  | KCase
  | KOf
  | KIn
  | KWhere
  | KIf
  | KThen
  | KElse
  | KTo
  | KTrue
  | KFalse
  | KData
  | KNamespace
  | KUse
  | -- | @forall@ (or @∀@) at the head of a signature or an ascription (design §4.8)
    KForall
  | -- | @space@: a space's declaration (design §3.10, F2)
    KSpace
  | -- | @on@: a chart's parent, and subtraction in a frame (design §3.10, F10)
    KOn
  | -- | @from@: a conversion from a configuration (design §3.10, F7)
    KFrom
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data Token
  = TNum Rational
  | TIdent Text
  | TKw Keyword
  | {- | A binary operator in its canonical ASCII spelling: @+ - * / ^ == /=
    < <= > >= && ||@ and @.@ for composition; @·@ keeps its own, the
    matrix product @\@@ in an expression and a product in a dimension.
    -}
    TOp Text
  | -- | @±@ or @±σ@.
    TPlusMinus NudgeKind
  | TLambda
  | TArrow
  | TEquals
  | TBacktick
  | -- | @|@ between the constructors of a @data@ declaration
    TBar
  | TLParen
  | TRParen
  | TLBracket
  | TRBracket
  | TLBrace
  | TRBrace
  | TComma
  | TSqrt
  | -- | A superscript power glued to the preceding atom: @m²@, @s⁻²@.
    TSup Integer
  | -- | A field access glued to the preceding atom: @b.mass@ (§2.10).
    TField Text
  | {- | A dot and a name not glued to an atom: an absolute name, @.km@, the
    root's @km@ whatever the scope (design §7.6).
    -}
    TAbs Text
  | -- | A projection glued to the preceding atom: @v.0@, @m.1.2@.
    TProj Int
  | {- | A wildcard glued to the preceding atom, skipping one axis before a
    projection: the @._@ of @m._.0@ (§2.10).
    -}
    TWild
  | -- | @#label@ after a @±@, @noise@ or @gauss@ (§3.2.4).
    THashLabel Text
  | -- | Statement or binding separator: a @;@, or layout. Inside brackets, a row separator.
    TSep
  | -- | @;;@, @;;;@ …: a separator of rank two or more inside a bracket literal (§2.4).
    TSemis Int
  | -- | End of a @where@ block, inserted by layout.
    TBlockEnd
  deriving stock (Eq, Ord, Show)

data Located a = Located {span :: Span, value :: a}
  deriving stock (Eq, Ord, Show)

{- | Lex, check adjacency rules, and apply layout. The result is ready for
"Eval.Parser". Errors are rendered as text.
-}
tokenize :: Text -> Either Text [Located Token]
tokenize src =
  case runParser rawTokens "<input>" (prepare src) of
    Left bundle -> Left (T.pack (errorBundlePretty bundle))
    Right raws -> layout <$> adjacency raws

{- | NFC normalisation plus confusable folding (design §2.1). Folding is
length-preserving; NFC can shorten text that used combining characters,
in which case spans refer to the normalised form.
-}
prepare :: Text -> Text
prepare = T.map fold . normalize NFC
 where
  fold = \case
    '\x00B5' -> '\x03BC' -- micro sign → Greek mu
    '\x2126' -> '\x03A9' -- ohm sign → Greek Omega
    c -> c

-- Raw tokens --------------------------------------------------------------

type Lexer = Parsec Void Text

rawTokens :: Lexer [Located Token]
rawTokens = do
  ws
  toks <- many rawToken
  eof
  pure toks

ws :: Lexer ()
ws = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

-- | One token with its span. Gluedness is derived from spans in 'adjacency'.
rawToken :: Lexer (Located Token)
rawToken = do
  start <- getSourcePos
  t <- tokenBody
  end <- getSourcePos
  ws
  pure (Located (Span (toPos start) (toPos end)) t)

toPos :: SourcePos -> Pos
toPos p = Pos (unPos (sourceLine p)) (unPos (sourceColumn p))

tokenBody :: Lexer Token
tokenBody =
  choice
    [ TNum <$> number
    , superscript
    , hashLabel
    , identifierOrKeyword
    , symbol
    ]

-- | @3@, @9.81@, @1e-3@, @1_000_000@. Always an exact rational.
number :: Lexer Rational
number = do
  intPart <- digits
  fracPart <- optional (try (char '.' *> digits))
  expPart <- optional (try exponentPart)
  let mant = read (T.unpack (intPart <> fromMaybe "" fracPart)) :: Integer
      fracLen = maybe 0 T.length fracPart
      e = fromMaybe 0 expPart - fromIntegral fracLen
  pure (if e >= 0 then fromInteger (mant * 10 ^ e) else mant % (10 ^ negate e))
 where
  digits :: Lexer Text
  digits = do
    d <- digitChar
    rest <- takeWhileP (Just "digit") (\c -> isDigit c || c == '_')
    pure (T.filter (/= '_') (T.cons d rest))
  exponentPart :: Lexer Integer
  exponentPart = do
    _ <- char 'e' <|> char 'E'
    sign <- optional (char '-' <|> char '+')
    ds <- takeWhile1P (Just "digit") isDigit
    let n = read (T.unpack ds)
    pure (if sign == Just '-' then negate n else n)

{- | A glued power: an optional superscript minus followed by superscript
digits. Gluedness is checked afterwards from spans.
-}
superscript :: Lexer Token
superscript = do
  neg <- optional (char '⁻')
  ds <- takeWhile1P (Just "superscript digit") isSuperscriptDigit
  let n = foldl' (\acc c -> acc * 10 + supDigit c) 0 (T.unpack ds)
  pure (TSup (maybe n (const (negate n)) neg))
 where
  supDigit c = case c of
    '⁰' -> 0
    '¹' -> 1
    '²' -> 2
    '³' -> 3
    '⁴' -> 4
    '⁵' -> 5
    '⁶' -> 6
    '⁷' -> 7
    '⁸' -> 8
    '⁹' -> 9
    _ -> 0

-- | @#partA@: a measurement label, spelled like an identifier.
hashLabel :: Lexer Token
hashLabel =
  char '#'
    *> ( THashLabel
           <$> takeWhile1P
             (Just "label")
             (\x -> (isAlphaNum x && not (isSuperscriptDigit x)) || x == '_' || x == '\'')
       )

identifierOrKeyword :: Lexer Token
identifierOrKeyword = do
  c <- satisfy (\x -> isLetter x && x /= 'λ') <|> char '_'
  -- Superscript digits are alphanumeric to 'isAlphaNum' but are powers here.
  rest <-
    takeWhileP
      (Just "identifier character")
      ( \x ->
          (isAlphaNum x && not (isSuperscriptDigit x))
            || x == '_'
            || x == '\''
            || isSubscript x
      )
  let name = T.cons c rest
  pure $ case name of
    "let" -> TKw KLet
    "unit" -> TKw KUnit
    "chart" -> TKw KChart
    -- The old spelling of @chart@ (design §3.6), accepted for a release.
    "scale" -> TKw KChart
    "at" -> TKw KAt
    "space" -> TKw KSpace
    "on" -> TKw KOn
    "from" -> TKw KFrom
    "case" -> TKw KCase
    "of" -> TKw KOf
    "in" -> TKw KIn
    "where" -> TKw KWhere
    "if" -> TKw KIf
    "then" -> TKw KThen
    "else" -> TKw KElse
    "to" -> TKw KTo
    "true" -> TKw KTrue
    "false" -> TKw KFalse
    "data" -> TKw KData
    "namespace" -> TKw KNamespace
    "use" -> TKw KUse
    "forall" -> TKw KForall
    "π" -> TIdent "pi"
    _ -> TIdent name
 where
  isSubscript x = x >= '₀' && x <= '₉'

isSuperscriptDigit :: Char -> Bool
isSuperscriptDigit = (`elem` ("⁰¹²³⁴⁵⁶⁷⁸⁹" :: String))

-- | Symbols and their unicode spellings (design §2.8). Longest match first.
symbol :: Lexer Token
symbol =
  choice
    [ string "±σ" $> TPlusMinus Stat
    , string "+-s" $> TPlusMinus Stat
    , string "±" $> TPlusMinus Bound
    , string "+-" $> TPlusMinus Bound
    , string "->" $> TArrow
    , string "→" $> TArrow
    , string "==" $> TOp "=="
    , string "/=" $> TOp "/="
    , string "≠" $> TOp "/="
    , string "<=" $> TOp "<="
    , string "≤" $> TOp "<="
    , string ">=" $> TOp ">="
    , string "≥" $> TOp ">="
    , string "&&" $> TOp "&&"
    , string "/\\" $> TOp "/\\"
    , string "∧" $> TOp "/\\"
    , string "||" $> TOp "||"
    , string "∨" $> TOp "||"
    , char '|' $> TBar
    , string "∘" $> TOp "."
    , string ".+" $> TOp ".+"
    , string ".-" $> TOp ".-"
    , string ".*" $> TOp ".*"
    , string "./" $> TOp "./"
    , string "⊙" $> TOp ".*"
    , string "⊘" $> TOp "./"
    , string "⊗" $> TOp "*"
    , -- `·` is the matrix product `@` in an expression but a product in a
      -- dimension, where `@` is refused (design §4.1): a token of its own.
      oneOf ("·⋅" :: String) $> TOp "·"
    , char '@' $> TOp "@"
    , string "><" $> TOp "×"
    , char '×' $> TOp "×"
    , projection
    , wildcard
    , field
    , char '.' $> TOp "."
    , char '<' $> TOp "<"
    , char '>' $> TOp ">"
    , char '=' $> TEquals
    , char '+' $> TOp "+"
    , char '-' $> TOp "-"
    , char '*' $> TOp "*"
    , oneOf ("/÷" :: String) $> TOp "/"
    , char '^' $> TOp "^"
    , string "::" $> TOp "::"
    , char ':' $> TOp ":"
    , oneOf ("\\λ" :: String) $> TLambda
    , char '√' $> TSqrt
    , char '∀' $> TKw KForall
    , char '¬' $> TIdent "not"
    , char '⋆' $> TIdent "star"
    , string "°C" $> TIdent "degC"
    , string "°F" $> TIdent "degF"
    , char '°' $> TIdent "deg"
    , char '′' $> TIdent "arcmin"
    , char '″' $> TIdent "arcsec"
    , char '(' $> TLParen
    , char ')' $> TRParen
    , char '[' $> TLBracket
    , char ']' $> TRBracket
    , char '{' $> TLBrace
    , char '}' $> TRBrace
    , char ',' $> TComma
    , char '`' $> TBacktick
    , (\n -> if n == 1 then TSep else TSemis n) . length <$> some (char ';')
    ]

{- | @.0@, @.12@: a projection only when digits follow the dot immediately;
otherwise the dot is composition. Named positions (@.x@, @.pos@) are a
future sugar defined at the desugaring layer (design §2.10), not lexemes.
-}
projection :: Lexer Token
projection = try $ do
  _ <- char '.'
  TProj . read . T.unpack <$> takeWhile1P (Just "digit") isDigit

{- | @._@: a wildcard axis, as in @m._.0@ (column 0) and @t._._.2@. The
@_@ must not start an identifier: @x._y@ stays the composition of @x@ and
@_y@.
-}
wildcard :: Lexer Token
wildcard = try $ do
  _ <- char '.'
  _ <- char '_'
  notFollowedBy (satisfy (\x -> isAlphaNum x || x == '_' || x == '\''))
  pure TWild

-- | @.name@: a record field, glued to what precedes it (§2.10).
field :: Lexer Token
field = try $ do
  _ <- char '.'
  c <- satisfy (\x -> isLetter x && x /= 'λ')
  rest <-
    takeWhileP
      (Just "identifier character")
      (\x -> (isAlphaNum x && not (isSuperscriptDigit x)) || x == '_' || x == '\'')
  pure (TField (T.cons c rest))

-- Adjacency ----------------------------------------------------------------

{- | Compute gluedness from spans and enforce the rules that depend on it:
a superscript or projection must be glued to an atom-ending token.
-}
adjacency :: [Located Token] -> Either Text [Located Token]
adjacency = go Nothing
 where
  go _ [] = Right []
  go prev (t : ts) = do
    let gluedToPrev = case prev of
          Just p -> p.span.to == t.span.from
          Nothing -> False
        endsAtom = case prev of
          Just p -> case p.value of
            TIdent _ -> True
            TRParen -> True
            TRBracket -> True
            TProj _ -> True
            TWild -> True
            TField _ -> True
            TAbs _ -> True
            TNum _ -> True
            TSup _ -> True
            TKw KTrue -> True
            TKw KFalse -> True
            _ -> False
          Nothing -> False
    case t.value of
      TSup _
        | not (gluedToPrev && endsAtom) ->
            Left
              ( at
                  t.span
                  "a superscript power must be attached to the thing it raises, as in m² or x⁻¹"
              )
      TProj _
        | not (gluedToPrev && endsAtom) ->
            Left
              ( at
                  t.span
                  "a projection like .0 must be attached to a vector or matrix, as in v.0"
              )
      TWild
        | not (gluedToPrev && endsAtom) ->
            Left
              ( at
                  t.span
                  "a wildcard ._ must be attached to a tensor and followed by a position, as in m._.0"
              )
      _ -> pure ()
    -- A dot and a name not glued to an atom start one: an absolute name,
    -- @.km@ (design §7.6). Glued, they are a field access.
    let t' = case t.value of
          TField f | not (gluedToPrev && endsAtom) -> t{value = TAbs f}
          _ -> t
    rest <- go (Just t') ts
    pure (t' : rest)
  at sp msg = T.pack (show sp.from.line) <> ":" <> T.pack (show sp.from.col) <> ": " <> msg

-- Layout ---------------------------------------------------------------------

{- | The layout pass (design §2.1, §2.2). A token that starts a new line at the
column of the enclosing context begins a new statement or binding, so a
'TSep' is inserted before it. The top-level context is column 1. The first
token after @where@ or @of@ opens a new context at its own column, and so
does the first token after the path of a @namespace@ (design §7.6) when it
is indented further than the enclosing context; otherwise the namespace's
block is empty. A token on a new line to the left of a context's column
closes it with 'TBlockEnd'. A line indented deeper than its context is a
continuation.
-}
layout :: [Located Token] -> [Located Token]
layout = go [Block 1] Nothing Closed
 where
  go :: [Frame] -> Maybe Span -> Opening -> [Located Token] -> [Located Token]
  go stack prev opening [] =
    let here = maybe (Pos 1 1) (.to) prev
     in -- A namespace with nothing after its path has an empty block.
        [Located (Span here here) TBlockEnd | Header <- [opening]]
          ++ [Located (Span here here) TBlockEnd | Block _ <- take (length stack - 1) stack]
  go stack prev Header (t : ts)
    -- The path of a namespace: a name and its glued fields, on one line.
    | isPathTok t.value
    , maybe True (\p -> p.to.line == t.span.from.line) prev =
        t : go stack (Just t.span) Header ts
    -- A block indented no further than its context is empty.
    | Just p <- prev
    , t.span.from.line > p.to.line
    , maybe False (t.span.from.col <=) (top (dropWhile isOpen stack)) =
        Located (Span t.span.from t.span.from) TBlockEnd : go stack prev Closed (t : ts)
    | otherwise = go stack prev Next (t : ts)
  go stack _ Next (t : ts) =
    let opened = Block t.span.from.col : stack
     in t
          : go
            (if isOpenTok t.value then Open : opened else opened)
            (Just t.span)
            (opensBlock t)
            ts
  go stack prev Closed (t : ts)
    -- A closing bracket ends every block opened since its opening bracket
    -- (Haskell's parse-error rule, for the one case that matters).
    | isClose t.value =
        let (inside, rest) = break isOpen stack
            ends = [Located (Span t.span.from t.span.from) TBlockEnd | Block _ <- inside]
         in ends ++ (t : go (drop 1 rest) (Just t.span) Closed ts)
    | isOpenTok t.value = t : go (Open : stack) (Just t.span) Closed ts
    | Just p <- prev
    , t.span.from.line > p.to.line =
        let c = t.span.from.col
            (closed, stack') = span (\case Block k -> k > c; Open -> False) stack
            here = Span t.span.from t.span.from
            ends = map (const (Located here TBlockEnd)) closed
            -- An explicit ';' at the start of a line is already a separator.
            sep = [Located here TSep | top stack' == Just c, t.value /= TSep]
         in ends ++ sep ++ (t : go stack' (Just t.span) (opensBlock t) ts)
    | otherwise = t : go stack (Just t.span) (opensBlock t) ts
  top = \case
    Block c : _ -> Just c
    _ -> Nothing
  opensBlock t = case t.value of
    TKw KWhere -> Next
    TKw KOf -> Next
    TKw KNamespace -> Header
    _ -> Closed
  isPathTok = \case
    TIdent _ -> True
    TAbs _ -> True
    TField _ -> True
    _ -> False
  isOpenTok = \case
    TLParen -> True
    TLBracket -> True
    TLBrace -> True
    _ -> False
  isClose = \case
    TRParen -> True
    TRBracket -> True
    TRBrace -> True
    _ -> False
  isOpen = \case
    Open -> True
    _ -> False

{- | Whether the next token opens a layout block: after @where@ and @of@ it
does; after @namespace@, once the path has been read.
-}
data Opening = Closed | Next | Header

-- | A layout context: a block at a column, or an open bracket.
data Frame = Block Int | Open

-- | For error messages.
showToken :: Token -> Text
showToken = \case
  TNum r -> T.pack (show (fromRational r :: Double))
  TIdent n -> n
  TKw k -> T.toLower (T.drop 1 (T.pack (show k)))
  TOp o -> o
  TPlusMinus Bound -> "±"
  TPlusMinus Stat -> "±σ"
  TLambda -> "\\"
  TArrow -> "->"
  TEquals -> "="
  TBacktick -> "`"
  TBar -> "|"
  TLParen -> "("
  TRParen -> ")"
  TLBracket -> "["
  TLBrace -> "{"
  TRBrace -> "}"
  TRBracket -> "]"
  TComma -> ","
  TSqrt -> "sqrt"
  TSup n -> "^" <> T.pack (show n)
  TProj i -> "." <> T.pack (show i)
  TWild -> "._"
  TField f -> "." <> f
  TAbs f -> "." <> f
  THashLabel l -> "#" <> l
  TSep -> "newline"
  TSemis n -> T.replicate n ";"
  TBlockEnd -> "end of block"
