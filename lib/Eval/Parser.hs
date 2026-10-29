{-# LANGUAGE TypeFamilies #-}

{- | The parser (design §2.5 to §2.7): megaparsec over the token stream from
"Eval.Lexer". Produces the surface AST of "Eval.Syntax".
-}
module Eval.Parser (
  parseProgram,
  parseExpr,
) where

import Control.Monad.Combinators.Expr
import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Ratio (denominator, numerator)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Eval.Core (NudgeKind)
import Eval.Lexer
import Eval.Syntax
import Text.Megaparsec qualified as P

-- Token stream ---------------------------------------------------------------

data TokStream = TokStream {source :: Text, toks :: [Located Token]}

instance P.Stream TokStream where
  type Token TokStream = Located Token
  type Tokens TokStream = [Located Token]
  tokenToChunk _ = pure
  tokensToChunk _ = id
  chunkToTokens _ = id
  chunkLength _ = length
  chunkEmpty _ = null
  take1_ s = case s.toks of
    [] -> Nothing
    t : ts -> Just (t, s{toks = ts})
  takeN_ n s
    | n <= 0 = Just ([], s)
    | null s.toks = Nothing
    | otherwise = let (a, b) = splitAt n s.toks in Just (a, s{toks = b})
  takeWhile_ p s = let (a, b) = span p s.toks in (a, s{toks = b})

instance P.VisualStream TokStream where
  showTokens _ = T.unpack . T.unwords . map (showToken . (.value)) . NE.toList
  tokensLength _ = length

instance P.TraversableStream TokStream where
  reachOffset o pst =
    let s = P.pstateInput pst
        (pre, post) = splitAt (o - P.pstateOffset pst) s.toks
        srcName = P.sourceName (P.pstateSourcePos pst)
        mk p = P.SourcePos srcName (P.mkPos (max 1 p.line)) (P.mkPos (max 1 p.col))
        pos = case post of
          t : _ -> mk t.span.from
          [] -> case reverse pre of
            t : _ -> mk t.span.to
            [] -> P.pstateSourcePos pst
        lineNo = P.unPos (P.sourceLine pos)
        lineText = case drop (lineNo - 1) (T.lines s.source) of
          l : _ -> T.unpack l
          [] -> ""
     in ( Just lineText
        , pst
            { P.pstateInput = s{toks = post}
            , P.pstateOffset = max (P.pstateOffset pst) o
            , P.pstateSourcePos = pos
            }
        )

type Parser = P.Parsec Void TokStream

-- Entry points -----------------------------------------------------------------

parseProgram :: Text -> Either Text [Statement]
parseProgram src = do
  toks <- tokenize src
  runP program src toks

parseExpr :: Text -> Either Text Expr
parseExpr src = do
  toks <- tokenize src
  runP (P.many (tok TSep) *> expr <* P.many (tok TSep)) src toks

runP :: Parser a -> Text -> [Located Token] -> Either Text a
runP p src toks =
  first
    (T.pack . P.errorBundlePretty)
    (P.runParser (p <* P.eof) "<input>" (TokStream src toks))

-- Token helpers --------------------------------------------------------------------

dummy :: Span
dummy = Span (Pos 1 1) (Pos 1 1)

tok :: Token -> Parser Span
tok t =
  P.token
    (\lt -> if lt.value == t then Just lt.span else Nothing)
    (Set.singleton (P.Tokens (Located dummy t :| [])))

match :: String -> (Token -> Maybe a) -> Parser (Span, a)
match label f =
  P.token
    (\lt -> (lt.span,) <$> f lt.value)
    (Set.singleton (P.Label (NE.fromList label)))

kw :: Keyword -> Parser Span
kw = tok . TKw

{- | A binary operator token, but not when a @)@ follows: that is a right
section, and the expression parser must stop before it.
-}
opTok :: Text -> Parser Span
opTok o = P.try (tok (TOp o) <* P.notFollowedBy (tok TRParen))

name :: Parser Name
name =
  (\(sp, t) -> Name sp t)
    <$> match "identifier" (\case TIdent t -> Just t; _ -> Nothing)

-- Statements ---------------------------------------------------------------------

program :: Parser [Statement]
program = P.many (tok TSep) *> P.sepEndBy statement (P.some (tok TSep))

statement :: Parser Statement
statement = letStatement P.<|> unitStatement P.<|> SExpr <$> expr

-- | @unit name = expr@: a definition that is also a display unit.
unitStatement :: Parser Statement
unitStatement = do
  s <- kw KUnit
  n <- name
  _ <- tok TEquals
  e <- expr
  pure (SLet (Binding (spanUnion s e.span) n [] e True))

{- | @let b@ as a definition (optionally with @where@), or @let b in e@ as an
expression statement. Both start the same way, so they share a prefix.
-}
letStatement :: Parser Statement
letStatement = do
  s <- kw KLet
  b <- binding
  P.choice
    [ do
        _ <- kw KIn
        body <- expr
        pure (SExpr (Expr (spanUnion s body.span) (Let b.name b.params b.body body)))
    , do
        wh <- P.optional whereClause
        let body' = maybe b.body (foldr wrapWhere b.body) wh
            sp = foldr (spanUnion . (.span)) (spanUnion s b.span) (maybe [] id wh)
        pure (SLet (Binding sp b.name b.params body' False))
    ]
 where
  wrapWhere wb acc = Expr (spanUnion wb.span acc.span) (Let wb.name wb.params wb.body acc)

binding :: Parser Binding
binding = do
  n <- name
  ps <- P.many name
  _ <- tok TEquals
  e <- expr
  pure (Binding (spanUnion n.span e.span) n ps e False)

whereClause :: Parser [Binding]
whereClause = kw KWhere *> P.sepBy1 binding (tok TSep) <* tok TBlockEnd

-- Expressions ----------------------------------------------------------------------

expr :: Parser Expr
expr = P.choice [lambda, letIn, ifExpr, opExpr]

lambda :: Parser Expr
lambda = do
  s <- tok TLambda
  ps <- P.some name
  _ <- tok TArrow
  b <- expr
  pure (Expr (spanUnion s b.span) (Lam ps b))

letIn :: Parser Expr
letIn = do
  s <- kw KLet
  b <- binding
  _ <- kw KIn
  body <- expr
  pure (Expr (spanUnion s body.span) (Let b.name b.params b.body body))

ifExpr :: Parser Expr
ifExpr = do
  s <- kw KIf
  c <- expr
  _ <- kw KThen
  t <- expr
  _ <- kw KElse
  e <- expr
  pure (Expr (spanUnion s e.span) (If c t e))

opExpr :: Parser Expr
opExpr = makeExprParser term table
 where
  table =
    [ [InfixR (binop Compose <$ opTok "."), InfixL backtick]
    , [Prefix (foldr1 (.) <$> P.some (negP P.<|> sqrtP))]
    ,
      [ InfixL (binop Outer <$ opTok "*")
      , InfixL (binop Dot <$ opTok "@")
      , InfixN (binop Cross <$ opTok "×")
      , InfixL (binop Wedge <$ opTok "/\\")
      , InfixL (binop EMul <$ opTok ".*")
      , InfixL (binop EDiv <$ opTok "./")
      , InfixL (binop Div <$ opTok "/")
      ]
    , [InfixL (binop Add <$ opTok "+"), InfixL (binop Sub <$ opTok "-")]
    , [InfixN plusMinus]
    ,
      [ InfixN (binop Eq <$ opTok "==")
      , InfixN (binop Ne <$ opTok "/=")
      , InfixN (binop Le <$ opTok "<=")
      , InfixN (binop Ge <$ opTok ">=")
      , InfixN (binop Lt <$ opTok "<")
      , InfixN (binop Gt <$ opTok ">")
      ]
    , [InfixR (binop And <$ opTok "&&")]
    , [InfixR (binop Or <$ opTok "||")]
    , [InfixN (binop To <$ kw KTo)]
    ]
  negP = do
    s <- tok (TOp "-")
    pure (\e -> Expr (spanUnion s e.span) (Neg e))
  sqrtP = do
    s <- tok TSqrt
    pure (\e -> Expr (spanUnion s e.span) (App (Expr s (Var "sqrt")) e))
  backtick = do
    _ <- tok TBacktick
    n <- name
    _ <- tok TBacktick
    pure (binop (Infix n.text))
  plusMinus = do
    (_, k) <- match "±" (\case TPlusMinus k -> Just k; _ -> Nothing)
    pure (binop (PlusMinus k))

binop :: Op -> Expr -> Expr -> Expr
binop o a b = Expr (spanUnion a.span b.span) (BinOp o a b)

-- | An application or quantity, optionally raised to a literal power.
term :: Parser Expr
term = do
  base <- application
  withPower base

withPower :: Expr -> Parser Expr
withPower base = do
  pw <- P.optional powerSuffix
  pure (maybe base (\(sp, n) -> Expr (spanUnion base.span sp) (Pow base n)) pw)

powerSuffix :: Parser (Span, Integer)
powerSuffix = caret P.<|> match "superscript" (\case TSup n -> Just n; _ -> Nothing)
 where
  caret = do
    s <- tok (TOp "^")
    neg <- P.optional (tok (TOp "-"))
    (s2, n) <-
      match
        "integer literal"
        (\case TNum r | denominator r == 1 -> Just (numerator r); _ -> Nothing)
    pure (spanUnion s s2, maybe n (const (negate n)) neg)

{- | Application by juxtaposition, or the quantity rule (§2.6) when the head
is a number or vector literal.
-}
application :: Parser Expr
application = do
  hd <- atom
  case hd.node of
    Num _ -> quantity hd
    Vec _ -> quantity hd
    _ -> do
      args <- P.many atom
      pure (foldl (\f a -> Expr (spanUnion f.span a.span) (App f a)) hd args)
 where
  quantity hd = do
    units <- P.many unitAtom
    pure (foldl (binop Outer) hd units)
  unitAtom = atom >>= withPower

-- | A primary expression with any glued projections.
atom :: Parser Expr
atom = do
  p <- primary
  projs <- P.many (match "projection" (\case TProj i -> Just i; _ -> Nothing))
  pure (foldl (\acc (sp, i) -> Expr (spanUnion acc.span sp) (Proj acc i)) p projs)

primary :: Parser Expr
primary =
  P.choice
    [ (\(sp, r) -> Expr sp (Num r))
        <$> match "number" (\case TNum r -> Just r; _ -> Nothing)
    , (\sp -> Expr sp (Bool True)) <$> kw KTrue
    , (\sp -> Expr sp (Bool False)) <$> kw KFalse
    , (\n -> Expr n.span (Var n.text)) <$> name
    , parens
    , vecOrMat
    ]

{- | @(e)@, a left section @(op e)@, or a right section @(e op)@. @(- e)@ is
negation, as in Haskell, so @-@ is excluded from left sections.
-}
parens :: Parser Expr
parens = do
  s <- tok TLParen
  P.choice
    [ P.try $ do
        o <- sectionOp False
        e <- expr
        e2 <- tok TRParen
        pure (Expr (spanUnion s e2) (SectionL o e))
    , do
        e <- expr
        P.choice
          [ do
              o <- sectionOp True
              e2 <- tok TRParen
              pure (Expr (spanUnion s e2) (SectionR e o))
          , do
              e2 <- tok TRParen
              pure (Expr (spanUnion s e2) e.node)
          ]
    ]

sectionOp :: Bool -> Parser Op
sectionOp allowMinus =
  P.choice
    $ [ Outer <$ tok (TOp "*")
      , Dot <$ tok (TOp "@")
      , Cross <$ tok (TOp "×")
      , Wedge <$ tok (TOp "/\\")
      , EMul <$ tok (TOp ".*")
      , EDiv <$ tok (TOp "./")
      , Div <$ tok (TOp "/")
      , Add <$ tok (TOp "+")
      , Eq <$ tok (TOp "==")
      , Ne <$ tok (TOp "/=")
      , Le <$ tok (TOp "<=")
      , Ge <$ tok (TOp ">=")
      , Lt <$ tok (TOp "<")
      , Gt <$ tok (TOp ">")
      , And <$ tok (TOp "&&")
      , Or <$ tok (TOp "||")
      , Compose <$ tok (TOp ".")
      , To <$ kw KTo
      , PlusMinus <$> plusMinusKind
      , Infix . (.text) <$> (tok TBacktick *> name <* tok TBacktick)
      ]
      ++ [Sub <$ tok (TOp "-") | allowMinus]
 where
  plusMinusKind :: Parser NudgeKind
  plusMinusKind = snd <$> match "±" (\case TPlusMinus k -> Just k; _ -> Nothing)

{- | A bracket literal. Nested brackets are simply vectors of vectors; a
ragged nesting is a shape error found by the type checker.
-}
vecOrMat :: Parser Expr
vecOrMat = do
  s <- tok TLBracket
  es <- P.sepBy expr (tok TComma)
  e <- tok TRBracket
  pure (Expr (spanUnion s e) (Vec es))
