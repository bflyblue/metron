{-# LANGUAGE TypeFamilies #-}

{- | The parser (design §2.5 to §2.7): megaparsec over the token stream from
"Eval.Lexer". Produces the surface AST of "Eval.Syntax".
-}
module Eval.Parser (
  parseProgram,
  parseExpr,
  parseType,
) where

import Control.Monad.Combinators.Expr
import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, isJust)
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
  uncurry Name
    <$> match "identifier" (\case TIdent t -> Just t; _ -> Nothing)

-- Statements ---------------------------------------------------------------------

program :: Parser [Statement]
program = P.many (tok TSep) *> P.sepEndBy statement (P.some (tok TSep))

statement :: Parser Statement
statement =
  letStatement
    P.<|> unitStatement
    P.<|> chartStatement
    P.<|> spaceStatement
    P.<|> dataStatement
    P.<|> namespaceStatement
    P.<|> useStatement
    P.<|> signatureStatement
    P.<|> SExpr
    <$> expr

{- | @name :: type@ (design §4.8): a signature for the definition of that
name. The cue is a name followed by @::@, which no expression statement
starts with.
-}
signatureStatement :: Parser Statement
signatureStatement = do
  n <- P.try (name <* tok (TOp "::"))
  SSig n <$> sigType

{- | @namespace a.b@ and an indented block of statements (design §7.6). The
block opens at the first token after the path, as after @where@; it must be
indented further than the line of the @namespace@.
-}
namespaceStatement :: Parser Statement
namespaceStatement = do
  _ <- kw KNamespace
  p <- pathP False
  stmts <- P.sepEndBy statement (P.some (tok TSep))
  o <- P.getOffset
  _ <- tok TBlockEnd
  if null stmts
    then
      P.setOffset o
        >> fail
          ( "namespace "
              <> T.unpack (renderPath p)
              <> " has no statements: indent them under it, or write them on the same line"
          )
    else pure (SNamespace p stmts)

-- | @use a.b@ or @use a.b as k@ (design §7.6). @as@ is not a keyword: it is also attoseconds.
useStatement :: Parser Statement
useStatement = do
  _ <- kw KUse
  p <- pathP True
  alias <-
    P.optional
      (match "as" (\case TIdent "as" -> Just (); _ -> Nothing) *> name)
  pure (SUse p alias)

{- | A dotted path, @orbital.kepler@: a name and the fields glued to it. With
the flag, a leading dot (an absolute name) is allowed and dropped.
-}
pathP :: Bool -> Parser Path
pathP absolute = do
  (s, lead) <-
    match "path" $ \case
      TIdent t -> Just t
      TAbs t | absolute -> Just t
      _ -> Nothing
  rest <- P.many (match "path segment" (\case TField t -> Just t; _ -> Nothing))
  let end = if null rest then s else fst (last rest)
  pure (Path (spanUnion s end) (lead :| map snd rest))

{- | A name that may be qualified, @orbital.Body@, or absolute, @.Body@
(design §7.6), as one 'Name' with the dots in its text.
-}
qualifiedName :: Parser Name
qualifiedName = do
  (s, lead) <-
    match "name" $ \case
      TIdent t -> Just t
      TAbs t -> Just ("." <> t)
      _ -> Nothing
  rest <- P.many (match "name segment" (\case TField t -> Just t; _ -> Nothing))
  let end = if null rest then s else fst (last rest)
  pure (Name (spanUnion s end) (T.intercalate "." (lead : map snd rest)))

-- | @unit name = expr@: a definition that is also a display unit.
unitStatement :: Parser Statement
unitStatement = do
  s <- kw KUnit
  n <- name
  _ <- tok TEquals
  e <- expr
  pure (SLet (Binding (spanUnion s e.span) n [] e Unit))

{- | @chart name params… on parent [at origin] [step unit] [by B [then B
…]] [spinning ω]@ (design §3.10, F10; @scale@ is the old spelling): a
definition whose value is a chart, marked as one. @on@ ends the
parameters and names the parent, a space or a chart; the other clauses
come in any order, each running to the next clause word, so no
expression in them needs parentheses. @step@, @by@ and @spinning@ are
words in this statement only, like @then@ between generators, so they
stay names everywhere else. Parameters make a chart with parameters, a
function to a chart, as they make a function of a @let@. The generators
become a list literal, a single one a list of one; an @if@ inside one
takes its own @then@.
-}
chartStatement :: Parser Statement
chartStatement = do
  s <- kw KChart
  n <- name
  ps <- P.many name
  o <- P.getOffset
  equals <- P.optional (tok TEquals)
  case equals of
    Just _ ->
      P.setOffset o
        >> fail
          "a chart is declared with no `=`: its parent after `on`, then its clauses, as in chart degC on Temperature at 273.15 K"
    Nothing -> pure ()
  _ <-
    kw KOn
      P.<|> fail
        "name its space: `chart … on Temperature`, or the chart it is on, after its parameters"
  input <- P.getInput
  let (stmt, rest) = splitAt (statementEnd input.toks) input.toks
  clauses <- mapM (clause input) (clauseSegments stmt)
  P.setInput input{toks = rest}
  let words' = [w | (Just w, _) <- clauses]
  case [w | (i, w) <- zip [0 :: Int ..] words', w `elem` drop (i + 1) words'] of
    w : _ -> fail ("a chart has one `" <> T.unpack w <> "` clause")
    [] -> pure ()
  parent <- case clauses of
    (Nothing, p) : _ -> pure p
    _ -> fail "a chart names its parent after `on`"
  let find w = lookup (Just w) clauses
      body =
        ChartClauses
          parent
          (find "at")
          (find "step")
          (find "by")
          (find "spinning")
          (not (null ps))
      sp = spanUnion s (foldr (spanUnion . (.span) . snd) parent.span clauses)
  pure (SLet (Binding sp n ps (Expr sp (ChartForm body)) ChartDecl))
 where
  -- One clause, from its tokens: the parent, or a clause word and its expression.
  clause input (word, toks) = do
    P.setInput input{toks = toks}
    case word of
      Nothing -> (Nothing,) <$> expr <* P.eof
      Just "by" -> do
        _ <- P.anySingle
        g <- expr
        gs <- P.many (kw KThen *> expr)
        P.eof
        let sp = foldr (spanUnion . (.span)) g.span gs
        pure (Just "by", Expr sp (List (g : gs)))
      Just w -> do
        _ <- P.anySingle
        (Just w,) <$> expr <* P.eof

{- | The index at which the current statement ends: the first separator or
block end outside brackets.
-}
statementEnd :: [Located Token] -> Int
statementEnd = go (0 :: Int) 0
 where
  go _ i [] = i
  go depth i (t : ts) = case t.value of
    TSep | depth == 0 -> i
    TBlockEnd | depth == 0 -> i
    v
      | v `elem` [TLParen, TLBracket, TLBrace] -> go (depth + 1) (i + 1) ts
      | v `elem` [TRParen, TRBracket, TRBrace] -> go (depth - 1) (i + 1) ts
      | otherwise -> go depth (i + 1) ts

{- | A chart statement's tokens after @on@, cut at its clause words outside
brackets: the parent's, then each clause's, its word first.
-}
clauseSegments :: [Located Token] -> [(Maybe Text, [Located Token])]
clauseSegments = go (0 :: Int) Nothing []
 where
  go _ word acc [] = [(word, reverse acc)]
  go depth word acc (t : ts)
    | depth == 0
    , Just w <- clauseWord t.value =
        (word, reverse acc) : go depth (Just w) [t] ts
    | t.value `elem` [TLParen, TLBracket, TLBrace] =
        go (depth + 1) word (t : acc) ts
    | t.value `elem` [TRParen, TRBracket, TRBrace] =
        go (depth - 1) word (t : acc) ts
    | otherwise = go depth word (t : acc) ts
  clauseWord = \case
    TKw KAt -> Just "at"
    TIdent w | w `elem` ["step", "by", "spinning"] -> Just w
    _ -> Nothing

{- | @space Name = type@ (design §3.10, F2): a nominal space, of the amounts
of a tensor type, @Num K@ or @Vec 3 m@.
-}
spaceStatement :: Parser Statement
spaceStatement = do
  _ <- kw KSpace
  n <- name
  _ <- tok TEquals
  SSpace n <$> typeExpr

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
            sp = foldr (spanUnion . (.span)) (spanUnion s b.span) (fromMaybe [] wh)
        pure (SLet (Binding sp b.name b.params body' Plain))
    ]
 where
  wrapWhere wb acc = Expr (spanUnion wb.span acc.span) (Let wb.name wb.params wb.body acc)

binding :: Parser Binding
binding = do
  n <- name
  ps <- P.many name
  _ <- tok TEquals
  e <- expr
  pure (Binding (spanUnion n.span e.span) n ps e Plain)

whereClause :: Parser [Binding]
whereClause = kw KWhere *> P.sepBy1 binding (tok TSep) <* tok TBlockEnd

{- | @data Name params = Con fields | Con fields@ (design §2.3), optionally
preceded by @structural@. A field is a type atom: a name, or a compound
type in parentheses.
-}
dataStatement :: Parser Statement
dataStatement = do
  structural <-
    P.optional
      (P.try (match "structural" (\case TIdent "structural" -> Just (); _ -> Nothing)))
  s <- kw KData
  n <- name
  ps <- P.many name
  _ <- tok TEquals
  cons <- P.sepBy1 constructor (tok TBar)
  let start = maybe s fst structural
      end = case last cons of
        (c, []) -> c.span
        (_, fs) -> (last fs).ty.span
  pure
    ( SData
        ( DataDecl
            (spanUnion start end)
            n
            ps
            cons
            (isJust structural)
        )
    )
 where
  constructor = (,) <$> name <*> (recordFields P.<|> P.many (FieldDecl Nothing <$> typeAtom))
  -- @C {f :: type, g :: type}@: named fields (§2.3). The cue is @{name ::@,
  -- so @G {Num}@ is a constructor with one list-typed field.
  recordFields = do
    _ <- P.try (tok TLBrace <* P.lookAhead (name *> tok (TOp "::")))
    P.sepBy1 fieldDecl (tok TComma) <* tok TRBrace
  fieldDecl = do
    n <- name
    _ <- tok (TOp "::")
    FieldDecl (Just n) <$> typeExpr

-- Types ---------------------------------------------------------------------------

{- | The type of a signature or an ascription (design §4.8): a type, headed
by @forall@ (or @∀@), its binders and a @.@ when it has variables. A binder
is a name, or a name with the length it stands for, @(a : 3)@.
-}
sigType :: Parser TyExpr
sigType = do
  quantified <- P.optional $ do
    s <- kw KForall
    bs <- P.some binder
    _ <- tok (TOp ".")
    pure (s, bs)
  t <- typeExpr
  pure $ case quantified of
    Nothing -> t
    Just (s, bs) -> TyExpr (spanUnion s t.span) (TyForall bs t)
 where
  binder =
    P.choice
      [ (\n -> TyBinder n Nothing Nothing) <$> name
      , do
          _ <- tok TLParen
          n <- name
          _ <- tok (TOp ":")
          -- A length, @(a : 3)@, or a space, @(c : Temperature)@ (design
          -- §3.10, F1).
          b <-
            P.choice
              [ (\(_, k) -> TyBinder n (Just k) Nothing)
                  <$> match
                    "length"
                    (\case TNum r | denominator r == 1 && r >= 0 -> Just (numerator r); _ -> Nothing)
              , TyBinder n Nothing . Just <$> qualifiedName
              ]
          _ <- tok TRParen
          pure b
      ]

-- | A type: an application, optionally followed by @->@ and another type.
typeExpr :: Parser TyExpr
typeExpr = do
  a <- typeApp
  P.option a $ do
    _ <- tok TArrow
    b <- typeExpr
    pure (TyExpr (spanUnion a.span b.span) (TyFun a b))

-- | A name applied to atoms, or a lone atom.
typeApp :: Parser TyExpr
typeApp =
  P.choice
    [ do
        hd <- qualifiedName
        args <- P.many typeAtom
        pure $ case args of
          [] -> TyExpr hd.span (TyName hd.text)
          _ -> TyExpr (spanUnion hd.span (last args).span) (TyApp hd args)
    , typeAtom
    ]

typeAtom :: Parser TyExpr
typeAtom =
  P.choice
    [ (\n -> TyExpr n.span (TyName n.text)) <$> qualifiedName
    , (\(sp, k) -> TyExpr sp (TyInt k)) <$> integer "length"
    , parenthesised
    , do
        s <- tok TLBrace
        t <- typeExpr
        e <- tok TRBrace
        pure (TyExpr (spanUnion s e) (TyList t))
    , -- Brackets hold a shape only; a dimension is an argument of its own.
      do
        s <- tok TLBracket
        items <- P.sepBy shapeItem (tok TComma)
        e <- tok TRBracket
        pure (TyExpr (spanUnion s e) (TyShape items))
    ]
 where
  shapeItem =
    P.choice
      [ (\n -> TyExpr n.span (TyName n.text)) <$> qualifiedName
      , (\(sp, k) -> TyExpr sp (TyInt k)) <$> integer "length"
      ]

{- | @(…)@: a type in parentheses, a tuple, or a dimension (design §4.1). A
type followed by @*@, @·@, @/@ or a power is the first factor of a
dimension, which goes on as a product, left to right: @m/s*kg@ is
@m·kg/s@. Each later factor is a name, @1@ or a parenthesised group, with
an optional power.
-}
parenthesised :: Parser TyExpr
parenthesised = do
  s <- tok TLParen
  t <- typeExpr
  node <-
    P.choice
      [ TyTuple . (t :) <$> P.some (tok TComma *> typeExpr)
      , TyDim <$> dimensionFrom t
      , pure t.node
      ]
  e <- tok TRParen
  pure (TyExpr (spanUnion s e) node)
 where
  dimensionFrom t =
    P.choice
      [ do
          k <- power
          refuseJuxtaposed t
          rest <- P.many step
          pure (factorsOf k t ++ concat rest)
      , (factorsOf 1 t ++) . concat <$> P.some step
      ]
  step = do
    divides <-
      P.choice
        [ False <$ tok (TOp "*")
        , False <$ tok (TOp "·")
        , True <$ tok (TOp "/")
        , -- Taken and put back, so the refusal stands at the `@`.
          do
            o <- P.getOffset
            _ <- tok (TOp "@")
            P.setOffset o
            fail "`@` is the matrix product; a dimension's product is * or ·"
        ]
    f <-
      P.choice
        [ (\n -> TyExpr n.span (TyName n.text)) <$> qualifiedName
        , (\(sp, k) -> TyExpr sp (TyInt k)) <$> integer "number"
        , parenthesised
        ]
    k <- P.option 1 power
    refuseJuxtaposed f
    pure [(g, if divides then negate e else e) | (g, e) <- factorsOf k f]
  -- A group's power raises each of its factors.
  factorsOf k f = case f.node of
    TyDim fs -> [(g, k * e) | (g, e) <- fs]
    _ -> [(f, k)]
  -- @m s@ is an application, not a product: say how to write one.
  refuseJuxtaposed f = do
    next <- P.optional (P.lookAhead (P.try typeAtom))
    case next of
      Nothing -> pure ()
      Just a -> fail (T.unpack (juxtaposedHint (map spelled [f, a])))
  spelled f = case f.node of
    TyName n -> n
    TyInt k -> T.pack (show k)
    _ -> "…"

-- | A power: @^2@, @^-2@, or a superscript.
power :: Parser Integer
power =
  P.choice
    [ snd <$> match "superscript" (\case TSup k -> Just k; _ -> Nothing)
    , do
        _ <- tok (TOp "^")
        neg <- P.optional (tok (TOp "-"))
        (_, k) <- integer "exponent"
        pure (maybe k (const (negate k)) neg)
    ]

-- | An integer literal.
integer :: String -> Parser (Span, Integer)
integer label =
  match
    label
    (\case TNum r | denominator r == 1 -> Just (numerator r); _ -> Nothing)

-- Expressions ----------------------------------------------------------------------

expr :: Parser Expr
expr = P.choice [lambda, letIn, ifExpr, caseExpr, opExpr]

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

{- | The operators, and last a conversion (design §3.10, F7, F10): @x to
c@, @x from c to c1@, or a subtraction in a frame, @b .- a on c@, none of
which chain.
-}
opExpr :: Parser Expr
opExpr = do
  x <- inner
  P.option x
    $ P.choice
      [ binop To x <$> (kw KTo *> inner)
      , binop On x <$> (kw KOn *> inner)
      , do
          _ <- kw KFrom
          c <- inner
          _ <- kw KTo
          c1 <- inner
          pure (Expr (spanUnion x.span c1.span) (FromTo x c c1))
      ]
 where
  inner = makeExprParser term table
  table =
    [ [InfixR (binop Compose <$ opTok "."), InfixL backtick]
    , [Prefix (foldr1 (.) <$> P.some (negP P.<|> sqrtP))]
    ,
      [ InfixL (binop Outer <$ opTok "*")
      , InfixL (binop Dot <$ (opTok "@" P.<|> opTok "·"))
      , InfixN (binop Cross <$ opTok "×")
      , InfixL (binop Wedge <$ opTok "/\\")
      , InfixL (binop EMul <$ opTok ".*")
      , InfixL (binop EDiv <$ opTok "./")
      , InfixL (binop Div <$ opTok "/")
      ]
    ,
      [ InfixL (binop Add <$ opTok "+")
      , InfixL (binop Sub <$ opTok "-")
      , InfixL (binop PAdd <$ opTok ".+")
      , InfixL (binop PSub <$ opTok ".-")
      ]
    , [InfixN plusMinus]
    , [Postfix labelP]
    , [InfixR (binop Cons <$ opTok ":")]
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
  labelP = do
    (sp, l) <- match "#label" (\case THashLabel l -> Just l; _ -> Nothing)
    pure (\e -> Expr (spanUnion e.span sp) (Labelled l e))

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
is a number or vector literal. A literal next to another literal is an
error:  4 3@ is not a product, write  * 4 * 3@.
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
    pure (foldl (binop Scale) hd units)
  unitAtom = do
    o <- P.getOffset
    a <- atom
    case a.node of
      Num _ ->
        P.setOffset o
          >> fail "a number next to a number: write the multiplication, 5 * 4"
      Vec _ ->
        P.setOffset o
          >> fail "a literal next to a vector literal: write the multiplication, 2 * [1, 2]"
      _ -> withPower a

{- | A primary expression with any glued projections.
| A primary expression with its glued projections, field accesses and record braces.
-}
atom :: Parser Expr
atom = primary >>= postfixes
 where
  postfixes acc =
    P.choice
      [ match "projection" (\case TProj i -> Just i; _ -> Nothing)
          >>= \(sp, i) -> postfixes (Expr (spanUnion acc.span sp) (Proj acc i))
      , slice acc >>= postfixes
      , match "field" (\case TField f -> Just f; _ -> Nothing)
          >>= \(sp, f) -> postfixes (Expr (spanUnion acc.span sp) (FieldOf acc f))
      , recordBraces acc >>= postfixes
      , pure acc
      ]
  -- @e._.i@ (§2.10): each wildcard skips an axis, and a position must follow.
  slice acc = do
    wilds <- P.some (match "wildcard" (\case TWild -> Just (); _ -> Nothing))
    P.choice
      [ (\(sp, i) -> Expr (spanUnion acc.span sp) (Slice acc (length wilds) i))
          <$> match "projection" (\case TProj i -> Just i; _ -> Nothing)
      , fail
          "a wildcard ._ skips an axis and must be followed by a position, as in m._.0 for column 0"
      ]
  -- @{f = e, …}@ after an expression: a record construction or update (§2.3).
  -- A list literal also starts with a brace, so look for @name =@ first.
  recordBraces acc = do
    _ <- P.try (tok TLBrace <* P.lookAhead (name *> tok TEquals))
    fields <- P.sepBy1 ((,) <$> name <* tok TEquals <*> expr) (tok TComma)
    e <- tok TRBrace
    pure (Expr (spanUnion acc.span e) (Record acc fields))

primary :: Parser Expr
primary =
  P.choice
    [ (\(sp, r) -> Expr sp (Num r))
        <$> match "number" (\case TNum r -> Just r; _ -> Nothing)
    , (\sp -> Expr sp (Bool True)) <$> kw KTrue
    , (\sp -> Expr sp (Bool False)) <$> kw KFalse
    , (\n -> Expr n.span (Var n.text)) <$> name
    , -- An absolute name, @.km@ (design §7.6): the root's, whatever the scope.
      (\(sp, n) -> Expr sp (Var ("." <> n)))
        <$> match "absolute name" (\case TAbs n -> Just n; _ -> Nothing)
    , parens
    , vecOrMat
    , listLit
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
          , -- An ascription (design §4.8): @(e :: type)@.
            do
              _ <- tok (TOp "::")
              t <- sigType
              e2 <- tok TRParen
              pure (Expr (spanUnion s e2) (Ascribe e t))
          , -- A tuple: two or more components (§2.3).
            do
              rest <- P.some (tok TComma *> expr)
              e2 <- tok TRParen
              pure (Expr (spanUnion s e2) (Tuple (e : rest)))
          ]
    ]

-- | @{a, b, c}@ or @{}@: a list literal (§2.3).
listLit :: Parser Expr
listLit = do
  s <- tok TLBrace
  es <- P.sepBy expr (tok TComma)
  e <- tok TRBrace
  pure (Expr (spanUnion s e) (List es))

-- | @case e of alts@: the alternatives are a layout block, as after @where@.
caseExpr :: Parser Expr
caseExpr = do
  s <- kw KCase
  scrut <- expr
  _ <- kw KOf
  alts <- P.sepBy1 alternative (P.some (tok TSep))
  _ <- P.optional (tok TSep)
  _ <- tok TBlockEnd
  let end = case alts of
        [] -> scrut.span
        _ -> (snd (last alts)).span
  pure (Expr (spanUnion s end) (CaseOf scrut alts))
 where
  alternative = do
    p <- patternP
    _ <- tok TArrow
    body <- expr
    pure (p, body)

-- | One constructor deep: a tuple of names, @{}@, @x : xs@, a boolean, @_@ or a name.
patternP :: Parser Pattern
patternP =
  P.choice
    [ do
        s <- tok TLParen
        ns <- P.sepBy1 name (tok TComma)
        e <- tok TRParen
        pure (Pattern (spanUnion s e) (PCon "Tuple" ns))
    , do
        s <- tok TLBrace
        e <- tok TRBrace
        pure (Pattern (spanUnion s e) (PCon "Nil" []))
    , (\sp -> Pattern sp (PCon "True" [])) <$> kw KTrue
    , (\sp -> Pattern sp (PCon "False" [])) <$> kw KFalse
    , -- A qualified or absolute constructor (design §7.6), with its fields.
      do
        c <-
          P.try
            ( qualifiedName >>= \n ->
                if T.any (== '.') n.text then pure n else fail "a qualified constructor"
            )
        fields <- P.many name
        pure
          ( Pattern
              (if null fields then c.span else spanUnion c.span (last fields).span)
              (PCon c.text fields)
          )
    , do
        x <- name
        P.choice
          [ do
              _ <- tok (TOp ":")
              xs <- name
              pure (Pattern (spanUnion x.span xs.span) (PCon "Cons" [x, xs]))
          , -- A declared constructor with its fields; a lone name is a
            -- variable here and becomes a nullary constructor pattern when
            -- it names one (Eval.Desugar).
            do
              fields <- P.some name
              pure (Pattern (spanUnion x.span (last fields).span) (PCon x.text fields))
          , pure (Pattern x.span (if x.text == "_" then PWild else PVar x))
          ]
    ]

sectionOp :: Bool -> Parser Op
sectionOp allowMinus =
  P.choice
    $ [ Outer <$ tok (TOp "*")
      , Dot <$ (tok (TOp "@") P.<|> tok (TOp "·"))
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
      , PAdd <$ tok (TOp ".+")
      , PSub <$ tok (TOp ".-")
      , Cons <$ tok (TOp ":")
      , To <$ kw KTo
      , PlusMinus <$> plusMinusKind
      , Infix . (.text) <$> (tok TBacktick *> name <* tok TBacktick)
      ]
      ++ [Sub <$ tok (TOp "-") | allowMinus]
 where
  plusMinusKind :: Parser NudgeKind
  plusMinusKind = snd <$> match "±" (\case TPlusMinus k -> Just k; _ -> Nothing)

{- | A bracket literal (§2.4). Commas separate elements, @;@ separates rows,
@;;@ separates planes, and so on: @[1, 2; 3, 4]@ is @[[1, 2], [3, 4]]@. The
rank is one more than the highest separator used, and a level that never
appears is a length-one axis, so @[1; 2]@ is a 2×1 matrix. Nested brackets
are still vectors of vectors; a ragged nesting is a shape error found by the
type checker.
-}
vecOrMat :: Parser Expr
vecOrMat = do
  s <- tok TLBracket
  items <- P.optional $ do
    x0 <- expr
    rest <- P.many ((,) <$> separator <*> expr)
    pure (x0 : map snd rest, map fst rest)
  e <- tok TRBracket
  pure $ Expr (spanUnion s e) $ case items of
    Nothing -> Vec []
    Just (es, seps) -> Vec (splitLevel (maximum (0 : seps)) es seps)
 where
  separator =
    P.choice
      [ 0 <$ tok TComma
      , 1 <$ tok TSep
      , snd <$> match "row separator" (\case TSemis n -> Just n; _ -> Nothing)
      ]
  -- The elements of the literal at a level: at level 0 the expressions
  -- themselves, above that one nested literal per group between separators
  -- of that level.
  splitLevel :: Int -> [Expr] -> [Int] -> [Expr]
  splitLevel 0 es _ = es
  splitLevel k es seps = [nested (splitLevel (k - 1) g gs) | (g, gs) <- groups k es seps]
  nested xs = Expr (foldr1 spanUnion (map (.span) xs)) (Vec xs)
  groups :: Int -> [Expr] -> [Int] -> [([Expr], [Int])]
  groups k es seps = case es of
    [] -> []
    e0 : rest -> go [e0] [] rest seps
   where
    go acc accS (x : xs) (s : ss)
      | s == k = (reverse acc, reverse accS) : go [x] [] xs ss
      | otherwise = go (x : acc) (s : accS) xs ss
    go acc accS _ _ = [(reverse acc, reverse accS)]

-- | A type on its own, for tests and the driver.
parseType :: Text -> Either Text TyExpr
parseType src = do
  toks <- tokenize src
  runP (P.many (tok TSep) *> sigType <* P.many (tok TSep)) src toks
