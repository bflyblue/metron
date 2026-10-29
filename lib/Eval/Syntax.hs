{- | The surface AST (design §2): a faithful tree of what the user typed,
with source spans on every node. Sugar lives here and is removed by
"Eval.Desugar".
-}
module Eval.Syntax (
  Pos (..),
  Span (..),
  spanUnion,
  Name (..),
  Op (..),
  Expr (..),
  Node (..),
  Binding (..),
  Statement (..),
  renderSpanError,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core (NudgeKind)

-- | A 1-based line and column.
data Pos = Pos {line :: !Int, col :: !Int}
  deriving stock (Eq, Ord, Show)

{- | A half-open source range: @from@ is the first character, @to@ is the
position just after the last one.
-}
data Span = Span {from :: !Pos, to :: !Pos}
  deriving stock (Eq, Ord, Show)

spanUnion :: Span -> Span -> Span
spanUnion a b = Span (min a.from b.from) (max a.to b.to)

-- | A binder or reference with the span of the identifier itself.
data Name = Name {span :: Span, text :: Text}
  deriving stock (Eq, Show)

{- | Binary operators as written. Overloading and primitive names are the
desugarer's business.
-}
data Op
  = Add
  | Sub
  | -- | @*@, @⊗@: tensor product, including scalar scaling
    Outer
  | -- | juxtaposition, @5 km@: a literal times a unit expression (§2.6); the desugarer checks the unit
    Scale
  | -- | @·@, @@@: contracting product
    Dot
  | -- | @×@, @><@: the 3D cross product, a prelude definition
    Cross
  | -- | @∧@, @/\@: the wedge (exterior) product
    Wedge
  | -- | @⊙@, @.*@: elementwise product
    EMul
  | -- | @⊘@, @./@: elementwise division
    EDiv
  | -- | @/@: division by a scalar
    Div
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | And
  | Or
  | -- | @±@ (bound) or @±σ@ (statistical)
    PlusMinus NudgeKind
  | To
  | Compose
  | -- | a backticked name used infix
    Infix Text
  deriving stock (Eq, Show)

data Expr = Expr {span :: Span, node :: Node}
  deriving stock (Eq, Show)

data Node
  = Num Rational
  | Bool Bool
  | Var Text
  | Lam [Name] Expr
  | App Expr Expr
  | -- | @let f x y = e in body@; parameters are sugar for a lambda.
    Let Name [Name] Expr Expr
  | If Expr Expr Expr
  | BinOp Op Expr Expr
  | Neg Expr
  | -- | @e ^ n@ or a glued superscript; the exponent is always a literal.
    Pow Expr Integer
  | -- | @(op e)@, meaning @\x -> x op e@.
    SectionL Op Expr
  | -- | @(e op)@, meaning @\x -> e op x@.
    SectionR Expr Op
  | -- | @e #label@: a global identity for the measurement @e@ declares (§3.2.4).
    Labelled Text Expr
  | -- | A bracket literal; nesting gives higher ranks.
    Vec [Expr]
  | -- | @e.i@ with a literal position.
    Proj Expr Int
  deriving stock (Eq, Show)

{- | A top-level or @where@ binding: @name params = body@. A binding declared
with @unit@ instead of @let@ is a display unit (design §3.2.12): the
codebase remembers that about the name, and values computed from it print
in terms of it.
-}
data Binding = Binding
  {span :: Span, name :: Name, params :: [Name], body :: Expr, isUnit :: Bool}
  deriving stock (Eq, Show)

data Statement
  = SLet Binding
  | SExpr Expr
  deriving stock (Eq, Show)

{- | An error message pointing at a span, with the source line and carets
underneath (design §4.7). Without the source, just the position.
-}
renderSpanError :: Maybe Text -> Span -> Text -> Text
renderSpanError src sp msg =
  case src >>= \s -> lineAt s sp.from.line of
    Nothing -> pos <> ": " <> msg
    Just lineText ->
      let width
            | sp.to.line == sp.from.line = max 1 (sp.to.col - sp.from.col)
            | otherwise = max 1 (T.length lineText - sp.from.col + 1)
       in T.intercalate
            "\n"
            [ "error at " <> pos
            , "  " <> lineText
            , "  " <> T.replicate (sp.from.col - 1) " " <> T.replicate width "^"
            , "  " <> msg
            ]
 where
  pos = T.pack (show sp.from.line) <> ":" <> T.pack (show sp.from.col)
  lineAt s n = case drop (n - 1) (T.lines s) of
    l : _ -> Just l
    [] -> Nothing
