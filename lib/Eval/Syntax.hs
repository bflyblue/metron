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
  Pattern (..),
  PatNode (..),
  BindKind (..),
  Statement (..),
  TyExpr (..),
  TyNode (..),
  DataDecl (..),
  FieldDecl (..),
  Decl (..),
  declOf,
  renderSpanError,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core (NudgeKind)
import GHC.Records (HasField (..))

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
  | -- | @.+@: a point plus an amount (§3.6)
    PAdd
  | -- | @.-@: the amount from one point to another (§3.6)
    PSub
  | -- | @:@: prepend to a list
    Cons
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
  | {- | @e._.i@, @e._._.i@: a slice along axis @k@ (the number of
    wildcards, at least one) at the literal position @i@ (§2.10).
    -}
    Slice Expr Int Int
  | -- | @e.name@: a record field (§2.10)
    FieldOf Expr Text
  | -- | @C {f = e, …}@ builds a record when @C@ is a constructor; @e {f = e'}@ updates one
    Record Expr [(Name, Expr)]
  | -- | @(a, b, …)@: two or more components (§2.3)
    Tuple [Expr]
  | -- | @{a, b, c}@: a list literal
    List [Expr]
  | -- | @case e of alternatives@
    CaseOf Expr [(Pattern, Expr)]
  deriving stock (Eq, Show)

-- | A pattern of a case alternative: one constructor deep (§2.3).
data Pattern = Pattern {span :: Span, node :: PatNode}
  deriving stock (Eq, Show)

data PatNode
  = -- | a constructor with variables for its fields: @(a, b)@, @x : xs@, @{}@, @true@
    PCon Text [Name]
  | -- | @_@: every constructor not listed
    PWild
  | -- | a variable: every constructor not listed, with the scrutinee bound
    PVar Name
  deriving stock (Eq, Show)

{- | A top-level or @where@ binding: @name params = body@. A binding declared
with @unit@ instead of @let@ is a display unit (design §3.2.12): the
codebase remembers that about the name, and values computed from it print
in terms of it.
-}

-- | What a top-level definition declares besides a value (design §3.2.12, §3.6).
data BindKind = Plain | Unit | ScaleDecl
  deriving stock (Eq, Show)

data Binding = Binding
  {span :: Span, name :: Name, params :: [Name], body :: Expr, kind :: BindKind}
  deriving stock (Eq, Show)

{- | A type as written in a @data@ declaration (design §2.3). The sorts
(types, lengths, shapes, dimensions) are told apart by position when the
declaration is entered; here a bracket is just a bracket.
-}
data TyExpr = TyExpr {span :: Span, node :: TyNode}
  deriving stock (Eq, Show)

data TyNode
  = -- | a type name, a parameter, or a dimension name inside brackets
    TyName Text
  | -- | a length literal
    TyInt Integer
  | -- | a type name applied to arguments: @Num [m]@, @Vec 3 [m]@, @Maybe a@
    TyApp Name [TyExpr]
  | -- | @(a, b, …)@: two or more components
    TyTuple [TyExpr]
  | -- | @{a}@: a list
    TyList TyExpr
  | TyFun TyExpr TyExpr
  | {- | @[…]@: comma-separated items, each a product of powered factors.
    @[2, 3]@ is a shape, @[kg m^2 s^-2]@ a dimension; @[m / s]@ divides.
    -}
    TyBracket [[(TyExpr, Integer)]]
  deriving stock (Eq, Show)

{- | @data Name params = Con fields | …@ (design §2.3). A @structural@
declaration takes its identity from its structure alone; otherwise the
type name is stamped into it.
-}
data DataDecl = DataDecl
  { span :: Span
  , name :: Name
  , params :: [Name]
  , constructors :: [(Name, [FieldDecl])]
  , structural :: Bool
  }
  deriving stock (Eq, Show)

-- | A constructor field: its type, and its name when the constructor is a record.
data FieldDecl = FieldDecl {label :: Maybe Name, ty :: TyExpr}
  deriving stock (Eq, Show)

-- | What the scratch holds: a definition or a data declaration.
data Decl = DBind Binding | DData DataDecl
  deriving stock (Eq, Show)

instance HasField "name" Decl Name where
  getField = \case
    DBind b -> b.name
    DData d -> d.name

instance HasField "span" Decl Span where
  getField = \case
    DBind b -> b.span
    DData d -> d.span
data Statement
  = SLet Binding
  | SData DataDecl
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

-- | The declaration a statement makes, if it is one.
declOf :: Statement -> Maybe Decl
declOf = \case
  SLet b -> Just (DBind b)
  SData d -> Just (DData d)
  SExpr _ -> Nothing
