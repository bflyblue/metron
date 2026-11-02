{- | The binary operators that are primitives (design §2.5): how the parser
reads each, the primitive the desugarer makes of it, and how the printer
writes it back, in one table, so that printed source parses to the term
it was printed from.

The operators that are not one primitive are not here: the cross product
@×@ (a library function), @:@ (a
constructor), composition, juxtaposition, backticks, and @on@ and @from …
to@ (conversions the desugarer builds). The parser and the printer treat
each of those by hand.
-}
module Metron.Fixity (
  Assoc (..),
  Fixity (..),
  binaryOperators,
  fixityOfOp,
  fixityOfPrim,
  operatorsAt,
) where

import Data.List (find)
import Data.Map.Strict qualified as Map (Map, fromList, lookup)
import Data.Text (Text)
import Metron.Syntax (Op (..))

-- | How operators of one level group: to the left, to the right, or not at all.
data Assoc = L | R | N
  deriving stock (Eq, Show)

{- | A binary operator: the surface operator, the primitive it means, the
tokens the parser takes for it (after the lexer has folded unicode
spellings into ASCII ones), the symbol the printer writes in each
spelling, its precedence level on the printer's scale (higher binds
tighter; design §2.5 maps it to the parser's ladder) and its associativity.
-}
data Fixity = Fixity
  { op :: Op
  , primitive :: Text
  , tokens :: [Text]
  , ascii :: Text
  , unicode :: Text
  , level :: Int
  , assoc :: Assoc
  }
  deriving stock (Show)

{- | Every binary primitive operator, by level, tightest first. A
conversion's @to@ has no tokens: the parser reads it after the operators,
as a keyword, and @toChart@ and @toAxes@, which only the types choose,
print as the same @to@.
-}
binaryOperators :: [Fixity]
binaryOperators =
  concatMap
    ( \(level, assoc, ops) ->
        [ Fixity{op, primitive, tokens, ascii, unicode, level, assoc}
        | (op, primitive, tokens, ascii, unicode) <- ops
        ]
    )
    [
      ( 7
      , L
      ,
        [ (Outer, "outer", ["*"], "*", "*")
        , (Dot, "dot", ["@", "·"], "·", "·")
        , (Wedge, "wedge", ["/\\"], "∧", "∧")
        , (EMul, "emul", [".*"], "⊙", "⊙")
        , (EDiv, "ediv", ["./"], "⊘", "⊘")
        , (Div, "div", ["/"], "/", "/")
        ]
      )
    ,
      ( 6
      , L
      ,
        [ (Add, "add", ["+"], "+", "+")
        , (Sub, "sub", ["-"], "-", "-")
        , -- A point and an amount (design §3.6): `.+` and `.-` are the
          -- primitives always, so they read back as they are written.
          (PAdd, "pointAdd", [".+"], ".+", ".+")
        , (PSub, "pointSub", [".-"], ".-", ".-")
        ]
      )
    ,
      ( 4
      , N
      ,
        [ (Eq, "eq", ["=="], "==", "==")
        , (Ne, "ne", ["/="], "/=", "≠")
        , (Le, "le", ["<="], "<=", "≤")
        , (Ge, "ge", [">="], ">=", "≥")
        , (Lt, "lt", ["<"], "<", "<")
        , (Gt, "gt", [">"], ">", ">")
        ]
      )
    , (3, R, [(And, "and", ["&&"], "&&", "&&")])
    , (2, R, [(Or, "or", ["||"], "||", "∨")])
    ,
      ( 1
      , L
      ,
        [ -- An amount to a unit, a point or an amount to a chart (design
          -- §3.10, F5, F10). Conversions chain from the left (design §2.5):
          -- `x to a to b` is `(x to a) to b`.
          (To, "to", [], "to", "to")
        , (To, "toChart", [], "to", "to")
        , (To, "toAxes", [], "to", "to")
        ]
      )
    ]

-- | The operators the parser reads at a level, in table order.
operatorsAt :: Int -> [Fixity]
operatorsAt l = [f | f <- binaryOperators, f.level == l, not (null f.tokens)]

-- | The operator a primitive prints as, if it is one.
fixityOfPrim :: Text -> Maybe Fixity
fixityOfPrim p = Map.lookup p byPrimitive

byPrimitive :: Map.Map Text Fixity
byPrimitive = Map.fromList [(f.primitive, f) | f <- binaryOperators]

-- | A surface operator's entry, if it is a primitive: its first.
fixityOfOp :: Op -> Maybe Fixity
fixityOfOp o = find (\f -> f.op == o) binaryOperators
