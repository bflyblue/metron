{- | The fixity table ("Metron.Fixity"): every binary operator the printer
writes reads back, through the parser and the desugarer, as the term it
was printed from, alone and nested in any other, in both spellings.
-}
module Operators (operatorTests) where

import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Text qualified as T
import Metron.Core
import Metron.Desugar (desugarClosed, noResolver, renderDesugarError)
import Metron.Dimension (Spelling (..))
import Metron.Fixity (Fixity (..), binaryOperators)
import Metron.Parser (parseExpr)
import Metron.Pretty (renderTermIn)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

operatorTests :: TestTree
operatorTests =
  localOption (mkTimeout 60_000_000)
    $ testGroup
      "fixity"
      [ testCase "every pair of operators, nested either way, reads back" $ do
          let failures =
                [ (spelling, printed, back)
                | spelling <- [Ascii, Unicode]
                , f <- readable
                , g <- readable
                , t <-
                    [ abc (op f (op g v2 v1) v0)
                    , abc (op f v2 (op g v1 v0))
                    ]
                , let (printed, back) = roundTrip spelling t
                , back /= Right (show t)
                ]
          failures @?= []
      , testProperty "operator trees read back" $ forAll (genTree 4) $ \body ->
          let t = abc body
           in conjoin
                [ counterexample (T.unpack printed) (back === Right (show t))
                | spelling <- [Ascii, Unicode]
                , let (printed, back) = roundTrip spelling t
                ]
      ]

-- | The operators the parser reads, as opposed to @to@, which it reads as a keyword.
readable :: [Fixity]
readable = [f | f <- binaryOperators, not (null f.tokens)]

op :: Fixity -> Term n -> Term n -> Term n
op f a b = PrimApp f.primitive [a, b]

abc :: Term (S (S (S Z))) -> Term Z
abc = Lam "a" . Lam "b" . Lam "c"

v0, v1, v2 :: Term (S (S (S Z)))
v0 = Var FZ
v1 = Var (FS FZ)
v2 = Var (FS (FS FZ))

-- | A tree of operators over the three variables.
genTree :: Int -> Gen (Term (S (S (S Z))))
genTree depth
  | depth <= 0 = elements [v0, v1, v2]
  | otherwise =
      frequency
        [ (1, elements [v0, v1, v2])
        , (3, op <$> elements readable <*> genTree (depth - 1) <*> genTree (depth - 1))
        ]

-- | A term printed in a spelling, and what parsing and desugaring that gives back.
roundTrip :: Spelling -> Term Z -> (Text, Either Text String)
roundTrip spelling t = (printed, show . fst <$> back)
 where
  printed = renderTermIn spelling (\_ _ w -> w) VNil t
  back = parseExpr printed >>= first renderDesugarError . desugarClosed noResolver
