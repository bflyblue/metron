{- | The warnings an evaluation makes along the way (design §8.2): a
comparison the double backend's copies disagree about. A warning is kept
as data, not text, until the value is shown: the double backend's
parallel batches each see only their own copies, so each records what its
copies said, and only the batches' records together give the count over
all the copies.
-}
module Metron.Remark (
  Site (..),
  Cause (..),
  Split (..),
  Remarks,
  noted,
  Warning (..),
  warnings,
) where

import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet (singleton, size, union)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (elems, insertWith, unionWith)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Metron.Core (Hash)

{- | Where a node sits: the enclosing top-level definition and the path of
child indices down to it, innermost first. Declared uncertainty takes its
identity from here (design §3.2.4), and a comparison's warning its
place. Erased type nodes do not count, so the path is the Core path and
survives re-elaboration.
-}
data Site = Site {definition :: Hash, path :: [Int]}
  deriving stock (Eq, Ord, Show)

{- | What a comparison's copies spread by: rounding alone, or draws of a
declared σ as well. Draws win when both meet.
-}
data Cause = Rounding | Draws
  deriving stock (Eq, Ord, Show)

instance Semigroup Cause where
  (<>) = max

{- | How a comparison's copies split, as one evaluation sees it: the
relation and its operands' IEEE values, the IEEE result (which alone
decides the branch), what the copies spread by, how many of this
evaluation's copies the condition held for, of how many, and how many
copies there are in all, over every batch.
-}
data Split = Split
  { relation :: !Text
  , left :: !Double
  , right :: !Double
  , result :: !Bool
  , cause :: !Cause
  , held :: !Int
  , copies :: !Int
  , samples :: !Int
  }
  deriving stock (Eq, Show)

{- | A comparison by its place in the term and its operands' bits: a
comparison in a loop is a warning for each set of operands it meets, and
two comparisons with the same operands are two.
-}
data Key = Key
  { site :: !Site
  , relation :: !Text
  , left :: !Word64
  , right :: !Word64
  }
  deriving stock (Eq, Ord, Show)

{- | One comparison's record: the first time any of its copies disagreed
with the IEEE result, each such time (the comparison's number in the
evaluation, the same in every batch), how many copies disagreed in all,
and what they spread by. A batch whose copies all agree records nothing,
so a time is counted once with all the copies whichever batches disagreed
at it. The split is the first one seen, for what every one shares: the
relation, the operands, the result and the number of copies in all.
-}
data Tally = Tally
  { first :: !Int
  , times :: !IntSet
  , differing :: !Int
  , cause :: !Cause
  , split :: !Split
  }

-- | Two records of one comparison: in two batches, or at two times.
instance Semigroup Tally where
  a <> b =
    Tally
      { first = min a.first b.first
      , times = IntSet.union a.times b.times
      , differing = a.differing + b.differing
      , cause = a.cause <> b.cause
      , split = a.split
      }

{- | An evaluation's warnings, or several batches' together: '<>' combines
the records of each comparison.
-}
newtype Remarks = Remarks (Map Key Tally)

instance Semigroup Remarks where
  Remarks a <> Remarks b = Remarks (Map.unionWith (<>) a b)

instance Monoid Remarks where
  mempty = Remarks mempty

{- | Note a comparison made at a site, the given number in its evaluation:
kept when any of its copies disagrees with the IEEE result.
-}
noted :: Int -> Site -> Split -> Remarks -> Remarks
noted time site sp rs@(Remarks m)
  | d == 0 = rs
  | otherwise =
      Remarks
        ( Map.insertWith
            (<>)
            Key
              { site
              , relation = sp.relation
              , left = castDoubleToWord64 sp.left
              , right = castDoubleToWord64 sp.right
              }
            Tally
              { first = time
              , times = IntSet.singleton time
              , differing = d
              , cause = sp.cause
              , split = sp
              }
            m
        )
 where
  d = if sp.result then sp.copies - sp.held else sp.held

{- | A comparison the copies disagree about, over all of them: the relation
and its operands, what the copies spread by, and how many copies the
condition held for, of how many.
-}
data Warning = Warning
  { relation :: Text
  , left :: Double
  , right :: Double
  , cause :: Cause
  , held :: Int
  , copies :: Int
  }
  deriving stock (Eq, Show)

{- | The warnings, in the order one evaluation first made them. A time some
batch did not record, its copies all held what the IEEE result says.
-}
warnings :: Remarks -> [Warning]
warnings (Remarks m) = map snd (sortOn fst (map warning (Map.elems m)))
 where
  warning t =
    let sp = t.split
        total = IntSet.size t.times * sp.samples
     in ( t.first
        , Warning
            { relation = sp.relation
            , left = sp.left
            , right = sp.right
            , cause = t.cause
            , held = if sp.result then total - t.differing else t.differing
            , copies = total
            }
        )
