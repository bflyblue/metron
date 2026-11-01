{- | What an evaluation notes along the way (design §8.2, "Branches under
copies"): each time it reaches a branch point, an @if@ or a @case@, whose
scrutinee carries the double backend's copies, how those copies' own
scrutinees choose among its alternatives.

A note is data, not text, until the value is shown: the parallel batches
each see only their own copies, so each records what its copies said, and
only the batches' records together give the table over all the copies.
Every count here is a sum over copies, and a copy's path is the same in
whichever batch carries it, so the merged tables are the same for every
@cores@.
-}
module Metron.Remark (
  Site (..),
  Cause (..),
  Reach (..),
  Pending,
  pend,
  Remarks,
  remarksOf,
  Table (..),
  tables,
) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Vector.Unboxed qualified as VU
import Metron.Core (Hash)

{- | Where a node sits: the enclosing top-level definition and the path of
child indices down to it, innermost first. Declared uncertainty takes its
identity from here (design §3.2.4), and a branch point its table. Erased
type nodes do not count, so the path is the Core path and survives
re-elaboration.
-}
data Site = Site {definition :: Hash, path :: [Int]}
  deriving stock (Eq, Ord, Show)

{- | What a scrutinee's copies spread by: rounding alone, or draws of a
declared σ as well. Draws win when both meet.
-}
data Cause = Rounding | Draws
  deriving stock (Eq, Ord, Show)

instance Semigroup Cause where
  (<>) = max

{- | One time an evaluation reached a branch point with copies, as one
batch sees it.
-}
data Reach = Reach
  { order :: (Int, Int)
  {- ^ where in the evaluation's order: the branch points the nominal path
  reached before it, the same in every batch, and 0 on the nominal path
  itself or 1 off it
  -}
  , nominal :: Maybe Int
  {- ^ the alternative the nominal value selects, when the evaluation is
  on the nominal path
  -}
  , cause :: Cause
  , rows :: IntMap Int
  -- ^ copies, by the alternative their own scrutinee selects
  , departed :: Int
  -- ^ of those, copies already off their own path, left behind by rounding
  , split :: Bool
  -- ^ whether the copies split here, each group down its own alternative
  , counted :: Maybe (Int, VU.Vector Int)
  {- ^ the copies counted, by global number, under a key for that set of
  them; 'Nothing' when all the batch's were. The set is read only the
  first time its key is
  -}
  }

{- | One batch's record of a branch point, reach by reach. A copy's number
of reaches is kept only where not every copy was there, so that a table
can say how many times the point was reached.
-}
data Pending = Pending
  { first :: (Int, Int)
  , rows :: IntMap Int
  , taken :: IntMap Int
  , departed :: Int
  , differing :: Int
  , cause :: Cause
  , split :: Bool
  , full :: Int
  , partial :: IntMap (VU.Vector Int, Int)
  }

-- | Add a reach to a batch's records.
pend :: Site -> Reach -> Map Site Pending -> Map Site Pending
pend site r = Map.insertWith after site this
 where
  after new old =
    Pending
      { first = min old.first new.first
      , rows = IntMap.unionWith (+) old.rows new.rows
      , taken = IntMap.unionWith (+) old.taken new.taken
      , departed = old.departed + new.departed
      , differing = old.differing + new.differing
      , cause = old.cause <> new.cause
      , split = old.split || new.split
      , full = old.full + new.full
      , partial =
          IntMap.unionWith (\(_, j) (cs, k) -> (cs, j + k)) new.partial old.partial
      }
  total = sum (IntMap.elems r.rows)
  this =
    Pending
      { first = r.order
      , rows = r.rows
      , taken = maybe IntMap.empty (`IntMap.singleton` 1) r.nominal
      , departed = r.departed
      , differing = case r.nominal of
          Just a -> total - IntMap.findWithDefault 0 a r.rows
          Nothing -> total - maximum (0 : IntMap.elems r.rows)
      , cause = r.cause
      , split = r.split
      , full = maybe 1 (const 0) r.counted
      , partial =
          maybe IntMap.empty (\(key, cs) -> IntMap.singleton key (cs, 1)) r.counted
      }

{- | Branch points as one or more batches recorded them: '<>' combines the
batches' records of each point.
-}
newtype Remarks = Remarks (Map Site Tally)

{- | A branch point over one or more batches. Its evaluations are the most
times any one copy reached it, which every batch counts alike for its own
copies; the rest are sums.
-}
data Tally = Tally
  { first :: (Int, Int)
  , rows :: IntMap Int
  , taken :: IntMap Int
  , departed :: Int
  , differing :: Int
  , cause :: Cause
  , split :: Bool
  , evaluations :: Int
  }

instance Semigroup Remarks where
  Remarks a <> Remarks b = Remarks (Map.unionWith merge a b)
   where
    merge x y =
      Tally
        { first = min x.first y.first
        , rows = IntMap.unionWith (+) x.rows y.rows
        , taken = IntMap.unionWith max x.taken y.taken
        , departed = x.departed + y.departed
        , differing = x.differing + y.differing
        , cause = x.cause <> y.cause
        , split = x.split || y.split
        , evaluations = max x.evaluations y.evaluations
        }

instance Monoid Remarks where
  mempty = Remarks mempty

-- | A batch's records, done.
remarksOf :: Map Site Pending -> Remarks
remarksOf = Remarks . Map.map done
 where
  done p =
    Tally
      { first = p.first
      , rows = p.rows
      , taken = p.taken
      , departed = p.departed
      , differing = p.differing
      , cause = p.cause
      , split = p.split
      , evaluations = p.full + maximum (0 : IntMap.elems (perCopy p.partial))
      }
  -- How many times each copy was counted, over the sets of copies.
  perCopy =
    IntMap.foldl'
      (\acc (cs, k) -> VU.foldl' (\m c -> IntMap.insertWith (+) c k m) acc cs)
      IntMap.empty

{- | A branch point some copies would leave by another alternative, over
all the copies: what its table says.
-}
data Table = Table
  { site :: Site
  , rows :: IntMap Int
  -- ^ copies by the alternative their own scrutinee selects; an absent one is 0
  , taken :: IntMap Int
  -- ^ how many evaluations on the nominal path took each alternative
  , evaluations :: Int
  , counted :: Int
  -- ^ the copies counted, over every evaluation
  , departed :: Int
  -- ^ of those, copies already off their own path
  , cause :: Cause
  , split :: Bool
  }
  deriving stock (Eq, Show)

{- | The tables to show, in the order the evaluation first reached their
branch points: those where some copy's own scrutinee chose otherwise than
the branch taken.
-}
tables :: Remarks -> [Table]
tables (Remarks m) =
  map
    snd
    (sortOn fst [(t.first, table s t) | (s, t) <- Map.toList m, t.differing > 0])
 where
  table s t =
    Table
      { site = s
      , rows = t.rows
      , taken = t.taken
      , evaluations = t.evaluations
      , counted = sum (IntMap.elems t.rows)
      , departed = t.departed
      , cause = t.cause
      , split = t.split
      }
