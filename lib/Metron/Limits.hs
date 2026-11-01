{- | Resource limits (design §8.1): how much an evaluation may ask of the
machine before it fails with an ordinary error naming the setting it hit.

A limit is a property of the session, changed with @:set@ and on the
command line, never of a term: it never changes a value or a hash, only
whether an evaluation finishes. @steps@ and @depth@ are counted by the
evaluator through a 'Budget'; @digits@ and @components@ are checked where
numbers and tensors are made; @memory@ and @time@ are the runtime's and
are enforced around an input by 'runLimited'.
-}
module Metron.Limits (
  Limits (..),
  Limit (..),
  defaultLimits,
  limitName,
  limitHint,
  settingLines,
  setLimit,
  parseCount,

  -- * The evaluator's budget
  Budget,
  newBudget,
  spend,
  nested,
  Context (..),
  newContext,
  reach,
  within,
  remarksAfter,

  -- * Sizes of numbers
  log10Abs,
  beyond,

  -- * Around an input
  runLimited,
  applyMemory,
  limitHeap,
) where

import Control.Exception (
  AsyncException (HeapOverflow, StackOverflow),
  evaluate,
  mask,
  throwIO,
  try,
 )
import Control.Monad (unless)
import Data.Bits (shiftR, unsafeShiftL)
import Data.Char (isDigit)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map.Strict (Map)
import Data.Maybe (isNothing)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word64)
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrArray, withForeignPtr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import GHC.Num.Integer (integerLog2)
import Metron.Remark (
  Cause,
  Pending,
  Reach (..),
  Remarks,
  Site,
  pend,
  remarksOf,
 )
import Metron.Scalar (Members, memberVector)
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import System.Mem (performMajorGC)
import System.Timeout (timeout)

-- | The settings (design §8.1).
data Limits = Limits
  { memory :: Int
  -- ^ the runtime's heap, in GB
  , steps :: Int
  -- ^ evaluation steps per expression
  , depth :: Int
  -- ^ nested evaluations, calls whose result something waits for
  , digits :: Int
  -- ^ the largest decimal exponent, either way, of a number
  , components :: Int
  -- ^ the components of one tensor
  , time :: Maybe Int
  -- ^ wall-clock seconds per input; 'Nothing' is off
  }
  deriving stock (Eq, Show)

-- | Which limit was hit.
data Limit = Memory | Steps | Depth | Digits | Components | Time
  deriving stock (Eq, Show, Enum, Bounded)

{- | The defaults, chosen by measurement (design §8.1, as built): the test
suite, the library and the tutorial use a small fraction of each, and a
runaway meets one within seconds.
-}
defaultLimits :: Limits
defaultLimits =
  Limits
    { memory = 4
    , steps = 100_000_000
    , depth = 100_000
    , digits = 100_000
    , components = 10_000_000
    , time = Nothing
    }

-- | The setting's name, as @:set@ takes it.
limitName :: Limit -> Text
limitName = \case
  Memory -> "memory"
  Steps -> "steps"
  Depth -> "depth"
  Digits -> "digits"
  Components -> "components"
  Time -> "time"

-- | What an error ends with: the setting that would let it finish.
limitHint :: Limit -> Text
limitHint l = " (`:set " <> limitName l <> "`)"

-- | The settings as @:set@ lists them.
settingLines :: Limits -> [Text]
settingLines l =
  [ "memory " <> tshow l.memory
  , "steps " <> tshow l.steps
  , "depth " <> tshow l.depth
  , "digits " <> tshow l.digits
  , "components " <> tshow l.components
  , "time " <> maybe "off" tshow l.time
  ]

{- | Change one setting by name, as @:set name value@ and @--set name
value@ do. 'Nothing' when the name is not a limit's.
-}
setLimit :: Text -> Text -> Limits -> Maybe (Either Text Limits)
setLimit name value l = case name of
  "memory" -> Just (positive (\k -> l{memory = k}))
  "steps" -> Just (positive (\k -> l{steps = k}))
  "depth" -> Just (positive (\k -> l{depth = k}))
  "digits" -> Just (positive (\k -> l{digits = k}))
  "components" -> Just (positive (\k -> l{components = k}))
  "time"
    | value == "off" -> Just (Right l{time = Nothing})
    | otherwise -> Just (positive (\k -> l{time = Just k}))
  _ -> Nothing
 where
  positive set = case parseCount value of
    Just k | k > 0 -> Right (set k)
    _ ->
      Left
        ( name
            <> " is a positive whole number, such as 1000000 or 1e6"
            <> (if name == "time" then ", or off" else "")
        )

{- | A count as a setting is written: digits with optional @_@ separators,
or a mantissa and a power of ten, @1e9@, @2.5e6@, whose value is whole.
-}
parseCount :: Text -> Maybe Int
parseCount t = case T.splitOn "e" (T.filter (/= '_') t) of
  [m] -> whole m 0
  [m, e] | Just k <- natural e, k <= 18 -> whole m k
  _ -> Nothing
 where
  natural s
    | not (T.null s) && T.all isDigit s && T.length s <= 18 =
        Just (read (T.unpack s) :: Int)
    | otherwise = Nothing
  whole m k = case T.splitOn "." m of
    [i] -> scaled i "" k
    [i, f] -> scaled i f k
    _ -> Nothing
  scaled i f k
    | T.null i || not (T.all isDigit i) || not (T.all isDigit f) = Nothing
    | T.length f > k && T.any (/= '0') (T.drop k f) = Nothing
    | otherwise = do
        let ds = i <> T.take k (f <> T.replicate k "0")
        n <- if T.length ds <= 18 then Just (read (T.unpack ds) :: Integer) else Nothing
        if n <= toInteger (maxBound :: Int) then Just (fromInteger n) else Nothing

tshow :: (Show a) => a -> Text
tshow = T.pack . show

-- The budget ------------------------------------------------------------------------

{- | What one evaluation has spent: the steps it took and how deeply it is
nested now; and what it noted on the way, the branch points its copies
reached (design §8.2). Counted in place: the evaluator is pure, and
threading a counter through every thunk would make every value a
computation. The count changes no value: an evaluation either finishes
with the value it would have had, or fails with the limit it hit.
-}
data Budget = Budget
  { limits :: Limits
  , counters :: ForeignPtr Int
  , branches :: IORef (Map Site Pending)
  -- ^ the branch points reached with copies, kept in place as the counters are
  , current :: IORef (Maybe (VU.Vector Int))
  {- ^ the group of copies, by global number, whose alternative is being
  evaluated, when a branch point has split them: a value shared with the
  evaluation around the split, when forced for the group, counts only the
  group's copies at its branch points
  -}
  }

{- | A fresh budget, for one evaluation. Each of the double backend's
parallel batches (design §8.2) is one, with the whole @steps@ limit. Its
last argument keeps two evaluations from sharing one: each passes what it
evaluates.
-}
newBudget :: Limits -> a -> Budget
newBudget l x = unsafeDupablePerformIO $ do
  _ <- evaluate (x `seq` ())
  cs <- mallocForeignPtrArray 2
  withForeignPtr cs $ \p -> mapM_ (\i -> pokeElemOff p i 0) [0, 1]
  Budget l cs <$> newIORef mempty <*> newIORef Nothing
{-# NOINLINE newBudget #-}

{- | Where an evaluation is, among the double backend's copies (design
§8.2): the copies it carries, whether it is the evaluation of the whole
batch, whether it follows the nominal path, and its place below the
branch points that split the copies, with a count of the branch points
it has reached itself. The count is the evaluation's own, so a branch
point has the same place in every batch, whatever the other groups of a
split do. And the copies, by global number, that an earlier branch point
this evaluation is inside took along although their own scrutinee
chose another alternative: they have left the evaluated path.
-}
data Context = Context
  { members :: Members
  , whole :: Bool
  , nominal :: Bool
  , place :: [Int]
  , counter :: IORef Int
  , departed :: IntSet
  }

{- | A context with its own count and no copy departed. Its last argument
keeps two from sharing one.
-}
newContext :: Members -> Bool -> Bool -> [Int] -> a -> Context
newContext m whole nominal place x = unsafePerformIO $ do
  _ <- evaluate (x `seq` ())
  counter <- newIORef 0
  pure (Context m whole nominal place counter IntSet.empty)
{-# NOINLINE newContext #-}

{- | Note that an evaluation reached a branch point with copies: their own
alternatives, in the order of the context's copies, the copies the
scrutinee already says are off their path, the alternative the
evaluation takes, and whether the copies split there. Only the copies of
the group being evaluated count, if any is. The result is the copies off
their path in the alternative taken: those before, and, unless the copies
split, those whose own alternative is another. Not dupable, since the
context's count is taken once; the alternatives make every call its own.
-}
reach ::
  Budget ->
  Context ->
  Site ->
  Int ->
  Cause ->
  Bool ->
  IntSet ->
  VU.Vector Int ->
  IntSet
reach b ctx site taken cause split left alts = unsafePerformIO $ do
  n <- readIORef ctx.counter
  writeIORef ctx.counter (n + 1)
  group <- readIORef b.current
  let everyone = memberVector ctx.members
      places = case group of
        Nothing -> Nothing
        Just g -> Just (VU.findIndices (inSorted g) everyone)
      counted = maybe alts (VU.backpermute alts) places
      globals = maybe everyone (VU.backpermute everyone) places
      rows =
        IntMap.fromList
          [ (a, k)
          | (a, k) <- zip [0 ..] (VU.toList (alternativeCounts counted))
          , k > 0
          ]
      off = IntSet.union ctx.departed left
      already
        | IntSet.null off = 0
        | otherwise = VU.length (VU.filter (`IntSet.member` off) globals)
      leaving
        | split = IntSet.empty
        | otherwise =
            IntSet.fromList
              (VU.toList (VU.ifilter (\i _ -> VU.unsafeIndex alts i /= taken) everyone))
  unless (VU.null counted)
    $ modifyIORef'
      b.branches
      ( pend
          site
          Reach
            { position = ctx.place ++ [n]
            , nominal = if ctx.nominal then Just taken else Nothing
            , cause
            , rows
            , departed = already
            , split
            , counted =
                if ctx.whole && isNothing group then Nothing else Just (VU.toList globals)
            }
      )
  pure (IntSet.union off leaving)
{-# NOINLINE reach #-}

{- | Evaluate a value for a group of copies, by global number: its branch
points count only them. The group in force before is restored after.
-}
within :: Budget -> VU.Vector Int -> a -> a
within b g x = unsafePerformIO $ do
  before <- readIORef b.current
  writeIORef b.current (Just g)
  r <- evaluate x
  writeIORef b.current before
  pure r
{-# NOINLINE within #-}

-- | Whether a number is in an ascending vector.
inSorted :: VU.Vector Int -> Int -> Bool
inSorted v x = go 0 (VU.length v)
 where
  go lo hi
    | lo >= hi = False
    | otherwise =
        let mid = (lo + hi) `div` 2
            y = VU.unsafeIndex v mid
         in case compare x y of
              EQ -> True
              LT -> go lo mid
              GT -> go (mid + 1) hi

-- | How many of the alternatives are each number, from 0 to the largest.
alternativeCounts :: VU.Vector Int -> VU.Vector Int
alternativeCounts as
  | VU.null as = VU.empty
  | otherwise =
      VU.accumulate (+) (VU.replicate (VU.maximum as + 1) 0) (VU.map (,1) as)

{- | The branch points so far: read after the value they came from has been
evaluated, which the first argument forces.
-}
remarksAfter :: a -> Budget -> Remarks
remarksAfter x b = unsafeDupablePerformIO $ do
  _ <- evaluate x
  remarksOf <$> readIORef b.branches
{-# NOINLINE remarksAfter #-}

{- | Count one step of the evaluation of the given term: 'False' once the
evaluation has taken more than its steps. The term makes every call its
own, so that no two are shared.
-}
spend :: Budget -> t -> Bool
spend b t = unsafeDupablePerformIO $ withForeignPtr b.counters $ \p -> do
  n <- peekElemOff p 0
  pokeElemOff p 0 (n + 1)
  pure (t `seq` n < b.limits.steps)
{-# NOINLINE spend #-}

{- | Evaluate a value that something waits for, one level deeper: the
error value given instead when that would nest more than the limit
allows.
-}
nested :: Budget -> a -> a -> a
nested b over x = unsafeDupablePerformIO $ withForeignPtr b.counters $ \p -> do
  d <- peekElemOff p 1
  if d >= b.limits.depth
    then pure over
    else do
      pokeElemOff p 1 (d + 1)
      r <- evaluate x
      pokeElemOff p 1 d
      pure r
{-# NOINLINE nested #-}

-- Sizes ------------------------------------------------------------------------------

{- | @log₁₀ |r|@, from the leading bits of the numerator and denominator,
never writing the number out; 0 for 0. Close enough to tell how many
digits a number has, which is all a limit needs.
-}
log10Abs :: Rational -> Double
log10Abs r
  | r == 0 = 0
  | otherwise = (log2 (abs (numerator r)) - log2 (denominator r)) * logBase 10 2
 where
  log2 :: Integer -> Double
  log2 n =
    let k = fromIntegral (integerLog2 n) :: Int
        s = max 0 (k - 52)
     in fromIntegral s + logBase 2 (fromInteger (n `shiftR` s))

{- | Whether a number of the given @log₁₀@ is further from 1 than the
@digits@ limit allows, and if so what it would need.
-}
beyond :: Limits -> Double -> Maybe Text
beyond l e
  | e > limit = Just ("would have more than " <> tshow l.digits <> " digits")
  | e < negate limit =
      Just ("would have more than " <> tshow l.digits <> " zeros after the point")
  | otherwise = Nothing
 where
  limit = fromIntegral l.digits :: Double

-- Around an input ------------------------------------------------------------------------

{- | Run an input's work under the limits only the runtime can enforce: the
heap and the clock. The work must force everything it returns. A heap
overflow or a timeout becomes an error naming its setting, and the
session goes on; so does a Haskell stack overflow, which only nesting
deeper than the evaluator counts can cause.
-}
runLimited :: Limits -> IO a -> IO (Either Text a)
runLimited l work = mask $ \restore -> do
  r <-
    try
      (restore (maybe (Just <$> work) (\s -> timeout (s * 1_000_000) work) l.time))
  case r of
    Right (Just x) -> pure (Right x)
    Right Nothing ->
      pure
        ( Left
            ("error: the input took more than " <> plural l.time "second" <> limitHint Time)
        )
    Left HeapOverflow -> do
      settle restore
      pure
        ( Left
            ( "error: the evaluation needed more than "
                <> tshow l.memory
                <> " GB"
                <> limitHint Memory
            )
        )
    Left StackOverflow ->
      pure (Left ("error: the evaluation nested too deeply" <> limitHint Depth))
    Left e -> throwIO e
 where
  -- Collect, taking in any further heap overflow the runtime throws for
  -- the same work: while the double backend's parallel batches are being
  -- stopped (design §8.2) they go on allocating, and the runtime throws
  -- again. Masked, those wait here instead of reaching the top level and
  -- ending the session.
  settle restore = do
    again <- try (restore performMajorGC)
    case again of
      Left HeapOverflow -> settle restore
      Left e -> throwIO e
      Right () -> pure ()
  plural n w = case n of
    Just 1 -> "1 " <> w
    Just k -> tshow k <> " " <> w <> "s"
    Nothing -> "no " <> w <> "s"

{- | Make the runtime's maximum heap the setting, in GB. The collector reads
it at every collection, so a change takes effect at once.
-}
applyMemory :: Limits -> IO ()
applyMemory l = limitHeap (fromIntegral l.memory `unsafeShiftL` 30)

-- | The runtime's maximum heap, in bytes; 0 is none.
limitHeap :: Word64 -> IO ()
limitHeap = setMaxHeap

foreign import ccall unsafe "metron_set_max_heap"
  setMaxHeap :: Word64 -> IO ()
