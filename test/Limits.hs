{- | Resource limits (design §8.1): each runaway stops quickly with an
error naming its setting, raising the setting lets a program finish, and
the loops that used to leak run in constant memory.

Memory is measured as the runtime sees it: after a major collection, the
heap is limited to what is live plus a margin, and a program that keeps
more than the margin fails with a heap overflow instead of finishing.
-}
module Limits (Measured, measure, limitTests) where

import Control.Exception (bracket_, evaluate)
import Control.Monad (join)
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Stats (GCDetails (..), RTSStats (..), getRTSStats)
import Metron.Driver (Session, feed, seededSession)
import Metron.Limits (
  Limits (..),
  defaultLimits,
  limitHeap,
  parseCount,
  runLimited,
 )
import System.Mem (performMajorGC)
import Test.Tasty
import Test.Tasty.HUnit

limitTests :: Measured -> TestTree
limitTests m =
  localOption (mkTimeout 60_000_000)
    $ testGroup
      "limits (design §8.1)"
      [ settingTests
      , stepsTests
      , depthTests
      , digitsTests
      , memoryTests m
      , timeTests
      , leakTests m
      ]

-- Running sessions -------------------------------------------------------------------

seeded :: Session
seeded = either (error . T.unpack) id seededSession

-- | Lines fed in turn to a seeded session; the outputs, or the first error.
run :: [Text] -> Either Text [Text]
run = go seeded []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

-- | The lines fail with an error that says the given text.
refused :: Text -> [Text] -> Assertion
refused what ls = case run ls of
  Left err -> T.isInfixOf what err @? T.unpack err
  Right out -> assertFailure ("expected an error, got " <> show out)

{- | The lines, run under the runtime's limits, with every output forced
inside them, as the executable runs an input.
-}
runIO :: Limits -> [Text] -> IO (Either Text [Text])
runIO l ls = do
  r <- runLimited l (evaluate (forced (run ls)))
  pure (join r)
 where
  forced r = case r of
    Left err -> T.length err `seq` r
    Right outs -> sum (map T.length outs) `seq` r

{- | Run with the heap limited to what is live now plus the margin in MB,
and no limit after.
-}
withinMB :: Int -> IO a -> IO a
withinMB margin act = do
  performMajorGC
  live <- (.gc.gcdetails_live_bytes) <$> getRTSStats
  bracket_
    (limitHeap (live + fromIntegral margin * 1024 * 1024))
    (limitHeap 0)
    act

-- Settings -------------------------------------------------------------------------

settingTests :: TestTree
settingTests =
  testGroup
    "settings"
    [ testCase "a count is written plainly, with separators, or with a power of ten" $ do
        parseCount "1000000" @?= Just 1000000
        parseCount "1_000_000" @?= Just 1000000
        parseCount "1e9" @?= Just 1000000000
        parseCount "2.5e6" @?= Just 2500000
        parseCount "1.5" @?= Nothing
        parseCount "1e19" @?= Nothing
        parseCount "lots" @?= Nothing
    , testCase ":set changes a limit, and refuses what is not one" $ do
        let setting name = fmap (filter (T.isPrefixOf (name <> " ")))
        setting "steps" (run [":set steps 2e6", ":set"]) @?= Right ["steps 2000000"]
        setting "time" (run [":set time 5", ":set time off", ":set"])
          @?= Right ["time off"]
        refused "steps is a positive whole number" [":set steps 0"]
        refused
          "time is a positive whole number, such as 1000000 or 1e6, or off"
          [":set time never"]
    , testCase "a limit changes no value and no hash" $ do
        let program = ["let k = 2^40 / 3", "k", ":hash k"]
        run ([":set steps 1e9", ":set digits 50", ":set depth 1000"] ++ program)
          @?= run program
    ]

-- Steps ------------------------------------------------------------------------------

stepsTests :: TestTree
stepsTests =
  testGroup
    "steps"
    [ testCase "an endless loop stops at the limit"
        $ refused
          "the evaluation took more than 1000000 steps (`:set steps`)"
          [":set steps 1e6", "let f n = f (n + 1)", "f 0"]
    , testCase "raising the limit lets a long loop finish" $ do
        let loop = ["let hh n = if n == 0 then 0 else hh (n - 1)", "hh 200000"]
        refused "(`:set steps`)" (":set steps 1e6" : loop)
        run (":set steps 1e7" : loop) @?= Right ["0"]
    , testCase "each expression has its own steps"
        $ run
          [ ":set steps 3e6"
          , "let hh n = if n == 0 then 0 else hh (n - 1)"
          , "hh 200000"
          , "hh 200000"
          , "hh 200000"
          ]
          @?= Right ["0", "0", "0"]
    ]

-- Depth ------------------------------------------------------------------------------

depthTests :: TestTree
depthTests =
  testGroup
    "depth"
    [ testCase "deep recursion stops at the limit; raising it lets it finish" $ do
        let deep = ["let g n = if n == 0 then 0 else 1 + g (n - 1)", "g 5000"]
        refused
          "the evaluation nested more than 1000 calls deep (`:set depth`)"
          (":set depth 1000" : deep)
        run (":set depth 1e4" : deep) @?= Right ["5000"]
    , testCase "the default stops a runaway recursion"
        $ refused
          "(`:set depth`)"
          ["let g n = if n == 0 then 0 else 1 + g (n - 1)", "g 1000000"]
    , testCase "a tail call is no deeper"
        $ run
          [":set depth 100", "let hh n = if n == 0 then 0 else hh (n - 1)", "hh 100000"]
          @?= Right ["0"]
    , testCase "a tail call through a split is no deeper (design §8.2)"
        -- 2000 samples stop at their own steps, so the copies split at
        -- most of the loop's steps.
        $ case run
          ( drawn 10
              <> ["let count n = if n * x > 1000 then n else count (n + 1)", "count 0"]
          ) of
          Right outs -> any ("1001 (Monte Carlo" `T.isPrefixOf`) outs @? show outs
          Left err -> assertFailure (T.unpack err)
    , testCase "a split whose value something waits for nests"
        $ refused
          "the evaluation nested more than 1000 calls deep (`:set depth`)"
          (drawn 1000 <> ["let g n = if n * x > 10000 then 0 else 1 + g (n + 1)", "g 0"])
    ]
 where
  -- 2000 samples of a declared σ, under a depth limit.
  drawn :: Int -> [Text]
  drawn d =
    [ ":backend double"
    , ":set samples 2000"
    , ":set depth " <> T.pack (show d)
    , "let x = 1 ±σ 0.1"
    ]

-- Digits -----------------------------------------------------------------------------

digitsTests :: TestTree
digitsTests =
  testGroup
    "digits"
    [ testCase "a power's size is known before it is computed" $ do
        refused
          "the power would have more than 100000 digits (`:set digits`)"
          ["2^18446744073709551616"]
        refused "the power would have more than 100000 digits" ["(3/2)^1000000"]
        refused
          "the power would have more than 100000 zeros after the point"
          ["(2/3)^1000000"]
    , testCase "a literal's size is known before it is written out" $ do
        refused
          "the literal would have more than 100000 digits (`:set digits`)"
          ["1e1000000000"]
        refused
          "the literal would have more than 100000 zeros after the point"
          ["1e-1000000000"]
    , testCase "an exponential's size is known before its series is summed" $ do
        refused "the exponential would have more than 100000 digits" ["exp 1000000"]
        refused
          "the exponential would have more than 100000 zeros after the point"
          ["exp (-1000000)"]
        refused "the exponential would have more than 100000 digits" ["cosh 1000000"]
    , testCase "a result that grows past the limit is refused"
        $ refused
          "the result would have more than 100000 digits (`:set digits`)"
          ["let sq x k = if k == 0 then x else sq (x * x) (k - 1)", "sq 10 20"]
    , testCase "raising the limit lets the number be written" $ do
        refused "more than 10 digits" [":set digits 10", "2^40"]
        run [":set digits 20", "2^40"] @?= Right ["1099511627776"]
        refused "more than 10 digits" [":set digits 10", "1e15"]
        run [":set digits 20", "1e15"] @?= Right ["1000000000000000"]
    ]

-- Memory -----------------------------------------------------------------------------

{- | What has to run on the main thread: the runtime throws a heap overflow
to the main thread, which in the executable is the one evaluating, and in
the test suite is not the one running a test. 'measure' runs these before
the tests start; the tests check what came back.
-}
data Measured = Measured
  { overflows :: [Either Text [Text]]
  -- ^ a program past the heap, twice, then @1 + 1@
  , leaks :: [Either Text [Text]]
  -- ^ each of 'leakPrograms', within its margin
  }

-- | Run what measures memory, on the calling thread, which must be the main one.
measure :: IO Measured
measure = do
  let big = withinMB 200 (runIO defaultLimits ["reverse (range 0 3e7)"])
  first <- big
  second <- big
  afterwards <- withinMB 200 (runIO defaultLimits ["1 + 1"])
  leaks <- mapM (\(_, ls, _) -> withinMB 64 (runIO defaultLimits ls)) leakPrograms
  pure Measured{overflows = [first, second, afterwards], leaks}

memoryTests :: Measured -> TestTree
memoryTests m =
  testGroup
    "memory"
    [ testCase "a heap overflow is an error, and the session goes on" $ case m.overflows of
        [Left a, Left b, afterwards] -> do
          T.isInfixOf "(`:set memory`)" a @? T.unpack a
          T.isInfixOf "(`:set memory`)" b @? T.unpack b
          afterwards @?= Right ["2"]
        other -> assertFailure (show other)
    ]

-- Time -------------------------------------------------------------------------------

timeTests :: TestTree
timeTests =
  testGroup
    "time"
    [ testCase "an input past the time limit stops" $ do
        -- A countdown of six million steps takes about 3 s, within the
        -- steps limit. (The exact logistic map once served, its rationals
        -- doubling every step; it now runs at working precision, design
        -- §3.2.8, and finishes at once.)
        r <-
          runIO
            defaultLimits{time = Just 1}
            [ "let hh n = if n == 0 then 0 else hh (n - 1)"
            , "hh 6000000"
            ]
        case r of
          Left err -> T.isInfixOf "took more than 1 second (`:set time`)" err @? T.unpack err
          Right out -> assertFailure (show out)
    , testCase "off by default" $ defaultLimits.time @?= Nothing
    ]

-- Leaks ------------------------------------------------------------------------------

{- | Programs that once kept memory proportional to how long they ran, each
with what it must give within 64 MB more than was live before it.
-}
leakPrograms :: [(TestName, [Text], Either Text [Text] -> Assertion)]
leakPrograms =
  [
    ( "a lazy list consumed by length"
    , ["length (range 0 1e6)"]
    , (@?= Right ["1000001"])
    )
  ,
    ( "a strict left fold over a large range"
    , ["foldl' (\\n x -> n + x) 0 (range 0 1e6)"]
    , (@?= Right ["500000500000"])
    )
  ,
    ( "a fold whose function is written inside another"
    , ["let len xs = foldl' (\\n _ -> n + 1) 0 xs", "len (range 0 1e6)"]
    , (@?= Right ["1000001"])
    )
  ,
    ( "a loop with an accumulator"
    , ["let go n acc = if n == 0 then acc else go (n - 1) (acc + 1)", "go 1000000 0"]
    , (@?= Right ["1000000"])
    )
  ,
    ( "an endless loop stops at steps, not at memory"
    , [":set steps 3e7", "let f n = f (n + 1)", "f 0"]
    , \case
        Left err -> T.isInfixOf "(`:set steps`)" err @? T.unpack err
        Right out -> assertFailure (show out)
    )
  ,
    ( "a state vector carried through a loop"
    ,
      [ "let go v k = if k == 0 then v else go (v + [1, 1, 1, 1, 1, 1]) (k - 1)"
      , "go [0, 0, 0, 0, 0, 0] 1000000"
      ]
    , (@?= Right ["[1000000, 1000000, 1000000, 1000000, 1000000, 1000000]"])
    )
  ,
    ( "a quantity with a unit carried through a loop"
    , ["let go v k = if k == 0 then v else go (v + 1 m) (k - 1)", "go (0 m) 1000000"]
    , (@?= Right ["1000000 m"])
    )
  , -- Exact while its rationals are short, then at working precision
    -- (design §3.2.8): once 13 s for twenty steps, its digits doubling.

    ( "the exact logistic map, at working precision after its first steps"
    ,
      [ ":set precision 200"
      , "let iter x k = if k == 0 then x else iter (x * (1 - x) * 37/10) (k - 1)"
      , "iter (1/3) 250"
      ]
    , \case
        Right [out] ->
          T.isPrefixOf "0.92481968045107953044160642097568835177392693028574" out
            @? T.unpack out
        other -> assertFailure (show other)
    )
  , -- A loop whose condition carries draws splits the copies at every
    -- step, each sample stopping at its own (design §8.2): once one level
    -- of recombination per step, 470 MB at this size.

    ( "a loop whose condition carries draws, each sample stopping at its own step"
    ,
      [ ":backend double"
      , ":set samples 100"
      , "let x = 1 ±σ 0.1"
      , "let count n = if n * x > 100000 then n else count (n + 1)"
      , "count 0"
      ]
    , \case
        Right outs -> any ("100001 (Monte Carlo" `T.isPrefixOf`) outs @? show outs
        Left err -> assertFailure (T.unpack err)
    )
  ,
    ( "the margin is tight enough to see growth: a list kept whole overflows it"
    , ["length (reverse (range 0 1e6))"]
    , \case
        Left err -> T.isInfixOf "(`:set memory`)" err @? T.unpack err
        Right out -> assertFailure (show out)
    )
  ]

leakTests :: Measured -> TestTree
leakTests m =
  testGroup "constant memory"
    $ zipWith (\(name, _, check) r -> testCase name (check r)) leakPrograms m.leaks
      ++ [ testCase "foldl stays lazy in its accumulator; foldl' evaluates it" $ do
             run ["foldl (\\_ x -> x) (1/0) (range 0 3)"] @?= Right ["3"]
             run ["foldl (\\acc _ -> acc) 1 {1/0, 2}"] @?= Right ["1"]
             run ["foldl' (\\_ x -> x) (1/0) (range 0 3)"] @?= Right ["3"]
             refused
               "division by zero"
               ["foldl' (\\acc x -> if acc > 0 then x else x) (1/0) (range 0 3)"]
         , testCase
             "seq evaluates to a value and every component; a failing component fails only where used"
             $ do
               run ["seq (1 + 1) 5"] @?= Right ["5"]
               run ["seq (1/0) 5"] @?= Right ["5"]
               refused "division by zero" ["seq (if 1/0 > 0 then 1 else 2) 5"]
               run ["seq [1/0, 2] 5"] @?= Right ["5"]
         ]
