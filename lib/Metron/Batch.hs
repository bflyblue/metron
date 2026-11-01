{- | The double backend's copies in parallel batches (design §8.2, @:set
cores@): with @samples N@, an expression is evaluated K times, each
evaluation carrying about N/K of the copies in lockstep, and the K values
are merged into the one a single evaluation would give.

Each copy's random choices, its roundings and its draws, are keyed by its
number among all N, so a copy is the same number whichever batch carries
it, and every branch is decided by the IEEE value, which every batch
computes alike. The merged value is the batches' copies concatenated in
order: the same copies, bit for bit, as one evaluation's, and so the same
statistics, computed from them in the same order. (The design names
Chan's parallel update of means and variances; it sums in an order that
depends on K, so its last bits would.)

What reads across a number's copies, @mid@, @sd@, @errorOf@ and
@digitsOf@, would read only its own batch's, so an input that reaches
them runs as one evaluation ('acrossCopies'), as does one whose batches
do not merge ('merged').
-}
module Metron.Batch (
  batchesOf,
  acrossCopies,
  forced,
  merged,
  failure,
) where

import Control.Exception (evaluate)
import Control.Monad (void)
import Data.Either (lefts)
import Data.List (transpose)
import Data.Set (Set)
import Data.Set qualified as Set (fromList)
import Data.Text (Text)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import GHC.Float (castDoubleToWord64)
import Metron.Double (Dbl (..), Estimate (..))
import Metron.Eval (EvalError (Exceeded), ValueOf (..))
import Metron.Limits (Limit (Steps))
import Metron.Scalar (Batch (..))

{- | @n@ copies in @k@ batches, in order, their sizes differing by at most
one; at most @n `div` 2@ of them, so that every batch has the two copies a
spread needs.
-}
batchesOf :: Int -> Int -> [Batch]
batchesOf n k0 =
  [ Batch
      { first = i * size + min i extra
      , count = size + (if i < extra then 1 else 0)
      , batches = k
      }
  | i <- [0 .. k - 1]
  ]
 where
  k = max 1 (min k0 (n `div` 2))
  (size, extra) = n `divMod` k

-- | The built-ins that read across a number's copies.
acrossCopies :: Set Text
acrossCopies = Set.fromList ["mid", "sd", "errorOf", "digitsOf"]

{- | Force what a value will print: every element of a tensor, every
field of a constructor, down to the copies. Run in the thread that
evaluates its batch, so that each batch is forced in one thread only.
-}
forced :: ValueOf Dbl -> IO ()
forced = \case
  VTensor _ _ _ xs -> mapM_ forcedElement xs
  VPoint _ _ _ xs -> mapM_ forcedElement xs
  VData _ fs -> mapM_ (either (\_ -> pure ()) forced) fs
  VUnit v -> forced v
  VChart _ -> pure ()
  VClosure _ -> pure ()
  VTyAbs{} -> pure ()
 where
  forcedElement = \case
    Right x -> void (evaluate x)
    Left _ -> pure ()

{- | The batches' values as one: the same shape in each, the copies of each
number concatenated in batch order. 'Nothing' when they differ in any
way but their copies, or hold a chart, whose numbers are not merged; the
input then runs as one evaluation.
-}
merged :: [ValueOf Dbl] -> Maybe (ValueOf Dbl)
merged = \case
  [] -> Nothing
  vs@(v0 : _) -> case v0 of
    VTensor dims d hint xs0 -> do
      bufs <-
        traverse
          ( \case
              VTensor dims' _ _ b | dims' == dims && V.length b == V.length xs0 -> Just b
              _ -> Nothing
          )
          vs
      VTensor dims d hint . V.fromList
        <$> traverse element (transpose (map V.toList bufs))
    VUnit _ -> VUnit <$> (merged =<< traverse (\case VUnit v -> Just v; _ -> Nothing) vs)
    VData c fs0 -> do
      fieldss <-
        traverse
          (\case VData c' fs | c' == c && length fs == length fs0 -> Just fs; _ -> Nothing)
          vs
      VData c <$> traverse field (transpose fieldss)
    VClosure _ -> Just v0
    VTyAbs{} -> Just v0
    VChart _ -> Nothing
    VPoint{} -> Nothing
 where
  field ts = case sequence ts of
    Right vs -> Right <$> merged vs
    Left _ -> Left <$> failure ts

{- | The error batches that failed give together: the @steps@ limit, which
they share, if any reached it; else their error, if all failed alike;
else none, and the batches do not merge.
-}
failure :: [Either EvalError a] -> Maybe EvalError
failure rs = case [e | Left e@(Exceeded Steps _) <- rs] of
  e : _ -> Just e
  [] -> case lefts rs of
    e : more | length more + 1 == length rs && all (== e) more -> Just e
    _ -> Nothing

-- | One element across the batches: all numbers, merged, or all errors.
element :: [Either EvalError Dbl] -> Maybe (Either EvalError Dbl)
element es = case sequence es of
  Right xs -> Right <$> number xs
  Left _ -> Left <$> failure es

{- | One number across the batches: the same IEEE value in each, bit for
bit, and its copies concatenated; a number without copies (known
exactly) is the same in each.
-}
number :: [Dbl] -> Maybe Dbl
number = \case
  [] -> Nothing
  xs@(x0 : _)
    | any ((/= bits x0.value) . bits . (.value)) xs -> Nothing
    | otherwise -> case traverse copies xs of
        Just css -> Just x0{estimate = Copies (VU.concat css)}
        Nothing
          | all ((== x0.estimate) . (.estimate)) xs -> Just x0
          | otherwise -> Nothing
 where
  bits = castDoubleToWord64
  copies x = case x.estimate of
    Copies cs -> Just cs
    ErrorBound _ -> Nothing
