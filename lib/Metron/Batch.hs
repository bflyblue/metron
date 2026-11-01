{-# LANGUAGE PatternSynonyms #-}

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

import Data.Either (lefts)
import Data.List (transpose)
import Data.Set (Set)
import Data.Set qualified as Set (fromList)
import Data.Text (Text)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import GHC.Float (castDoubleToWord64)
import Metron.Builtin (pattern ConsC, pattern NilC)
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

{- | Force what a value will print, in the order the printer forces it
("Metron.Pretty"), down to the copies, and no further: the elements of
a tensor in order and the fields of a constructor in order, each in full,
up to the first error, where printing stops; a list's spine and items
first, then each item. So a batch does the reductions the single
evaluation's printing does, and no others. Run in the thread that
evaluates its batch, so that each batch is forced in one thread only.
'False' once an error is met.
-}
forced :: ValueOf Dbl -> IO Bool
forced = \case
  VTensor _ _ _ xs -> allM forcedElement (V.toList xs)
  VPoint _ _ _ xs -> allM forcedElement (V.toList xs)
  v@(VData c _) | c == ConsC || c == NilC -> case items v of
    Just vs -> allM forced vs
    Nothing -> pure False
  VData _ fs -> allM (either (const (pure False)) forced) fs
  VUnit v -> forced v
  VChart _ -> pure True
  VClosure _ -> pure True
  VTyAbs{} -> pure True
 where
  forcedElement = \case
    Right x -> True <$ evaluate x
    Left _ -> pure False
  -- The spine and each item to its constructor, as the printer walks a
  -- list before it prints any item.
  items = \case
    VData NilC [] -> Just []
    VData ConsC [Right x, Right xs] -> (x :) <$> items xs
    _ -> Nothing

-- | Each action in turn, while they succeed.
allM :: (a -> IO Bool) -> [a] -> IO Bool
allM f = \case
  [] -> pure True
  x : rest -> f x >>= \ok -> if ok then allM f rest else pure False

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

{- | The error batches that failed give together: the @steps@ limit, if
any reached it (each has the whole limit and takes the same steps, so
all reach it alike); else their error, if all failed alike; else none,
and the batches do not merge.
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
