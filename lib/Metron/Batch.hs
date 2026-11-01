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
import Data.IntSet qualified as IntSet
import Data.List (elemIndex, transpose)
import Data.Set (Set)
import Data.Set qualified as Set (fromList)
import Data.Text (Text)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import GHC.Float (castDoubleToWord64)
import Metron.Builtin (pattern ConsC, pattern NilC)
import Metron.Core (ConRef (UserCon))
import Metron.Double (Dbl (..), Estimate (..))
import Metron.Eval (
  Choice (..),
  EvalError (Exceeded),
  Mixture (..),
  Option (..),
  ValueOf (..),
 )
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

{- | Force what a value will print ("Metron.Pretty"), down to the copies,
and no further: the elements of a tensor in order and the fields of a
constructor in order, each in full, up to the first error, where
printing stops; a list item by item; every outcome of a mixture (design
§8.2). So a batch does the reductions the single evaluation's printing
does, and no others, and has noted every branch point it reaches before
its notes are read. Run in the thread that evaluates its batch, so that
each batch is forced in one thread only. 'False' once an error is met.
-}
forced :: ValueOf Dbl -> IO Bool
forced = \case
  VTensor _ _ _ xs -> allM forcedElement (V.toList xs)
  VPoint _ _ _ xs -> allM forcedElement (V.toList xs)
  v@(VData c _) | c == ConsC || c == NilC -> list v
  VData _ fs -> allM (either (const (pure False)) forced) fs
  VUnit v -> forced v
  VChart _ -> pure True
  VClosure _ -> pure True
  VTyAbs{} -> pure True
  -- Every outcome of a mixture, as the printer shows them all (design §8.2).
  VMixture m -> allM (forced . (.value)) m.options
 where
  forcedElement = \case
    Right x -> True <$ evaluate x
    Left _ -> pure False
  -- Each item, then the rest; a rest whose samples differ in length is a
  -- mixture, each of whose options is forced in turn.
  list = \case
    VData NilC [] -> pure True
    VData ConsC [Right x, Right xs] -> forced x >>= \ok -> if ok then list xs else pure False
    VMixture m -> allM (list . (.value)) m.options
    _ -> pure False

-- | Each action in turn, while they succeed.
allM :: (a -> IO Bool) -> [a] -> IO Bool
allM f = \case
  [] -> pure True
  x : rest -> f x >>= \ok -> if ok then allM f rest else pure False

{- | The batches' values as one: the copies of each number concatenated in
batch order, and the outcomes of a mixture (design §8.2) merged by
outcome, each outcome's copies in batch order too, so that a value is the
same for every @cores@. 'Nothing' when they differ in any way but their
copies and outcomes, or hold a chart or a mixture of functions, which are
not merged; the input then runs as one evaluation.
-}
merged :: [(Batch, ValueOf Dbl)] -> Maybe (ValueOf Dbl)
merged bvs = mergedAt True [(VU.enumFromN b.first b.count, v) | (b, v) <- bvs]

{- | Values for disjoint sets of the copies, by global number, in batch
order, as one value for them all: on the nominal path, whose numbers'
IEEE values agree in every batch, or off it, where they mean nothing.
-}
mergedAt :: Bool -> [(VU.Vector Int, ValueOf Dbl)] -> Maybe (ValueOf Dbl)
mergedAt onNominal parts = case pieces of
  [] -> Nothing
  (_, _, v0) : _ -> case v0 of
    VTensor dims d hint xs0 -> do
      bufs <-
        traverse
          ( \case
              (_, _, VTensor dims' _ _ b) | dims' == dims && V.length b == V.length xs0 -> Just b
              _ -> Nothing
          )
          pieces
      VTensor dims d hint . V.fromList
        <$> traverse (element nominalNumbers) (transpose (map V.toList bufs))
    VUnit _ ->
      VUnit
        <$> ( mergedAt onNominal
                =<< traverse (\case (ms, _, VUnit v) -> Just (ms, v); _ -> Nothing) pieces
            )
    VCon{} -> do
      classes <- traverse classOf (grouped pieces)
      case classes of
        [(_, _, v)] -> Just v
        _ ->
          Just
            ( VMixture
                ( Mixture
                    (elemIndex True [n | (_, n, _) <- classes])
                    [Option ms v | (ms, _, v) <- classes]
                )
            )
    VClosure _ | length pieces == length parts -> Just v0
    VTyAbs{} | length pieces == length parts -> Just v0
    _ -> Nothing
 where
  pieces = concatMap explode parts
  explode (ms, v) = case v of
    VMixture m ->
      [ (o.members, onNominal && m.nominal == Just i, o.value)
      | (i, o) <- zip [0 :: Int ..] m.options
      ]
    _ -> [(ms, onNominal, v)]
  nominalNumbers = onNominal
  -- Data by constructor, in the order first met.
  grouped = foldl' place []
  place acc piece@(_, _, v) = case v of
    VCon c _ _
      | (before, (k, ps) : after) <- break ((== c) . fst) acc ->
          before ++ (k, ps ++ [piece]) : after
      | otherwise -> acc ++ [(c, [piece])]
    _ -> acc
  classOf (c, ps) = do
    let ms = VU.concat [m | (m, _, _) <- ps]
        nominal = or [n | (_, n, _) <- ps]
    fieldss <- traverse (\case (_, _, VCon _ fs _) -> Just fs; _ -> Nothing) ps
    case fieldss of
      fs0 : _ | all ((== length fs0) . length) fieldss -> do
        fields <- traverse (field nominal [m | (m, _, _) <- ps]) (transpose fieldss)
        Just (ms, nominal, VCon c fields (choiceOf c ps))
      _ -> Nothing
  field nominal mss ts = case sequence ts of
    Right vs -> Right <$> mergedAt nominal (zip mss vs)
    Left _ -> Left <$> failure ts
  -- Copies' own constructors, side by side where any has them.
  choiceOf (UserCon _ k) ps = case [cause | (_, _, VCon _ _ (Copied cause _ _)) <- ps] of
    [] -> NoCopies
    cause : _ ->
      Copied
        cause
        (IntSet.unions [l | (_, _, VCon _ _ (Copied _ l _)) <- ps])
        ( VU.concat
            [ case ch of
                Copied _ _ as -> as
                NoCopies -> VU.replicate (VU.length m) k
            | (m, _, VCon _ _ ch) <- ps
            ]
        )

{- | The error batches that failed give together: the @steps@ limit, if
any reached it; else their error, if all failed alike; else none, and the
batches do not merge.
-}
failure :: [Either EvalError a] -> Maybe EvalError
failure rs = case [e | Left e@(Exceeded Steps _) <- rs] of
  e : _ -> Just e
  [] -> case lefts rs of
    e : more | length more + 1 == length rs && all (== e) more -> Just e
    _ -> Nothing

-- | One element across the batches: all numbers, merged, or all errors.
element :: Bool -> [Either EvalError Dbl] -> Maybe (Either EvalError Dbl)
element onNominal es = case sequence es of
  Right xs -> Right <$> number onNominal xs
  Left _ -> Left <$> failure es

{- | One number across the batches: on the nominal path the same IEEE value
in each, bit for bit, off it the first's, which means nothing; and its
copies concatenated, carrying draws if any batch's do. A number without
copies (known exactly) is the same in each.
-}
number :: Bool -> [Dbl] -> Maybe Dbl
number onNominal = \case
  [] -> Nothing
  xs@(x0 : _)
    | onNominal && any ((/= bits x0.value) . bits . (.value)) xs -> Nothing
    | otherwise -> case traverse copies xs of
        Just css -> Just x0{estimate = Copies (foldMap fst css) (VU.concat (map snd css))}
        Nothing
          | all ((== x0.estimate) . (.estimate)) xs -> Just x0
          | otherwise -> Nothing
 where
  bits = castDoubleToWord64
  copies x = case x.estimate of
    Copies sp cs -> Just (sp, cs)
    ErrorBound _ -> Nothing
