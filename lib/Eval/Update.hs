{- | Propagating a new version to its dependents (design §7.5).

Given a map from old references to new ones, every current definition
whose term mentions an old reference is rewritten to the new one,
re-typechecked, re-hashed, stored, and its names re-bound, in dependency
order so that each dependent is rewritten once. A dependent whose rewritten
term no longer typechecks is left on the old version and reported.
-}
module Eval.Update (
  RefMap,
  Propagation (..),
  propagate,
  staleReferences,
) where

import Data.Graph (flattenSCC, stronglyConnComp)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Eval.Codebase
import Eval.Core
import Eval.Hash (hashTerm)
import Eval.Infer

type RefMap = Map Reference Reference

data Propagation = Propagation
  { codebase :: Codebase
  , upgraded :: [(Text, Reference, Reference)]
  -- ^ name, old, new
  , skipped :: [(Text, Reference, Text)]
  -- ^ name, its current ref, why it stayed
  }

propagate :: RefMap -> Codebase -> Propagation
propagate initial cb0 = go cb0 initial (Propagation cb0 [] []) affectedInOrder
 where
  initialHashes = Set.fromList (map (.hash) (Map.keys initial))

  -- Hashes of current definitions that mention an old reference, directly
  -- or through another affected definition.
  affected = Set.difference (closure initialHashes) initialHashes
  closure olds =
    let hs =
          Set.fromList
            [ h
            | Reference h _ <- Map.elems cb0.names
            , Just t <- [lookupTerm h cb0]
            , mentionsAny olds t
            ]
        olds' = Set.union olds hs
     in if olds' == olds then olds else closure olds'
  mentionsAny olds t = any (\(h, _) -> h `Set.member` olds) (Set.toList (refsWithIndex t))

  -- Dependencies first.
  affectedInOrder =
    concatMap
      flattenSCC
      ( stronglyConnComp
          [ ( h
            , h
            , [d | (d, _) <- Set.toList (refsWithIndex t), d `Set.member` affected, d /= h]
            )
          | h <- Set.toList affected
          , Just t <- [lookupTerm h cb0]
          ]
      )

  go cb _ acc [] =
    acc
      { codebase = cb
      , upgraded = reverse acc.upgraded
      , skipped = reverse acc.skipped
      }
  go cb refmap acc (h : hs) = case lookupTerm h cb of
    Nothing -> go cb refmap acc hs
    Just t ->
      let t' =
            rewriteRefs
              ( \rh ri -> (\(Reference nh ni) -> (nh, ni)) <$> Map.lookup (Reference rh ri) refmap
              )
              t
          holders = [(n, i) | (n, Reference rh i) <- Map.toList cb.names, rh == h]
       in case elaborateClosed (\k -> lookupTypes k cb) t' of
            Left err ->
              go
                cb
                refmap
                acc
                  { skipped = [(n, Reference h i, err.message) | (n, i) <- holders] ++ acc.skipped
                  }
                hs
            Right (schemes, typed) ->
              let h' = hashTerm t'
                  renamed = [(n, Reference h i, Reference h' i) | (n, i) <- holders]
                  refmap' = foldr (\(_, old, new) -> Map.insert old new) refmap renamed
                  rebind (n, _, new) acc' = bindName n new acc'
                  cb' = foldr rebind (addTerm h' t' schemes typed cb) renamed
               in go cb' refmap' acc{upgraded = reverse renamed ++ acc.upgraded} hs

{- | References in current definitions that a name once pointed at but no
longer does, with nothing else naming them: the work `:upgrade` would do.
Each entry is (dependent, stale reference, the name that moved on).
-}
staleReferences :: Codebase -> [(Text, Reference, Text)]
staleReferences cb =
  [ (n, r, m)
  | (n, Reference h _) <- Map.toList cb.names
  , Just t <- [lookupTerm h cb]
  , (rh, ri) <- Set.toList (refsWithIndex t)
  , let r = Reference rh ri
  , null (namesOf r cb)
  , m <- historicalNamesOf r cb
  ]
