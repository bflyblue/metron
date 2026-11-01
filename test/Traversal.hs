{- | The walks over Core (core.md §7), all built on 'traverseChildren',
checked by their laws on generated terms of every shape. Terms are
compared by 'show', which unlike 'alphaEq' sees the hints.
-}
module Traversal (
  traversalTests,
  blankHints,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Any (..), Sum (..))
import Data.Set qualified as Set
import Gen (Depth (..), SomeTerm (..), coreHashes, genCoreTerm, genSomeTerm)
import Metron.Core
import Metron.Infer (rewriteReadings)
import Metron.Update (restampTerm)
import Test.Tasty
import Test.Tasty.QuickCheck

traversalTests :: TestTree
traversalTests =
  localOption (mkTimeout 60_000_000)
    $ testGroup
      "traversal"
      [ testProperty "mapChildren id is the identity" $ anyTerm $ \t ->
          show (mapChildren id t) === show t
      , testProperty "children are the subterms foldChildren visits" $ anyTerm $ \t ->
          length (children t) === getSum (foldChildren (const (Sum 1)) t)
      , testProperty "rewriteRefs rewrites exactly the references the map names"
          $ forAll genRefMap
          $ \m -> anyTerm $ \t ->
            let f h i = Map.lookup (h, i) m
             in cover 20 (hits m t) "a reference rewritten"
                  $ refsWithIndex (rewriteRefs f t)
                    === Set.map (\r -> fromMaybe r (Map.lookup r m)) (refsWithIndex t)
      , testProperty "rewriteRefs with nothing to rewrite is the identity" $ anyTerm $ \t ->
          show (rewriteRefs (\_ _ -> Nothing) t) === show t
      , testProperty "inlineRef leaves no reference to its target"
          $ forAll (elements coreHashes)
          $ \target -> forAll (sized (genCoreTerm DZ . min 10)) $ \r -> anyTerm $ \t ->
            let inlined :: Term m -> Bool
                inlined = Set.member (target, Nothing) . refsWithIndex
             in not (inlined r)
                  ==> cover 5 (inlined t) "a reference inlined"
                  $ not (inlined (inlineRef target r t))
      , testProperty "weakening by nothing is the identity" $ anyTerm $ \t ->
          show (weakenBy VNil t) === show t
      , testProperty "a closed term weakened is the same term"
          $ forAll (sized (genCoreTerm DZ . min 40))
          $ \t -> show (weakenBy (VCons () (VCons () VNil)) t) === show t
      , testProperty "restamping with identities is the identity" $ anyTerm $ \t ->
          show (restampTerm id id t) === show t
      , testProperty "rewriting no readings is the identity" $ anyTerm $ \t ->
          show (rewriteReadings Map.empty t) === show t
      , testProperty "blanking hints keeps the term" $ anyTerm $ \t ->
          alphaEq (blankHints t) t
      ]

-- | A property of a term in any scope, with its shapes counted.
anyTerm :: (Testable p) => (forall n. Term n -> p) -> Property
anyTerm p = forAll genSomeTerm $ \(SomeTerm _ t) ->
  checkCoverage
    . cover 10 (has isCycle t) "a cycle"
    . cover 10 (has isFieldAlt t) "an alternative with fields"
    . cover 10 (has isVar t) "a variable"
    . cover 10 (size t >= 50) "fifty nodes or more"
    $ p t
 where
  size :: Term n -> Int
  size = getSum . foldTerm (const (Sum 1))
  has :: (forall m. Term m -> Bool) -> Term n -> Bool
  has q = getAny . foldTerm (Any . q)
  isCycle, isFieldAlt, isVar :: Term m -> Bool
  isCycle = \case
    Cycle{} -> True
    _ -> False
  isFieldAlt = \case
    Case _ alts -> or [vecLength hs > 0 | Alt _ hs _ <- alts]
    _ -> False
  isVar = \case
    Var _ -> True
    _ -> False

genRefMap :: Gen (Map (Hash, Maybe Int) (Hash, Maybe Int))
genRefMap = Map.fromList <$> listOf ((,) <$> ref <*> ref)
 where
  ref = (,) <$> elements coreHashes <*> elements [Nothing, Just 0, Just 1, Just 2]

-- | Whether a rewrite map changes a reference the term makes.
hits :: Map (Hash, Maybe Int) a -> Term n -> Bool
hits m t = any (`Map.member` m) (Set.toList (refsWithIndex t))

-- | Every hint replaced by a fixed one: alpha-equivalent to the input.
blankHints :: Term n -> Term n
blankHints = go
 where
  go :: Term m -> Term m
  go = \case
    Lam _ b -> Lam "q" (go b)
    Let _ e b -> Let "q" (go e) (go b)
    Cycle hs bs -> Cycle (vecMap (const "q") hs) (vecMap go bs)
    t -> mapChildren go t
