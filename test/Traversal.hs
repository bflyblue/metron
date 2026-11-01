{- | The walks over Core (core.md §7): each built on 'traverseChildren',
checked on generated terms of every shape.
-}
module Traversal (
  traversalTests,
  blankHints,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Monoid (Any (..), Sum (..))
import Data.Set qualified as Set
import Gen (
  Depth (..),
  SomeTerm (..),
  coreHashes,
  genCoreTerm,
  genSomeTerm,
  scopeNames,
 )
import Metron.Branch (Inside (..), child, childNew)
import Metron.Core
import Metron.Infer (
  hasReadingMarkers,
  hasReadingMarkersNew,
  rewriteReadings,
  rewriteReadingsNew,
 )
import Metron.Update (restampTerm, restampTermNew)
import Test.Tasty
import Test.Tasty.QuickCheck

traversalTests :: TestTree
traversalTests = testGroup "traversal" [agreement]

{- | Each walk on the traversal against the hand-written walk it replaces,
compared by 'show', which unlike 'alphaEq' sees the hints.
-}
agreement :: TestTree
agreement =
  testGroup
    "agree"
    [ testProperty "conTypes" $ anyTerm $ \t -> conTypes t === conTypesNew t
    , testProperty "refsWritten" $ anyTerm $ \t -> refsWritten t === refsWrittenNew t
    , testProperty "directUses"
        $ anyTerm
        $ \t ->
          let picked = (`elem` ["add", "±", "gauss", "§to:1"])
           in directUses picked t === directUsesNew picked t
    , testProperty "rewriteRefs"
        $ forAll genRefMap
        $ \m -> anyTerm $ \t ->
          let f h i = Map.lookup (h, i) m
           in cover 20 (hits m t) "a reference rewritten"
                $ show (rewriteRefs f t) === show (rewriteRefsNew f t)
    , testProperty "rewriteRefsWritten"
        $ forAll genRefMap
        $ \m -> anyTerm $ \t ->
          let f h i w = if w == "a" then Nothing else Map.lookup (h, i) m
           in cover 20 (hits m t) "a reference rewritten"
                $ show (rewriteRefsWritten f t) === show (rewriteRefsWrittenNew f t)
    , testProperty "inlineRef"
        $ forAll (elements coreHashes)
        $ \target -> forAll (sized (genCoreTerm DZ . min 10)) $ \r -> anyTerm $ \t ->
          cover 5 (Set.member (target, Nothing) (refsWithIndex t)) "a reference inlined"
            $ show (inlineRef target r t) === show (inlineRefNew target r t)
    , testProperty "weakenBy" $ forAll (choose (0, 3)) $ \k -> anyTerm $ \t ->
        case vecFromList (replicate k ()) of
          SomeVec ks -> show (weakenBy ks t) === show (weakenByNew ks t)
    , testProperty "renameTerm" $ anyTerm $ \t ->
        show (renameTerm FS t) === show (renameTermNew FS t)
    , testProperty "closedIn" $ forAll (sized (genCoreTerm DZ . min 40)) $ \t ->
        show (closedIn t :: Term (S (S Z))) === show (closedInNew t :: Term (S (S Z)))
    , testProperty "rewriteReadings" $ anyTerm $ \t ->
        cover 1 (swaps t) "a point's reading, its arguments swapped"
          $ show (rewriteReadings chosen t) === show (rewriteReadingsNew chosen t)
    , testProperty "hasReadingMarkers" $ anyTerm $ \t ->
        hasReadingMarkers t === hasReadingMarkersNew t
    , testProperty "restampTerm" $ anyTerm $ \t ->
        show (restampTerm relabel recon t) === show (restampTermNew relabel recon t)
    , testProperty "child" $ forAll genSomeTerm $ \(SomeTerm d t) ->
        let ctx = scopeNames d
         in conjoin
              [ describe (child (Inside ctx t) i) === describe (childNew (Inside ctx t) i)
              | i <- [0 .. length (children t) + 1]
              ]
    , testProperty "blankHints" $ anyTerm $ \t ->
        show (blankHints t) === show (blankHintsNew t)
    ]
 where
  chosen = Map.fromList [("§quantity:0", "pointOn"), ("§to:1", "toChart")]
  swaps :: Term n -> Bool
  swaps =
    getAny
      . foldTerm
        ( \case
            PrimApp "§quantity:0" [_, _] -> Any True
            _ -> mempty
        )
  relabel = \case
    Owner o -> Owner (o <> "'")
    FrameLabel f moving -> FrameLabel f (not moving)
    l -> l
  recon (UserCon h i) = UserCon h (i + 1)
  describe = fmap (\(Inside ctx t) -> (vecToList ctx, show t))

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
    Var i -> Var i
    Ref hh i hint -> Ref hh i hint
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam _ b -> Lam "q" (go b)
    App f a -> App (go f) (go a)
    Let _ e b -> Let "q" (go e) (go b)
    Con c as -> Con c (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt c hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k l n
    Uncertain k l x e -> Uncertain k l (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle (vecMap (const "q") hs) (vecMap go bs)

blankHintsNew :: Term n -> Term n
blankHintsNew = go
 where
  go :: Term m -> Term m
  go = \case
    Lam _ b -> Lam "q" (go b)
    Let _ e b -> Let "q" (go e) (go b)
    Cycle hs bs -> Cycle (vecMap (const "q") hs) (vecMap go bs)
    t -> mapChildren go t
