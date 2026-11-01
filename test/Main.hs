module Main (main) where

import Astro (astroTests)
import Backend (backendTests)
import Lang.Affine (affineTests)
import Lang.Charts (
  movingChartTests,
  rotationTests,
  turnedChartTests,
 )
import Lang.Codebase (codebaseTests, itTests, namespaceTests)
import Lang.Core (coreTests, evalTests, hashTests, tcoreTests)
import Lang.Data (dataTests)
import Lang.EndToEnd (endToEndTests, soundnessTests)
import Lang.Frames (axisSlotTests, namedAxesTests, partFTests)
import Lang.Library (preludeTests, stdlibTests)
import Lang.Properties (propertyTests)
import Lang.Repl (replTests)
import Lang.Store (editTests, storeTests)
import Lang.Syntax (
  desugarTests,
  lexerTests,
  parserTests,
  prettyTests,
  respellTests,
 )
import Lang.Tensors (contractionTests, productTests, sliceTests)
import Lang.Types (
  annotationTests,
  dimensionSyntaxTests,
  forallTests,
  lintRegressionTests,
  roleTests,
  typeTests,
 )
import Lang.Units (
  displayTests,
  partUTests,
  readingTests,
  unitTests,
 )
import Limits (limitTests, measure)
import Operators (operatorTests)
import Precision (precisionTests)
import Test.Tasty (
  defaultMain,
  localOption,
  mkTimeout,
  testGroup,
 )
import Traversal (traversalTests)

{- | Every test has a five-minute limit as a backstop to 'caseLimit', which
times each generated case but not the generator itself: the whole suite
normally runs in seconds, so a test that reaches it has hung. What the
limits tests measure of the heap runs first, on the main thread ("Limits").
-}
main :: IO ()
main = do
  measured <- measure
  defaultMain
    . localOption (mkTimeout 300_000_000)
    $ testGroup
      "metron"
      [ coreTests
      , traversalTests
      , evalTests
      , tcoreTests
      , lexerTests
      , parserTests
      , desugarTests
      , hashTests
      , prettyTests
      , operatorTests
      , endToEndTests
      , codebaseTests
      , typeTests
      , soundnessTests
      , productTests
      , contractionTests
      , sliceTests
      , rotationTests
      , turnedChartTests
      , movingChartTests
      , axisSlotTests
      , namedAxesTests
      , propertyTests
      , unitTests
      , lintRegressionTests
      , preludeTests
      , displayTests
      , affineTests
      , storeTests
      , dataTests
      , itTests
      , respellTests
      , replTests
      , backendTests
      , namespaceTests
      , editTests
      , stdlibTests
      , limitTests measured
      , annotationTests
      , forallTests
      , dimensionSyntaxTests
      , readingTests
      , partUTests
      , partFTests
      , roleTests
      , astroTests
      , precisionTests
      ]
