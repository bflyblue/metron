{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Check and evaluate expressions with source diagnostics, without mutating a session.
module Metron.Compile (
  CheckedExpr (..),
  checkExpr,
  evalExpr,
  evalValue,
  evalValueAs,
  evalBatchedAs,
  evalChecked,
  openInValue,
  runtimeOf,
  renderResolveErrorWith,
  renderEvalError,
) where

import Control.Concurrent.Async (forConcurrently)
import Control.Exception (evaluate)
import Data.List (sortOn)
import Data.Map.Lazy qualified as LazyMap (map, mapWithKey)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (
  empty,
  findWithDefault,
  fromListWith,
  lookup,
  toList,
 )
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set qualified as Set (disjoint)
import Data.Text (Text)
import Data.Text qualified as T (intercalate, length, pack)
import Metron.Affine (Magnitude)
import Metron.Batch (acrossCopies, batchesOf, failure, forced, merged)
import Metron.Check (
  CheckError (CoreLintError, InferenceError),
  CheckedCore (inferred, linted, typed),
  checkCore,
 )
import Metron.Codebase (
  Codebase (derived, terms),
  Reference (Reference),
  chartNameFor,
  lookupTypeDef,
  unitNameFor,
 )
import Metron.Core (Hash, Nat (Z), Term, Vec (VNil), showHash)
import Metron.Desugar (
  DesugarError (BadSpecialForm, UnknownName),
  Provenance (ascriptions),
  desugarClosed,
  desugarMarked,
  fillOperands,
  provenanceAt,
 )
import Metron.Double (Dbl)
import Metron.Eval (
  Config (backend, batch, cores, limits, precision, samples),
  EvalError (..),
  RuntimeOf (..),
  Value,
  ValueOf,
  evalAt,
  evalDefinition,
  neededAtRuntime,
 )
import Metron.Hash (hashTerm)
import Metron.Infer qualified as I (
  TypeError (message, path),
  hasReadingMarkers,
  readingsOf,
  rewriteReadings,
 )
import Metron.Limits (limitHint, newBudget, remarksAfter, timedRemarksAfter)
import Metron.NameResolution (resolverFor)
import Metron.Needs (Needs, checkBackend, reachedBy)
import Metron.Pretty (Display, renderValue)
import Metron.Resolve (
  annotationsWith,
  ascriptionsIn,
  typeLookupFor,
  withHint,
 )
import Metron.Resolve.Error (ResolveError (..), renderResolveError)
import Metron.Scalar (Backend (..), Batch (..), Scalar)
import Metron.Session.Types (LastExpr (..))
import Metron.Source (printerFor, refNamer)
import Metron.Strictness (signatureAt, signatures, strictify)
import Metron.Syntax qualified as S (
  Expr (span),
  Name (span, text),
  Scope,
  renderSpanError,
 )
import Metron.TCore (TTerm)
import Metron.Type (
  Arg (AType),
  Scheme (..),
  Type (TData, TFun),
  VarId,
  freeVars,
  renderScheme,
  selfType,
 )
import Metron.UnitHint (Preferences)
import System.IO.Unsafe (unsafePerformIO)

data CheckedExpr = CheckedExpr
  { term :: Term Z
  , typed :: TTerm Z
  , scheme :: Maybe Scheme
  , linted :: [Scheme]
  }

-- | Type errors point into the input that defined the offending name.
renderResolveErrorWith :: Map Text Text -> Text -> ResolveError -> Text
renderResolveErrorWith sources src = \case
  TypeErrorIn n sp msg ->
    S.renderSpanError
      (Just (Map.findWithDefault src n.text sources))
      (fromMaybe n.span sp)
      ("in `" <> n.text <> "`: " <> msg)
  DuplicateDefinition n ->
    S.renderSpanError
      (Just src)
      n.span
      ("`" <> n.text <> "` is defined twice in the same group")
  Desugar (UnknownName sp n) -> S.renderSpanError (Just src) sp ("unknown name `" <> n <> "`")
  Desugar (BadSpecialForm sp msg) -> S.renderSpanError (Just src) sp msg
  DataError sp msg -> S.renderSpanError (Just src) sp msg
  SignatureError key sp msg ->
    S.renderSpanError (Just (Map.findWithDefault src key sources)) sp msg
  err@(LintFailure _ _) -> renderResolveError err

-- | Desugar, typecheck and elaborate, lint, evaluate, print.
evalExpr ::
  Config ->
  Preferences ->
  S.Scope ->
  Codebase ->
  Needs ->
  Text ->
  S.Expr ->
  Either Text (Text, LastExpr, Needs)
evalExpr cfg prefs scope cb memo src e = do
  (h, typed, le) <- prepared scope cb src e
  -- Refused before running if it reaches a built-in the backend lacks (design §8.2).
  let (verdict, memo') =
        checkBackend
          cfg.backend
          cfg.samples
          (\(r, i) -> refNamer scope cb r i "")
          cb.terms
          memo
          le.term
  either (Left . ("error: " <>)) Right verdict
  out <- case cfg.backend of
    AffineBackend -> evalShown @Magnitude cfg prefs scope cb h typed
    DoubleBackend
      -- The copies in parallel batches (design §8.2), unless the input reads
      -- across them or its batches do not merge.
      | cfg.samples > 0
      , length (batchesOf cfg.samples cfg.cores) > 1
      , Set.disjoint (fst (reachedBy cb.terms memo' le.term)) acrossCopies
      , Just batched <- batchedValue cfg cb h typed ->
          either
            (Left . renderEvalError)
            (uncurry (shown cfg scope cb prefs))
            batched
      | otherwise -> evalShown @Dbl cfg prefs scope cb h typed
  pure (out, le, memo')

-- | A value printed, with a line for each warning its evaluation made.
shown ::
  (Display s) =>
  Config ->
  S.Scope ->
  Codebase ->
  Preferences ->
  ValueOf s ->
  [Text] ->
  Either Text Text
shown cfg scope cb prefs v remarks = do
  out <-
    either
      (Left . renderEvalError)
      Right
      (renderValue (printerFor cfg scope cb) cfg.precision prefs v)
  pure (T.intercalate "\n" (out : map ("warning: " <>) remarks))

{- | The double backend's value with its copies evaluated in parallel
batches (design §8.2, "Metron.Batch"), each batch in its own thread and
its own runtime, then merged, with the batches' warnings together, or
the error they fail with together ('failure'). Each batch has the whole
@steps@ limit. 'Nothing' when the batches do not merge, and the input
should run as one evaluation.
-}
batchedValue ::
  Config ->
  Codebase ->
  Hash ->
  TTerm Z ->
  Maybe (Either EvalError (ValueOf Dbl, [Text]))
batchedValue cfg cb h typed = unsafePerformIO $ do
  -- A heap overflow or a timeout reaches this thread, and forConcurrently
  -- stops the batches; the further overflows they cause while stopping are
  -- taken in by runLimited.
  results <- forConcurrently (batchesOf cfg.samples cfg.cores) $ \b -> do
    let cfg' = cfg{batch = Just b}
        (rt, prepare) = runtimeWith @Dbl cfg' cb
    case evalAt cfg' rt h (prepare typed) of
      Left err -> pure (Left err)
      Right v -> do
        _ <- forced v
        remarks <- evaluate (timedRemarksAfter v rt.budget)
        _ <- evaluate (sum (map (T.length . snd) remarks))
        pure (Right (v, remarks))
  pure $ case sequence results of
    Left _ -> Left <$> failure results
    Right batches -> do
      v <- merged (map fst batches)
      -- Each warning at the first step any batch made it at: the order one
      -- evaluation makes them in.
      let firsts = Map.fromListWith min [(t, n) | (n, t) <- concatMap snd batches]
      Just (Right (v, map snd (sortOn fst [(n, t) | (t, n) <- Map.toList firsts])))
{-# NOINLINE batchedValue #-}

{- | 'evalValueAs' for the double backend with its copies in parallel
batches, as 'evalExpr' runs them, for the tests: 'Nothing' when the
batches do not merge.
-}
evalBatchedAs ::
  Config ->
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Maybe (Either EvalError (ValueOf Dbl)))
evalBatchedAs cfg scope cb src e = do
  (h, typed, _) <- prepared scope cb src e
  Right (fmap fst <$> batchedValue cfg cb h typed)

{- | Evaluate under the backend of the scalar type and print, with a line
for each warning the evaluation made: a branch lost in rounding (design
§8.2).
-}
evalShown ::
  forall s.
  (Display s) =>
  Config ->
  Preferences ->
  S.Scope ->
  Codebase ->
  Hash ->
  TTerm Z ->
  Either Text Text
evalShown cfg prefs scope cb h typed = do
  let (rt, prepare) = runtimeWith @s cfg cb
  v <- either (Left . renderEvalError) Right (evalAt cfg rt h (prepare typed))
  out <-
    either
      (Left . renderEvalError)
      Right
      (renderValue (printerFor cfg scope cb) cfg.precision prefs v)
  -- The warnings are read once the printing has evaluated the value.
  pure
    (T.intercalate "\n" (out : map ("warning: " <>) (remarksAfter out rt.budget)))

{- | Evaluate an expression. An expression typed at the prompt belongs to no
definition; its own hash stands in as the site of any @±@ in it (design
§3.2.4), so re-evaluating the same text gives the same nudges.
-}
evalValue ::
  Config -> S.Scope -> Codebase -> Text -> S.Expr -> Either Text (Hash, Value)
evalValue cfg scope cb src e = (\(h, v, _) -> (h, v)) <$> evalChecked cfg scope cb src e

-- | 'evalValue' under the backend of a scalar type (design §8.2).
evalValueAs ::
  forall s.
  (Scalar s) =>
  Config ->
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Hash, ValueOf s)
evalValueAs cfg scope cb src e = do
  (h, typed, _) <- prepared scope cb src e
  let (rt, prepare) = runtimeWith @s cfg cb
  (h,) <$> either (Left . renderEvalError) Right (evalAt cfg rt h (prepare typed))

-- | 'evalValue', keeping what was checked, to become @it@.
evalChecked ::
  Config ->
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Hash, Value, LastExpr)
evalChecked cfg scope cb src e = do
  (h, typed, le) <- prepared scope cb src e
  v <-
    let (rt, prepare) = runtimeWith cfg cb
     in either (Left . renderEvalError) Right (evalAt cfg rt h (prepare typed))
  pure (h, v, le)

{- | An expression checked for evaluation: its hash, its Typed Core and
what it leaves as @it@. A value whose shape or dimension nothing fixes is
refused here.
-}
prepared ::
  S.Scope -> Codebase -> Text -> S.Expr -> Either Text (Hash, TTerm Z, LastExpr)
prepared scope cb src e = do
  CheckedExpr term typed scheme linted <- checkExpr scope cb src e
  case scheme of
    Just sc
      | not (null (openInValue sc typed)) ->
          Left
            ( S.renderSpanError
                (Just src)
                e.span
                ( "ambiguous: nothing fixes the shape or dimension of this value, of type "
                    <> renderScheme sc
                    <> "; give an empty tensor a type, as in ([] :: Vec 0 m)"
                )
            )
    _ -> Right ()
  pure (hashTerm term, typed, LastExpr term linted typed cb)

{- | The length, shape and dimension variables an expression leaves open in
its value, outside any function, that its evaluation needs (design §3.3).
Nothing fixes them, so a value that needs one, an empty tensor alone
(@[]@ is @Tensor (0 : s) d@), has no shape or dimension to be built or
printed with. Inside a function they are the function's to receive, and
a value that never consults one, a constructor with no fields of a type
with a dimension parameter, is built without it. The typed term is the
expression's, abstracted over the scheme's variables.
-}
openInValue :: Scheme -> TTerm Z -> [VarId]
openInValue (Forall vs t) typed =
  [v | (v, k) <- vs, v `elem` inValue t, neededAtRuntime v k typed]
 where
  inValue = \case
    TFun _ _ -> []
    TData _ as -> concatMap inArg as
    ty -> map fst (freeVars ty)
  inArg = \case
    AType ty -> inValue ty
    a -> map fst (freeVars (TData selfType [a]))

{- | The runtime for one evaluation under a configuration. Every definition's
value is shared by all the references to it in that evaluation: a lazy
table over the codebase, each entry evaluated when first used, so that a
turned chart's rotation (design §3.8) is computed once and not once per
mention of the chart.
-}
runtimeOf :: (Scalar s) => Config -> Codebase -> RuntimeOf s
runtimeOf cfg cb = fst (runtimeWith cfg cb)

{- | 'runtimeOf', and how a term to evaluate against it is prepared: every
definition's Typed Core, and the expression's, with the arguments its
calls certainly evaluate marked ("Metron.Strictness"), each definition
analysed once per evaluation, when first used.
-}
runtimeWith ::
  (Scalar s) => Config -> Codebase -> (RuntimeOf s, TTerm Z -> TTerm Z)
runtimeWith cfg cb = (rt, strictify external)
 where
  rt =
    Runtime
      { typedOf = (`Map.lookup` analysed)
      , unitName = \h i written -> unitNameFor (Reference h i) written cb
      , chartName = \h i written -> chartNameFor (Reference h i) written cb
      , typeDefOf = (`lookupTypeDef` cb)
      , shared = (`Map.lookup` values)
      , budget =
          newBudget cfg.limits (cb, fmap (.first) cfg.batch)
      }
  analysed = LazyMap.map (strictify external . snd) cb.derived
  known = LazyMap.map (signatures external . snd) cb.derived
  external h mi = Map.lookup h known >>= (`signatureAt` mi)
  values = LazyMap.mapWithKey (evalDefinition cfg rt) analysed

{- | Desugar, typecheck, elaborate and lint an expression against a codebase.
Returns the Core, the Typed Core, the inferred type and the types lint
found, which are what a stored term carries.
-}
checkExpr ::
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text CheckedExpr
checkExpr scope cb src e = do
  (term, prov) <-
    either
      (Left . renderResolveErrorWith Map.empty src . Desugar)
      Right
      (desugarClosed (resolverFor scope cb) e)
  -- Uses of signed names see their signatures, and ascriptions narrow
  -- (design §4.8): with any, the term inferred is the one desugared with
  -- their markers, while the term hashed and kept stays the plain one.
  (checkTerm, checkProv) <-
    if null prov.ascriptions
      then Right (term, prov)
      else
        either
          (Left . renderResolveErrorWith Map.empty src . Desugar)
          Right
          (desugarMarked "" "" (resolverFor scope cb) VNil e)
  asc <-
    either
      (Left . renderResolveErrorWith Map.empty src)
      Right
      (ascriptionsIn scope cb Map.empty [] checkProv)
  -- The readings the types choose (design §3.10, U4, U6), written into both
  -- terms: their markers are named alike.
  chosen <-
    if I.hasReadingMarkers checkTerm
      then
        either
          (Left . typeErr checkProv)
          Right
          (I.readingsOf (annotationsWith cb asc) (typeLookupFor cb) checkTerm)
      else Right Map.empty
  let read' = I.rewriteReadings chosen
  checked <-
    either
      ( Left . \case
          InferenceError err -> typeErr checkProv err
          CoreLintError err -> "internal error: elaboration produced ill-typed core: " <> err
      )
      Right
      (checkCore (annotationsWith cb asc) (typeLookupFor cb) (read' checkTerm))
  let schemes = checked.inferred
      typed = checked.typed
      linted = checked.linted
  pure (CheckedExpr (read' term) typed (listToMaybe schemes) linted)
 where
  typeErr prov err = case provenanceAt err.path prov of
    Just (sp, hint) ->
      S.renderSpanError
        (Just src)
        sp
        (withHint hint (fillOperands err.path prov err.message))
    Nothing -> S.renderSpanError (Just src) e.span (fillOperands err.path prov err.message)

renderEvalError :: EvalError -> Text
renderEvalError = \case
  DivideByZero -> "error: division by zero"
  Domain msg -> "error: " <> msg
  Undecided msg -> "error: cannot decide " <> msg
  Internal msg -> "internal error: " <> msg
  UnknownRef h -> "error: unknown reference " <> showHash h
  BadCycleIndex i -> "error: bad cycle index " <> T.pack (show i)
  Unsupported msg -> "not implemented: " <> msg
  Exceeded l msg -> "error: " <> msg <> limitHint l
  ChartStep name why ->
    "error: "
      <> maybe "a chart" ("chart " <>) name
      <> " has no invertible coordinates: "
      <> why
