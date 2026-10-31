-- | Check and evaluate expressions with source diagnostics, without mutating a session.
module Eval.Compile (
  CheckedExpr (..),
  checkExpr,
  evalExpr,
  evalValue,
  evalChecked,
  openInValue,
  runtimeOf,
  renderResolveErrorWith,
  renderEvalError,
) where

import Data.Map.Strict ( Map )
import Data.Maybe ( fromMaybe, listToMaybe )
import Data.Text ( Text )
import Eval.Check
    ( checkCore,
      CheckError(CoreLintError, InferenceError),
      CheckedCore(inferred, linted, typed) )
import Eval.Codebase
    ( chartNameFor,
      lookupTypeDef,
      lookupTyped,
      unitNameFor,
      Codebase(derived),
      Reference(Reference) )
import Eval.Core ( showHash, Hash, Nat(Z), Term, Vec(VNil) )
import Eval.Desugar
    ( desugarClosed,
      desugarMarked,
      fillOperands,
      provenanceAt,
      DesugarError(BadSpecialForm, UnknownName),
      Provenance(ascriptions) )
import Eval.UnitHint ( Preferences )
import Eval.Eval ( evalAt, evalDefinition, neededAtRuntime, Config(precision), EvalError(..), Runtime(..), Value )
import Eval.Hash ( hashTerm )
import Eval.Pretty ( renderValue )
import Eval.Resolve.Error ( renderResolveError, ResolveError(..) )
import Eval.NameResolution ( resolverFor )
import Eval.Resolve ( annotationsWith, ascriptionsIn, typeLookupFor, withHint )
import Eval.Session.Types ( LastExpr(LastExpr) )
import Eval.Source ( printerFor )
import Eval.TCore ( TTerm )
import Eval.Type
    ( freeVars,
      selfType,
      Arg(AType),
      Scheme(..),
      Type(TData, TFun),
      VarId,
      renderScheme )
import Eval.Infer qualified as I
    ( hasReadingMarkers,
      readingsOf,
      rewriteReadings,
      TypeError(message, path) )
import Data.Map.Lazy qualified as LazyMap ( mapWithKey )
import Data.Map.Strict qualified as Map
    ( empty, lookup, findWithDefault )
import Eval.Syntax qualified as S
    ( renderSpanError, Expr(span), Name(span, text), Scope )
import Data.Text qualified as T ( pack )

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
  Text ->
  S.Expr ->
  Either Text (Text, LastExpr)
evalExpr cfg prefs scope cb src e = do
  (_, v, le) <- evalChecked cfg scope cb src e
  out <-
    either
      (Left . renderEvalError)
      Right
      (renderValue (printerFor cfg scope cb) cfg.precision prefs v)
  pure (out, le)

{- | Evaluate an expression. An expression typed at the prompt belongs to no
definition; its own hash stands in as the site of any @±@ in it (design
§3.2.4), so re-evaluating the same text gives the same nudges.
-}
evalValue ::
  Config -> S.Scope -> Codebase -> Text -> S.Expr -> Either Text (Hash, Value)
evalValue cfg scope cb src e = (\(h, v, _) -> (h, v)) <$> evalChecked cfg scope cb src e

-- | 'evalValue', keeping what was checked, to become @it@.
evalChecked ::
  Config ->
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Hash, Value, LastExpr)
evalChecked cfg scope cb src e = do
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
  let h = hashTerm term
  v <-
    either (Left . renderEvalError) Right (evalAt cfg (runtimeOf cfg cb) h typed)
  pure (h, v, LastExpr term linted typed cb)

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
runtimeOf :: Config -> Codebase -> Runtime
runtimeOf cfg cb = rt
 where
  rt =
    Runtime
      { typedOf = (`lookupTyped` cb)
      , unitName = \h i written -> unitNameFor (Reference h i) written cb
      , chartName = \h i written -> chartNameFor (Reference h i) written cb
      , typeDefOf = (`lookupTypeDef` cb)
      , shared = (`Map.lookup` values)
      }
  values = LazyMap.mapWithKey (\h (_, t) -> evalDefinition cfg rt h t) cb.derived

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
      (Left . \case
        InferenceError err -> typeErr checkProv err
        CoreLintError err -> "internal error: elaboration produced ill-typed core: " <> err)
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
  ChartStep name why ->
    "error: "
      <> maybe "a chart" ("chart " <>) name
      <> " has no invertible coordinates: "
      <> why
