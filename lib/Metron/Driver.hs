{-# LANGUAGE PatternSynonyms #-}

{- | Runs source text through the whole pipeline for the CLI and the tests
(design §7.3, §7.5).

Definitions typed at the prompt or read from a file go into the
**scratch**: they are desugared, typechecked, hashed and usable by
expressions, but not stored. @:add@ and @:update@ move them into the
codebase; @:update@ also propagates the new versions to the dependents
that still typecheck.
-}
module Metron.Driver (
  Session (..),
  LastExpr (..),
  emptySession,
  seededSession,
  startBackend,
  setSetting,
  startSettings,
  stdlibUpgrade,
  feed,
  feedFile,
  exportRequest,
  exportSource,
  EditScope (..),
  EditRequest (..),
  editRequest,
  editScopeArgs,
  editorNote,
  applyEdit,
  refreshPreferences,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.List (partition, sortOn)
import Data.Map.Strict qualified as Map (
  Map,
  delete,
  empty,
  fromList,
  fromListWith,
  insert,
  keys,
  member,
  toList,
  union,
 )
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import Data.Set qualified as Set (
  fromList,
  member,
  null,
  singleton,
  toList,
  union,
 )
import Data.Text (Text)
import Data.Text qualified as T (
  any,
  breakOn,
  drop,
  intercalate,
  isInfixOf,
  isPrefixOf,
  isSuffixOf,
  length,
  null,
  pack,
  splitOn,
  strip,
  stripPrefix,
  stripStart,
  takeWhile,
  toLower,
  unpack,
  unwords,
  words,
 )
import Data.Vector qualified as V (fromList, take, toList)
import Metron.Affine (Collapsed (..), Magnitude (..), addM, collapse)
import Metron.Builtin (frameDefMoving, pairC, pattern TupleC)
import Metron.Codebase (
  Codebase (
    conNames,
    derived,
    fieldNames,
    names,
    preferences,
    terms,
    typeDefs,
    typeNames,
    uses
  ),
  Reference (Reference, hash),
  addPreference,
  addStoredUse,
  addTerm,
  bindConName,
  bindFieldName,
  bindName,
  bindTypeName,
  clearFlags,
  conNameOf,
  dependents,
  fieldNamesOf,
  findByPrefix,
  historicalNamesOf,
  historyOf,
  isChartName,
  isUnitName,
  lookupConName,
  lookupFieldName,
  lookupName,
  lookupTerm,
  lookupTypeDef,
  lookupTypeName,
  lookupTyped,
  markChart,
  markUnit,
  removePreference,
  removeStoredUse,
  showReference,
  signatureOf,
  typeOf,
  unbindName,
 )
import Metron.Command (commandHelp)
import Metron.Compile (
  CheckedExpr (CheckedExpr),
  checkExpr,
  evalExpr,
  evalValue,
  renderEvalError,
  renderResolveErrorWith,
 )
import Metron.Core (
  ConRef (UserCon),
  Term (Cycle),
  inlineRef,
  refs,
  showHash,
  vecLength,
 )
import Metron.Desugar (DesugarError (UnknownName))
import Metron.Dimension (dimMul, dimPow, renderDimIn)
import Metron.Edit (
  EditRequest (..),
  EditScope (..),
  applyEdit,
  editRequest,
  editScopeArgs,
  editorNote,
 )
import Metron.Eval (
  Config (..),
  EvalError (Internal),
  ValueOf (VData, VTensor),
  covarianceMatrix,
  precisionOf,
 )
import Metron.Hash (hashTerm)
import Metron.Infer qualified as I (
  TypeError (message),
  elaborateClosed,
  matchesQuery,
 )
import Metron.Limits (Limits (digits), setLimit, settingLines)
import Metron.NameResolution (
  LabelKind (FieldLabel, TypeLabel),
  Qualified (Found),
  disjointness,
  isNamespace,
  namespaceLabels,
  qualifyName,
  qualifyWith,
  shortestName,
  shortestNameOf,
 )
import Metron.Parser (parseExprWithin, parseProgramWithin, parseType)
import Metron.Prelude (isLibraryPath, stdlibCodebase)
import Metron.Pretty (
  Printer (refName),
  displayParts,
  renderBudget,
  renderExact,
  renderRough,
  renderValue,
  renderValueWith,
  respell,
 )
import Metron.Resolve (processGroup, typeLookupFor)
import Metron.Resolve.Error (ResolveError (Desugar), renderResolveError)
import Metron.Scalar (
  Backend (..),
  backendName,
  backendNamed,
  roundingName,
  roundingNamed,
 )
import Metron.Session.Names (
  argPath,
  argPaths,
  labelKinds,
  labelNoun,
  labelsText,
  namespaceLine,
  relabel,
  removeLabel,
 )
import Metron.Session.Preferences (
  preferenceHint,
  refreshPreferences,
 )
import Metron.Session.Types (
  LastExpr (..),
  Session (..),
  emptySession,
 )
import Metron.Source (
  definitionLine,
  exportRequest,
  exportSource,
  nameTypes,
  printerFor,
  refNamer,
  signatureLine,
  spellingOf,
  upgradeReport,
  viewData,
  viewTyped,
 )
import Metron.Syntax qualified as S (
  Binding (name),
  DataDecl (name),
  Decl (..),
  Name (span, text),
  Pos (Pos),
  Scope (namespace, uses),
  Span (Span),
  Use (Use, alias, path),
  declKey,
  flatten,
  isSignature,
  lastSegment,
  qualify,
  renderSpanError,
  renderUse,
 )
import Metron.TCore (lintClosed)
import Metron.Type (
  Scheme (Forall),
  Type (TData, TFun),
  TypeDef (constructors, params),
  dataConstructors,
  defaultAxes,
  renderForallIn,
  renderScheme,
  renderTypeDef,
  varArg,
 )
import Metron.Type.Syntax (queryScheme)
import Metron.UnitHint (UnitHint (pinned), hintPow, hintProduct)
import Metron.Update (
  Propagation (Propagation, codebase, skipped, upgraded),
  Restamped (codebase, terms, types),
  propagateNamed,
  restamp,
  staleReferences,
 )

{- | A session on a seeded codebase (design §7.7): the standard library
entered by domain as one group and added, with its six stored default
@use@s, as a new codebase starts and as @--no-codebase@ runs. Fails only if
the library itself does not check, which is a build error.
-}

{- | A session under the named backend (design §8.2), as @:backend NAME@
leaves it: what @metron --backend NAME@ starts with.
-}
startBackend :: Text -> Session -> Either Text Session
startBackend name session = case backendNamed name of
  Just b -> Right session{config = session.config{backend = b}}
  Nothing -> Left (noBackend name)

noBackend :: Text -> Text
noBackend name = "no backend " <> name <> "; the backends are affine and double"

seededSession :: Either Text Session
seededSession = do
  cb <- stdlibCodebase
  pure emptySession{codebase = cb, staging = cb}

{- | Parse and run one input (a REPL input, a file). Returns the new session and
the lines to print, or the first error.
-}
feed :: Session -> Text -> Either Text (Session, [Text])
feed session src = case feed' session src of
  -- Declared types print by hash below here; the session names them (design §7.2).
  Left err -> Left (nameTypes session.scope session.staging err)
  Right (session', outs) ->
    Right (session', echo ++ map (nameTypes session'.scope session'.staging) outs)
 where
  -- With unicode on, a statement line is echoed in its unicode spelling
  -- (design §7.3). A file is not: it is many lines.
  line = T.strip src
  echo =
    [ "  ≡ " <> spelled
    | session.config.unicode
    , not (":" `T.isPrefixOf` line)
    , not (T.any (== '\n') line)
    , Just spelled <- [respell line]
    ]

feed' :: Session -> Text -> Either Text (Session, [Text])
feed' session src
  | Just cmd <- T.stripPrefix ":" (T.stripStart src) =
      command session src (T.words cmd)
  | otherwise = do
      stmts <- parseProgramWithin session.config.limits.digits src
      -- Namespaces flattened (design §7.6): full paths, each with its scope.
      -- The top-level `use`s last for the session.
      let (decls, exprs, scope') = S.flatten session.scope stmts
      (session', notes) <-
        if null decls then Right (session, []) else propose session src decls
      -- Each expression that evaluates becomes `it` for the next one.
      let step (s, outs) (scope, e) = do
            (out, le, needs) <-
              evalExpr s.config s.preferred scope (exprCodebase s) s.needs src e
            le' <- absorbLast s le
            pure (s{lastExpr = Just le', needs}, out : outs)
      (session'', outs) <- foldM step (session', []) exprs
      pure (session''{scope = scope'}, notes ++ reverse outs)

{- | A file read with @:load@: one input, whose top-level @use@s last for
the file only (design §7.6), not for the session.
-}
feedFile :: Session -> Text -> Either Text (Session, [Text])
feedFile session src = do
  (session', outs) <- feed session src
  pure (session'{scope = session.scope}, outs)

{- | What expressions and inspection commands resolve names against: the
staging codebase with @it@ bound to the last expression (design §7.3). It
is built on the fly and never becomes the staging codebase, so @it@ never
reaches the codebase or the store.
-}
exprCodebase :: Session -> Codebase
exprCodebase session = case session.lastExpr of
  Nothing -> session.staging
  Just le ->
    let h = hashTerm le.term
        cb = session.staging
        -- What the expression referenced stays reachable, by content, even
        -- if the scratch that defined it has changed since.
        withBase =
          cb
            { terms = Map.union cb.terms le.base.terms
            , derived = Map.union cb.derived le.base.derived
            , typeDefs = Map.union cb.typeDefs le.base.typeDefs
            }
     in clearFlags
          "it"
          ( bindName
              "it"
              (Reference h Nothing)
              (addTerm h le.term le.schemes le.typed withBase)
          )

{- | Put definitions into the scratch. A name already pending is replaced
(the scratch is a workspace, not a scope); a name defined twice in one
input is an error. The whole scratch is re-entered on top of the codebase
so that errors surface now.
-}
propose :: Session -> Text -> [S.Decl] -> Either Text (Session, [Text])
propose session src decls = do
  -- A name's signature and its definition are two entries (design §4.8):
  -- a new signature replaces a pending one, a new definition a pending one.
  let incoming = map S.declKey decls
      (replaced, kept) = partition (\b -> S.declKey b `elem` incoming) session.scratch
      scratch' = kept ++ decls
      sources' = foldr (\b -> Map.insert (S.declKey b) src) session.sources decls
  -- `it` is session-local (design §7.5): it is neither defined nor stored.
  case [b.name | S.DBind _ b <- decls, b.name.text == "it"] of
    n : _ ->
      Left
        ( S.renderSpanError
            (Just src)
            n.span
            "`it` is the last result and cannot be defined; choose another name"
        )
    [] -> Right ()
  staging' <-
    either
      (Left . renderProposeError sources')
      Right
      (processGroup session.codebase scratch')
  let notes =
        [ "replaced pending "
            <> (if S.isSignature b then "signature" else "definition")
            <> " of `"
            <> b.name.text
            <> "`"
        | b <- replaced
        ]
  pure
    (session{scratch = scratch', sources = sources', staging = staging'}, notes)
 where
  -- The staging codebase has no `it`, so a definition that uses it does not
  -- resolve; say why rather than that the name is unknown.
  renderProposeError sources' = \case
    Desugar (UnknownName sp "it")
      | isJust session.lastExpr ->
          S.renderSpanError
            (Just src)
            sp
            "`it` is the last result and cannot be stored; paste its definition (:view it) instead"
    err -> renderResolveErrorWith sources' src err

-- Commands ----------------------------------------------------------------------

{- | @:set name value@, as the command and @--set@ take it: the changed
configuration, the reason it is refused, or 'Nothing' when there is no
such setting.
-}
setSetting :: Text -> Text -> Config -> Maybe (Either Text Config)
setSetting name value cfg = case name of
  -- The double backend's estimate (design §8.2): 0 is the running bound,
  -- N ≥ 2 copies; one copy has no spread, and Monte Carlo needs many.
  "samples" ->
    Just $ case natural of
      Just k
        | k == 0 || (k >= 2 && k <= maxSamples) -> Right cfg{samples = k}
      _ ->
        Left
          "samples is 0 (a running error bound) or from 2 to 100000 copies"
  "seed" -> Just (count (\k -> cfg{seed = k}) "seed must be a non-negative integer")
  "rounding" ->
    Just
      ( maybe
          (Left "rounding is nearest or random")
          (\r -> Right cfg{rounding = r})
          (roundingNamed value)
      )
  -- How many evaluations carry the copies in parallel (design §8.2).
  "cores" ->
    Just $ case natural of
      Just k | k >= 1 -> Right cfg{cores = k}
      _ -> Left "cores must be a positive integer"
  "precision" ->
    Just
      (count (\k -> cfg{precision = k}) "precision must be a non-negative integer")
  "sigma" -> Just (count (\k -> cfg{sigma = k}) "sigma must be a non-negative integer")
  -- The threshold, in percent of the first-order σ, over which a value is
  -- marked non-linear (design §3.2).
  "nonlinear" ->
    Just
      ( count
          ( \k ->
              Config
                { precision = cfg.precision
                , sigma = cfg.sigma
                , unicode = cfg.unicode
                , nonlinear = fromIntegral k / 100
                , limits = cfg.limits
                , backend = cfg.backend
                , samples = cfg.samples
                , seed = cfg.seed
                , rounding = cfg.rounding
                , cores = cfg.cores
                , batch = cfg.batch
                }
          )
          "nonlinear must be a non-negative integer, a percentage"
      )
  -- Output spelling (design §2.8, §7.3).
  "unicode" -> Just $ case value of
    "on" -> Right cfg{unicode = True}
    "off" -> Right cfg{unicode = False}
    _ -> Left "unicode is on or off"
  -- The resource limits (design §8.1).
  _ -> fmap (\l -> cfg{limits = l}) <$> setLimit name value cfg.limits
 where
  natural = case reads (T.unpack value) of
    [(k, "")] | k >= (0 :: Int) -> Just k
    _ -> Nothing
  count adjust err = maybe (Left err) (Right . adjust) natural

{- | The settings @--set NAME VALUE@ changes at the start, in order, each as
@:set NAME VALUE@ would.
-}
startSettings :: [(Text, Text)] -> Config -> Either Text Config
startSettings changes cfg0 = foldM change cfg0 changes
 where
  change cfg (n, v) =
    fromMaybe
      (Left ("--set: no setting " <> n <> "; :set lists them"))
      (setSetting n v cfg)

-- | The most copies @:set samples@ takes, 10⁵ (design §8.2).
maxSamples :: Int
maxSamples = 100000

command :: Session -> Text -> [Text] -> Either Text (Session, [Text])
command session src = \case
  ["set"] ->
    keep
      ( Right
          $ [ "precision " <> tshow cfg.precision
            , "sigma " <> tshow cfg.sigma
            , "unicode " <> (if cfg.unicode then "on" else "off")
            , "nonlinear " <> T.pack (show (round (100 * cfg.nonlinear) :: Integer))
            , "samples " <> tshow cfg.samples
            , "seed " <> tshow cfg.seed
            , "rounding " <> roundingName cfg.rounding
            , "cores " <> tshow cfg.cores
            ]
            ++ settingLines cfg.limits
      )
  ["set", name, value]
    | Just changed <- setSetting name value cfg ->
        (\c -> (session{config = c}, [])) <$> changed
  -- Display preferences (design §3.2.12): a unit per exact dimension.
  ["prefer"] ->
    keep
      ( Right
          ( if Set.null cb.preferences
              then ["no preferences"]
              else map ("prefer " <>) (Set.toList cb.preferences)
          )
      )
  ("prefer" : rest) -> do
    let text = T.unwords rest
    (d, _) <- preferenceOf text
    -- One preference per dimension: an earlier one for the same dimension goes.
    let stale =
          [ t
          | t <- Set.toList cb.preferences
          , Just (d', _) <- [either (const Nothing) Just (preferenceOf t)]
          , d' == d
          ]
        cb' = addPreference text (foldr removePreference session.codebase stale)
    refreshed <-
      refreshPreferences
        session
          { codebase = cb'
          , staging = addPreference text (foldr removePreference cb stale)
          }
    pure
      ( refreshed
      ,
        [ "values of dimension "
            <> renderDimIn spelling (\v -> "d" <> tshow v) d
            <> " print in "
            <> text
        ]
      )
  ("unprefer" : rest) -> do
    let text = T.unwords rest
    if Set.member text cb.preferences
      then
        (,["removed the preference " <> text])
          <$> refreshPreferences
            session
              { codebase = removePreference text session.codebase
              , staging = removePreference text cb
              }
      else Left ("no preference " <> text <> "; :prefer lists them")
  -- The evaluator of the scalars (design §8.2). A stored term names no
  -- backend, so switching changes no hash, only what the next input runs on.
  ["backend"] -> keep (Right [backendName cfg.backend])
  ["backend", name] -> (,[]) <$> startBackend name session
  -- The commands that read uncertainty are the affine backend's.
  (c : _)
    | cfg.backend /= AffineBackend
    , c `elem` ["exact", "budget", "covariance"] ->
        Left
          ( ":"
              <> c
              <> " is the affine backend's; the "
              <> backendName cfg.backend
              <> " backend does not have it (:backend affine)"
          )
  -- The raw magnitudes (design §3.2.10): midpoint, nudges, slack.
  ("exact" : rest) -> keep $ do
    (h, v) <- evalOf rest
    (: [])
      <$> either
        (Left . renderEvalError)
        Right
        ( renderValueWith
            (inputPrinter h)
            cfg.precision
            session.preferred
            (renderExact (inputNamer h) cfg.precision)
            v
        )
  -- The error budget (design §3.2.6) of a scalar, or of the sum of a
  -- tensor's components.
  ("budget" : rest) -> keep $ do
    (h, v) <- evalOf rest
    case displayParts (inputPrinter h) cfg.precision session.preferred v of
      Right (_, xs, units) ->
        pure
          ( renderBudget
              (inputNamer h)
              cfg.precision
              cfg.nonlinear
              units
              (foldr (addM (precisionOf cfg)) (Exact 0) xs)
          )
      Left (Internal _) -> Left "budget: not a number"
      Left err -> Left (renderEvalError err)
  -- The covariance view (design §3.5): Σ cᵢcᵢᵀ over the statistical nudges of
  -- a vector, with the bound radii beside it as a bias box. A pair of
  -- vectors (r, v) prints its joint covariance as the three blocks of
  -- linalg.jointCovariance, rr, rv and vv (design §3.7), and both boxes.
  ("covariance" : rest) -> keep $ do
    (h, v) <- evalOf rest
    let shown =
          either (Left . renderEvalError) Right
            . renderValue (inputPrinter h) cfg.precision session.preferred
        rough =
          either (Left . renderEvalError) Right
            . renderValueWith (inputPrinter h) cfg.precision session.preferred renderRough
        components buf = either (Left . renderEvalError) Right (sequence (V.toList buf))
        unpinned = fmap (\hh -> hh{pinned = False})
        -- One vector's bound radii, in its own shape and unit.
        boundsOf dims d hint xs = VTensor dims d hint (V.fromList [Right (Exact (collapse x).bound) | x <- xs])
        vectorOf = \case
          Right (VTensor [n] d hint buf) -> Just (n, d, hint, buf)
          _ -> Nothing
    case v of
      VTensor dims d hint buf | length dims <= 1 -> do
        xs <- components buf
        let covHint = unpinned (hintPow (precisionOf cfg) 2 =<< hint)
            covValue = covarianceMatrix cfg (dimPow 2 d) covHint xs xs
            scalarVar = case covValue of
              VTensor _ d' h' cs -> VTensor [] d' h' (V.take 1 cs)
              other -> other
        covText <- shown (if null dims then scalarVar else covValue)
        boundText <- rough (boundsOf dims d hint xs)
        pure
          [ (if null dims then "variance " else "covariance ") <> covText
          , (if null dims then "bound " else "bound box ") <> boundText
          ]
      VData (TupleC 2) [a, b]
        | Just (n1, d1, h1, buf1) <- vectorOf a
        , Just (n2, d2, h2, buf2) <- vectorOf b -> do
            xs <- components buf1
            ys <- components buf2
            let p = precisionOf cfg
                block d hh = covarianceMatrix cfg d (unpinned hh)
            rr <- shown (block (dimPow 2 d1) (hintPow p 2 =<< h1) xs xs)
            rv <- shown (block (dimMul d1 d2) (hintProduct p h1 h2) xs ys)
            vv <- shown (block (dimPow 2 d2) (hintPow p 2 =<< h2) ys ys)
            boxes <-
              rough
                ( VData
                    pairC
                    [Right (boundsOf [n1] d1 h1 xs), Right (boundsOf [n2] d2 h2 ys)]
                )
            pure ["rr " <> rr, "rv " <> rv, "vv " <> vv, "bound box " <> boxes]
      _ -> Left "covariance: a number, a vector, or a pair of vectors"
  ["add"] -> add session
  ["update"] -> update True session
  ["update", "--no-upgrade"] -> update False session
  ["upgrade", n] -> upgrade (argIn session.codebase n) session
  ["todo"] -> keep (todo session)
  ["scratch"] -> keep (Right (map pending session.scratch))
  ["forget", n] -> forget (pendingName n) session
  -- The type the expression's value has as `it`, a named value (design
  -- §3.9, decision 5): when not a function, its free axes anonymous.
  ("type" : rest) -> keep $ do
    e <- parseExprWithin cfg.limits.digits (T.unwords rest)
    CheckedExpr _ _ ty _ <- checkExpr scope ecb (T.unwords rest) e
    pure [maybe "" (renderForallIn spelling . defaultAxes) ty]
  -- Without an editor, :edit prints the source it would open (design
  -- §7.3); the REPL opens it, and reads a file for --file.
  ("edit" : args) ->
    editRequest session args >>= \case
      EditOpen _ _ paste -> Right (session, paste)
      EditResume _ path ->
        Left ("only the REPL reads files; :edit --file " <> T.pack path <> " there")
  ["lint", n] -> keep $ withExprName n $ \_ r -> case lookupTyped r.hash ecb of
    Nothing -> Left ("no typed core for " <> showHash r.hash)
    Just t -> case lintClosed (typeLookupFor ecb) t of
      Left err -> Left ("lint failed: " <> err)
      Right schemes -> pure (map renderScheme schemes)
  ["core", n] -> keep $ withExprName n $ \full ->
    fmap ((: []) . ((short ecb full <> " = ") <>)) . viewTyped scope ecb
  -- Browse the codebase (design §7.3): names with their types, filtered.
  ("ls" : rest) -> keep (listNames session rest)
  ["hash", n] -> keep $ withExprName n $ \_ r -> pure [showReference r]
  ["names", h] -> keep $ case findByPrefix h cb of
    [] -> Left ("no definition with hash " <> h)
    hs ->
      pure
        [ showHash h'
            <> " "
            <> T.unwords
              (map (short cb) (historicalNamesOf (Reference h' Nothing) cb) ++ cycleNames h')
        | h' <- hs
        ]
  ["history", n] -> keep $ do
    full <- argFor (\p -> not (null (historyOf p cb))) cb n
    case historyOf full cb of
      [] -> Left ("unknown name `" <> n <> "`")
      r : rs -> pure ((showReference r <> "  (current)") : map showReference rs)
  -- A name the uses offer as several shows each, after a comment naming
  -- its path, types first (design §7.3).
  ["view", n] -> keep $ case argPaths scope ecb n of
    [full] -> viewOne full
    fulls -> case [(full, ls) | full <- fulls, Right ls <- [viewOne full]] of
      [] -> Left ("unknown name `" <> n <> "`")
      views -> pure (concat [("-- " <> full) : ls | (full, ls) <- views])
   where
    viewOne full = case lookupName full ecb of
      -- A chart's right-hand side, `step at origin`, is not an
      -- expression, so it is viewed with its keyword (design §3.8).
      Just r ->
        (: [])
          <$> definitionLine
            spelling
            scope
            ecb
            (if isChartName full ecb then "chart " else "")
            (short ecb full)
            r
      Nothing -> viewData spelling scope cb full
  ["dependents", n] -> keep $ withName n $ \full r -> pure (map (short cb) (dependents full r.hash cb))
  -- An alias of a unit or chart is one too; an alias of a namespace aliases
  -- every label under it (design §7.6).
  ["alias", new, old]
    | Just r <- lookupName (argIn session.codebase old) session.codebase -> do
        let old' = argIn session.codebase old
            new' = newPath new
            flagged =
              (if isUnitName old' cb then markUnit new' else id)
                . (if isChartName old' cb then markChart new' else id)
        refuseClash cb [(new', "definition")]
        commit
          (flagged (bindName new' r cb))
          ["`" <> new <> "` now also names " <> showReference r]
    | isNamespace session.codebase (argIn session.codebase old) -> do
        let old' = argIn session.codebase old
        (cb', k) <- relabel True (underNamespace old' (newPath new)) cb
        commit
          cb'
          [ "`"
              <> new
              <> "` now also names the "
              <> labelsText k
              <> " under `"
              <> old
              <> "`"
          ]
    | otherwise -> Left ("unknown name `" <> old <> "`")
  ["unname", n]
    | Just f <- T.stripPrefix "." n
    , Found full <- qualifyName FieldLabel scope session.codebase f ->
        commit (unbindName ("." <> full) cb) ["removed the label `" <> n <> "`"]
    | labelled (argIn session.codebase n) ->
        commit
          (unbindName (argIn session.codebase n) cb)
          ["removed the label `" <> n <> "`"]
    | isNamespace session.codebase (argIn session.codebase n) ->
        let ns = argIn session.codebase n
            gone = namespaceLabels session.codebase ns
         in commit
              (foldr removeLabel cb gone)
              [ "removed the "
                  <> labelsText (length (labelKinds session.codebase gone))
                  <> " under `"
                  <> n
                  <> "`; :history name still finds them"
              ]
    | otherwise -> Left ("unknown name `" <> n <> "`")
  -- Relabelling (design §7.2, §7.6): a label, or a namespace and all under it.
  ["rename", old, new] -> do
    let old' = argIn session.codebase old
        new' = newPath new
    pairs <- relabelPairs old' new'
    (cb', k) <- relabel False pairs cb
    re <- restamp pairs cb'
    commit
      re.codebase
      ( ( if labelled old'
            then "renamed `" <> old <> "` to `" <> new <> "`"
            else
              "renamed the " <> labelsText k <> " under `" <> old <> "` to `" <> new <> "`"
        )
          : restampReport pairs re
      )
  ("move" : args@(_ : _ : _)) -> do
    let target = newPath (last args)
        pathFor o = if T.null target then S.lastSegment o else target <> "." <> S.lastSegment o
    pairs <-
      concat
        <$> mapM
          (\o -> let o' = argIn session.codebase o in relabelPairs o' (pathFor o'))
          (init args)
    (cb', k) <- relabel False pairs cb
    re <- restamp pairs cb'
    commit
      re.codebase
      ( ("moved " <> labelsText k <> " to `" <> last args <> "`")
          : restampReport pairs re
      )
  -- The current namespace and the uses (design §7.6), for the session.
  ["namespace"] -> keep (Right [namespaceLine scope.namespace])
  ["namespace", p] -> do
    let path = case T.stripPrefix "." p of
          Just "" -> []
          Just rest -> T.splitOn "." rest
          Nothing -> T.splitOn "." p
    case [ q | k <- [1 .. length path], let q = T.intercalate "." (take k path), labelled q
         ] of
      q : _ ->
        Left
          ( "`"
              <> q
              <> "` is a "
              <> labelNoun session.codebase q
              <> "; it cannot also be a namespace"
          )
      [] | any T.null path -> Left ("not a namespace path: " <> p)
      [] -> Right (session{scope = scope{S.namespace = path}}, [namespaceLine path])
  -- The codebase's stored uses, then the session's (design §7.7).
  ["uses"] ->
    keep
      ( Right
          ( case ["use " <> S.renderUse u <> " (stored)" | u <- session.codebase.uses]
              ++ ["use " <> S.renderUse u | u <- scope.uses] of
              [] -> ["no uses"]
              ls -> ls
          )
      )
  -- A stored use when there is one, else the session's (design §7.7).
  ["unuse", p] ->
    let path = fromMaybe p (T.stripPrefix "." p)
        matches u = u.path == path || u.alias == Just path
        (gone, kept) = partition matches scope.uses
        storedGone = filter matches session.codebase.uses
     in if not (null storedGone)
          then
            storedUses
              (foldr removeStoredUse session.codebase storedGone)
              [ "removed the stored use "
                  <> S.renderUse u
                  <> "; :use "
                  <> S.renderUse u
                  <> " puts it back"
              | u <- storedGone
              ]
          else
            if null gone
              then Left ("`" <> p <> "` is not in use; :uses lists them")
              else Right (session{scope = scope{S.uses = kept}}, [])
  -- A stored use (design §7.7); a `use` statement is the session's own.
  ("use" : args) -> case args of
    [p] -> storeUse (S.Use (unDot p) Nothing)
    [p, "as", a] -> storeUse (S.Use (unDot p) (Just a))
    _ -> Left "usage: :use path [as alias], a use the codebase keeps"
  ["stdlib", "upgrade"] -> do
    lib <- stdlibCodebase
    stdlibUpgrade lib session
  -- The codebase as source (design §7.4); the REPL writes it to a file.
  ("export" : args) ->
    exportRequest session args >>= \case
      (Nothing, source) -> Right (session, [source | not (T.null source)])
      (Just file, _) -> Left ("only the REPL writes files; :export there to write " <> T.pack file)
  _ ->
    Left commandHelp
 where
  cb = session.staging
  scope = session.scope
  -- Read-only commands also see `it`; nothing built from this is kept.
  ecb = exprCodebase session
  cfg = session.config
  spelling = spellingOf cfg
  keep = fmap (session,)
  short = shortestName scope
  tshow = T.pack . show
  evalOf rest = do
    e <- parseExprWithin cfg.limits.digits (T.unwords rest)
    evalValue cfg scope ecb (T.unwords rest) e
  -- Nudges declared in the expression itself are labelled "input".
  inputNamer h h' i written = if h' == h then "input" else refNamer scope ecb h' i written
  inputPrinter h = (printerFor cfg scope ecb){refName = inputNamer h}
  preferenceOf = preferenceHint cfg cb
  commit cb' outs = Right (session{codebase = cb', staging = cb'}, outs)
  -- What a relabelling re-hashed (design §7.2): the stamped definitions and
  -- types it moved, then what was upgraded to follow them. A type's hash
  -- prints as its name wherever it is named, so a type line has no hashes.
  restampReport pairs re =
    [ "re-hashed data " <> shortestNameOf TypeLabel scope re.codebase n
    | (n, _, _) <- re.types
    ]
      ++ [ verb
             <> short re.codebase n
             <> " "
             <> showReference old
             <> " -> "
             <> showReference new
         | (verb, n, old, new) <-
             sortOn
               (\(verb, n, _, _) -> (verb /= "re-hashed ", n))
               [ (if n `elem` map snd pairs then "re-hashed " else "upgraded ", n, old, new)
               | (n, old, new) <- re.terms
               ]
         ]
  unDot p = fromMaybe p (T.stripPrefix "." p)
  storeUse u
    | u `elem` session.codebase.uses =
        Left ("use " <> S.renderUse u <> " is already stored")
    | otherwise =
        storedUses (addStoredUse u session.codebase) ["stored use " <> S.renderUse u]
  -- A change to the stored uses re-resolves the scratch and the
  -- preferences, which may have reached names through them.
  storedUses cb' outs = do
    staging' <-
      either
        ( \err ->
            Left
              ( "the pending definitions would not check; nothing was changed:\n"
                  <> renderResolveError err
              )
        )
        Right
        (processGroup cb' session.scratch)
    s <- refreshPreferences session{codebase = cb', staging = staging'}
    pure (s, outs)
  argIn = argPath scope
  -- A name to create: under the current namespace, or absolute.
  newPath n = fromMaybe (S.qualify scope.namespace n) (T.stripPrefix "." n)
  pendingName n =
    case qualifyWith
      session.codebase.uses
      (`elem` map (.name.text) session.scratch)
      scope
      n of
      Found full -> full
      _ -> n
  withName = withNameIn cb
  withExprName = withNameIn ecb
  withNameIn c n k = do
    full <- argFor (\p -> isJust (lookupName p c)) c n
    maybe (Left ("unknown name `" <> n <> "`")) (k full) (lookupName full c)
  {- A name a query about one definition takes: of the paths it may mean
  (design §7.6), the one that is such a definition; several are listed. -}
  argFor present c n = case argPaths scope c n of
    [full] -> Right full
    fulls -> case filter present fulls of
      [full] -> Right full
      [] -> Left ("unknown name `" <> n <> "`")
      several ->
        Left
          ( "`"
              <> n
              <> "` is both "
              <> T.intercalate " and " (map (\f -> "`" <> f <> "`") several)
              <> "; write one of them"
          )
  cycleNames h' = case lookupTerm h' cb of
    Just (Cycle hints _) ->
      [ T.intercalate
          ","
          (map (short cb) (historicalNamesOf (Reference h' (Just i)) cb))
      | i <- [0 .. vecLength hints - 1]
      ]
    _ -> []
  pending = \case
    S.DBind _ b -> "pending: " <> short cb b.name.text
    S.DData _ d -> "pending: data " <> shortestNameOf TypeLabel scope cb d.name.text
    S.DSig _ n _ -> "pending: " <> signatureLine spelling scope cb n.text
    S.DSpace _ n _ -> "pending: space " <> shortestNameOf TypeLabel scope cb n.text
  -- A label of any kind: a definition, a type, a constructor or a field.
  labelled n =
    Map.member n session.codebase.names
      || Map.member n session.codebase.typeNames
      || Map.member n session.codebase.conNames
  -- What to relabel for a label or a namespace given to :rename or :move.
  relabelPairs old new
    | labelled old || Map.member old session.codebase.fieldNames =
        Right [(old, new)]
    | isNamespace session.codebase old = Right (underNamespace old new)
    | otherwise = Left ("unknown name `" <> old <> "`")
  underNamespace old new =
    [ (l, new <> T.drop (T.length old) l) | l <- namespaceLabels session.codebase old
    ]
  refuseClash c new =
    case disjointness c [(n, what, S.Span (S.Pos 1 1) (S.Pos 1 1)) | (n, what) <- new] of
      Just (_, msg) -> Left msg
      Nothing -> Right ()
  _ = src

{- | Store scratch definitions whose names are new (or unchanged). A name
that exists with a different definition is a conflict.
-}
add :: Session -> Either Text (Session, [Text])
add session
  | null session.scratch = Right (session, ["nothing to add"])
  | Just err <- orphanSignature session = Left err
  | not (null conflicts) =
      Left
        ( T.intercalate "\n"
            $ ["`" <> n <> "` already exists with a different definition" | n <- conflicts]
              ++ [ "use :update to replace "
                     <> (if length conflicts == 1 then "it" else "them")
                     <> " and upgrade dependents"
                 ]
        )
  | otherwise =
      Right
        ( session
            { codebase = session.staging
            , scratch = []
            , sources = Map.empty
            , staging = session.staging
            }
        , [ "added " <> shortestName session.scope session.staging n
          | n <- defined
          ]
            ++ signedReport session
        )
 where
  names = nubOrd (map (.name.text) session.scratch)
  defined = nubOrd [d.name.text | d <- session.scratch, not (S.isSignature d)]
  conflicts =
    [ n
    | n <- names
    , Just old <- [lookupName n session.codebase]
    , lookupName n session.staging /= Just old
    ]
      ++ [ n
         | n <- names
         , Just old <- [lookupTypeName n session.codebase]
         , lookupTypeName n session.staging /= Just old
         ]

{- | Store scratch definitions, re-binding names that already exist, then
propagate the new versions to every dependent that still typechecks
(unless told not to).
-}
update :: Bool -> Session -> Either Text (Session, [Text])
update doUpgrade session
  | null session.scratch = Right (session, ["nothing to update"])
  | Just err <- orphanSignature session = Left err
  | otherwise =
      let names = nubOrd (map (.name.text) session.scratch)
          changed =
            [ (n, old, new)
            | n <- names
            , Just old <- [lookupName n session.codebase]
            , Just new <- [lookupName n session.staging]
            , old /= new
            ]
          added =
            [ n
            | S.DBind _ b <- session.scratch
            , let n = b.name.text
            , Nothing <- [lookupName n session.codebase]
            ]
          types =
            [ ( if Map.member n session.codebase.typeNames
                  then "updated data "
                  else "added data "
              )
                <> shortestNameOf TypeLabel session.scope session.staging n
            | S.DData _ d <- session.scratch
            , let n = d.name.text
            , lookupTypeName n session.codebase /= lookupTypeName n session.staging
            ]
          refmap = Map.fromList [(old, new) | (_, old, new) <- changed]
          written = Map.fromListWith Set.union [(old, Set.singleton n) | (n, old, _) <- changed]
          result =
            if doUpgrade
              then propagateNamed written refmap session.staging
              else Propagation session.staging [] []
          short = shortestName session.scope result.codebase
          report =
            types
              ++ ["added " <> short n | n <- added]
              ++ [ "updated " <> short n <> " " <> showReference old <> " -> " <> showReference new
                 | (n, old, new) <- changed
                 ]
              ++ signedReport session
              ++ upgradeReport short result
              ++ [ "dependents left on old versions: "
                     <> T.unwords [short n | (n, _, _) <- staleReferences result.codebase]
                 | not doUpgrade
                 , not (null (staleReferences result.codebase))
                 ]
       in Right
            ( session
                { codebase = result.codebase
                , scratch = []
                , sources = Map.empty
                , staging = result.codebase
                }
            , report
            )

{- | @signed f@ for each pending signature of a stored definition that the
scratch does not redefine (design §4.8): what @:add@ and @:update@ store
for it.
-}
signedReport :: Session -> [Text]
signedReport session =
  [ "signed " <> shortestName session.scope session.staging n.text
  | S.DSig _ n _ <- session.scratch
  , n.text `notElem` [b.name.text | S.DBind _ b <- session.scratch]
  ]

upgrade :: Text -> Session -> Either Text (Session, [Text])
upgrade n session = case lookupName n session.codebase of
  Nothing -> Left ("unknown name `" <> n <> "`")
  Just current ->
    let stale = [r | r <- historyOf n session.codebase, r /= current]
        result =
          propagateNamed
            (Map.fromList [(r, Set.singleton n) | r <- stale])
            (Map.fromList [(r, current) | r <- stale])
            session.codebase
        cb' = result.codebase
        staging' = fromRight cb' (processGroup cb' session.scratch)
     in Right
          ( session{codebase = cb', staging = staging'}
          , if null result.upgraded && null result.skipped
              then ["nothing to upgrade"]
              else upgradeReport (shortestName session.scope cb') result
          )

{- | @:stdlib upgrade@ (design §7.7), a sketch of upgrading a library from a
newer version of it: the shipped library's labels under its namespaces against
the codebase's. A name the codebase has never had is added, and so is a type
label, constructor label or field label it has never had. A name still on
the binding it was seeded with and whose shipped version differs is
updated, and its dependents are upgraded as @:update@ does. "Still on the
binding it was seeded with" is read off the history: it has exactly one
entry. A name the user rebound or unnamed is kept: the user's choice wins.
The codebase cannot know which versions earlier libraries shipped, so a
name rebound by an earlier upgrade counts as the user's.
-}
stdlibUpgrade :: Codebase -> Session -> Either Text (Session, [Text])
stdlibUpgrade shipped session =
  let cb0 = session.codebase
      library =
        [ (n, r)
        | (n, r) <- Map.toList shipped.names
        , isLibraryPath n
        ]
      added =
        [ (n, r) | (n, r) <- library, isNothing (lookupName n cb0), null (historyOf n cb0)
        ]
      untouched n = length (historyOf n cb0) == 1
      updated =
        [ (n, old, r)
        | (n, r) <- library
        , Just old <- [lookupName n cb0]
        , old /= r
        , untouched n
        ]
      kept =
        [ n
        | (n, r) <- library
        , lookupName n cb0 /= Just r
        , n `notElem` map fst added
        , n `notElem` [m | (m, _, _) <- updated]
        ]
      -- The shipped terms, with their types, are content and never conflict.
      withContent =
        cb0
          { terms = Map.union cb0.terms shipped.terms
          , derived = Map.union cb0.derived shipped.derived
          , typeDefs = Map.union cb0.typeDefs shipped.typeDefs
          }
      flagged n =
        (if isUnitName n shipped then markUnit n else id)
          . (if isChartName n shipped then markChart n else id)
      -- A type, constructor or field label the codebase has never had comes
      -- with the library's type; one it has, the user's or an older
      -- library's, is left alone.
      newLabels :: Map.Map Text a -> (Text -> Codebase -> Maybe a) -> [(Text, a)]
      newLabels m lookupIn =
        [ (n, x)
        | (n, x) <- Map.toList m
        , isLibraryPath n
        , isNothing (lookupIn n cb0)
        ]
      addedTypes = newLabels shipped.typeNames lookupTypeName
      withLabels =
        foldl
          (\acc (n, (h, i, j)) -> bindFieldName n h i j acc)
          ( foldl
              (\acc (n, (h, i)) -> bindConName n h i acc)
              (foldl (\acc (n, h) -> bindTypeName n h acc) withContent addedTypes)
              (newLabels shipped.conNames lookupConName)
          )
          (newLabels shipped.fieldNames lookupFieldName)
      cb1 =
        foldl
          (\acc (n, r) -> bindName n r acc)
          (foldl (\acc (n, r) -> flagged n (bindName n r acc)) withLabels added)
          [(n, r) | (n, _, r) <- updated]
      result =
        propagateNamed
          (Map.fromListWith Set.union [(old, Set.singleton n) | (n, old, _) <- updated])
          (Map.fromList [(old, r) | (_, old, r) <- updated])
          cb1
      cb' = result.codebase
      short = shortestName session.scope cb'
   in do
        staging' <-
          either (Left . renderResolveError) Right (processGroup cb' session.scratch)
        refreshed <- refreshPreferences session{codebase = cb', staging = staging'}
        pure
          ( refreshed
          , case [ "added data " <> shortestNameOf TypeLabel session.scope cb' n
                 | (n, _) <- addedTypes
                 ]
              ++ ["added " <> short n | (n, _) <- added]
              ++ [ "updated " <> short n <> " " <> showReference old <> " -> " <> showReference r
                 | (n, old, r) <- updated
                 ]
              ++ ["kept " <> short n <> " (yours)" | n <- kept]
              ++ upgradeReport short result of
              [] -> ["the library is up to date"]
              ls -> ls
          )

todo :: Session -> Either Text [Text]
todo session =
  Right
    $ [ "pending: " <> pendingText b <> " (use :add or :update)" | b <- session.scratch
      ]
      ++ [ "stale: "
             <> short n
             <> " uses "
             <> short m
             <> showReference r
             <> " (use :upgrade "
             <> short m
             <> ")"
         | (n, r, m) <- staleReferences session.codebase
         ]
      ++ [ "nothing to do" | null session.scratch, null (staleReferences session.codebase)
         ]
 where
  short = shortestName session.scope session.staging
  pendingText = \case
    S.DBind _ b -> short b.name.text
    S.DData _ d -> shortestNameOf TypeLabel session.scope session.staging d.name.text
    S.DSig _ n _ ->
      signatureLine (spellingOf session.config) session.scope session.staging n.text
    S.DSpace _ n _ -> shortestNameOf TypeLabel session.scope session.staging n.text

forget :: Text -> Session -> Either Text (Session, [Text])
forget n session
  | n `notElem` map (.name.text) session.scratch =
      Left ("`" <> n <> "` is not pending")
  | otherwise =
      let scratch' = filter (\b -> b.name.text /= n) session.scratch
       in case processGroup session.codebase scratch' of
            Left err -> Left (renderResolveError err)
            Right staging' ->
              Right
                ( session
                    { scratch = scratch'
                    , -- The name's signature goes with it (design §4.8).
                      sources = Map.delete ("::" <> n) (Map.delete n session.sources)
                    , staging = staging'
                    }
                , ["forgot `" <> n <> "`"]
                )

listNames :: Session -> [Text] -> Either Text [Text]
listNames session args = do
  let (before, after) = break (== ":") args
      flags = filter (T.isPrefixOf "--") before
      words' = filter (not . T.isPrefixOf "--") before
      -- A word that names a namespace lists that namespace (design §7.6);
      -- the others are globs. With no argument at all, the current namespace.
      (spaces, globs) = partition (isJust . namespaceOf) words'
      nsFilter = case mapMaybe namespaceOf spaces of
        ns : _ -> Just ns
        []
          | null args
          , not (null session.scope.namespace) ->
              Just (T.intercalate "." session.scope.namespace)
          | otherwise -> Nothing
      typeText = T.unwords (drop 1 after)
  mapM_
    ( \f ->
        if f `elem` ["--all", "--units", "--charts", "--types"]
          then Right ()
          else
            Left ("unknown flag " <> f <> "; :ls takes --all, --units, --charts, --types")
    )
    flags
  query <-
    if null after
      then Right Nothing
      else do
        t <- parseType typeText
        either
          (Left . renderResolveError)
          (Right . Just)
          (queryScheme session.scope cb t)
  let own = null args
      allPaths = "--all" `elem` flags && isNothing nsFilter
      kindOk n
        | "--units" `elem` flags = isUnitName n cb
        | "--charts" `elem` flags = isChartName n cb
        | "--types" `elem` flags = False
        | otherwise = True
      inNamespace n = maybe True (\ns -> (ns <> ".") `T.isPrefixOf` n) nsFilter
      nameOk n =
        inNamespace n
          && all (\g -> matchesGlob g n || matchesGlob g (S.lastSegment n)) globs
          && (not own || maybe False (not . T.any (== '.')) (relative n))
      -- Relative to the namespace listed, in full with --all, else as short
      -- as the scope allows.
      shown n = case nsFilter of
        Just ns -> T.drop (T.length ns + 1) n
        Nothing
          | allPaths -> n
          | otherwise -> shortestName session.scope cb n
      shownType n = case nsFilter of
        Just ns -> T.drop (T.length ns + 1) n
        Nothing
          | allPaths -> n
          | otherwise -> shortestNameOf TypeLabel session.scope cb n
      typeOk sc = maybe True (`I.matchesQuery` sc) query
      definitions =
        [ prefix n <> shown n <> " : " <> renderForallIn (spellingOf session.config) sc
        | (n, r) <- sortOn (T.toLower . fst) (Map.toList cb.names)
        , kindOk n
        , nameOk n
        , -- A signed name shows, and matches, its signature (design §4.8).
        Just sc <- [signatureOf n cb <|> (defaultAxes <$> typeOf r cb)]
        , typeOk sc
        ]
      types =
        [ line
        | "--units" `notElem` flags
        , "--charts" `notElem` flags
        , (n, h) <- sortOn (T.toLower . fst) (Map.toList cb.typeNames)
        , Just def <- [lookupTypeDef h cb]
        , -- A chart's frame lists with --types only (design §3.10, F3).
        "--types" `elem` flags || isNothing (frameDefMoving def)
        , line <-
            [ declaration shownType shown h n def
            | nameOk n
            , isNothing query
            ]
              ++ [ shown c <> " : " <> renderForallIn (spellingOf session.config) sc
                 | (i, fields) <- zip [0 ..] def.constructors
                 , Just c <- [conNameOf h i cb]
                 , nameOk c
                 , let sc = constructorScheme h def i fields
                 , typeOk sc
                 ]
        ]
      -- Alone: the namespaces directly under the current one, with their size.
      footer =
        [ "namespace "
            <> child
            <> " ("
            <> namesText (length (namespaceLabels cb full))
            <> ")"
        | own
        , child <-
            Set.toList
              ( Set.fromList
                  [ T.takeWhile (/= '.') r
                  | n <- labelPaths
                  , Just r <- [relative n]
                  , T.any (== '.') r
                  ]
              )
        , let full = if T.null here then child else here <> "." <> child
        ]
      -- A namespace's listing names its types relative to it too.
      listScope = case nsFilter of
        Just ns -> session.scope{S.namespace = T.splitOn "." ns}
        Nothing -> session.scope
  pure
    ( case map (nameTypes listScope cb) (definitions ++ types) ++ footer of
        [] -> ["nothing matches"]
        ls -> ls
    )
 where
  cb = session.staging
  tshow = T.pack . show
  -- The current namespace, and a path relative to it when it is under it.
  here = T.intercalate "." session.scope.namespace
  relative n = if T.null here then Just n else T.stripPrefix (here <> ".") n
  labelPaths =
    Map.keys cb.names
      ++ Map.keys cb.typeNames
      ++ Map.keys cb.conNames
      ++ Map.keys cb.fieldNames
  namesText k = tshow k <> (if k == 1 then " name" else " names")
  prefix n
    | isUnitName n cb = "unit "
    | isChartName n cb = "chart "
    | otherwise = ""
  declaration shownType shown h n def =
    renderTypeDef
      (spellingOf session.config)
      (shownType n)
      [ maybe (showHash h <> "." <> tshow i) shown (conNameOf h i cb)
      | i <- [0 .. length def.constructors - 1]
      ]
      [ map (fmap S.lastSegment) (fieldNamesOf h i (length fs) cb)
      | (i, fs) <- zip [0 ..] def.constructors
      ]
      def
  -- A word naming a namespace: relative to the current one, or absolute.
  namespaceOf w
    | T.any (== '*') w = Nothing
    | Just p <- T.stripPrefix "." w = if isNamespace cb p then Just p else Nothing
    | inside <- S.qualify session.scope.namespace w
    , not (null session.scope.namespace)
    , isNamespace cb inside =
        Just inside
    | isNamespace cb w = Just w
    | otherwise = Nothing
  -- A constructor's type: its fields to the type at its own parameters.
  constructorScheme h def i fields =
    let tyArgs = [varArg k v | (v, k) <- def.params]
        self = TData h tyArgs
        instantiated = case dataConstructors (`lookupTypeDef` cb) self of
          Just table | Just fs <- lookup (UserCon h i) table -> fs
          _ -> fields
     in Forall def.params (foldr TFun self instantiated)

{- | @*@ matches any run of characters; a pattern without @*@ matches as a
case-insensitive substring.
-}
matchesGlob :: Text -> Text -> Bool
matchesGlob pat name
  | T.any (== '*') pat = go (T.splitOn "*" (T.toLower pat)) (T.toLower name)
  | otherwise = T.toLower pat `T.isInfixOf` T.toLower name
 where
  go [] s = T.null s
  go [p] s = p `T.isSuffixOf` s
  go (p : ps) s
    | p == "" = anywhere ps s
    | p `T.isPrefixOf` s = anywhere ps (T.drop (T.length p) s)
    | otherwise = False
  anywhere [] _ = True
  anywhere (p : ps) s = case T.breakOn p s of
    (_, rest) | p /= "" && T.null rest -> False
    (_, rest) -> case ps of
      [] -> p `T.isSuffixOf` s
      _ -> anywhere ps (T.drop (T.length p) rest)

{- | A new last expression that mentions the previous @it@ takes that
expression's term into itself, so @:view it@ after @1 + 2@ then @it * 2@
prints @(1 + 2) * 2@ and not a reference nothing names. The inlined term
is checked again, so the typed term and types stay those of what is shown.
-}
absorbLast :: Session -> LastExpr -> Either Text LastExpr
absorbLast session le = case session.lastExpr of
  Just previous
    | let h = hashTerm previous.term
    , h `Set.member` refs le.term -> do
        let term' = inlineRef h previous.term le.term
            look = typeLookupFor le.base
        (_, typed') <- either (Left . (.message)) Right (I.elaborateClosed look term')
        linted <- either (Left . ("internal error: " <>)) Right (lintClosed look typed')
        pure le{term = term', schemes = linted, typed = typed'}
  _ -> pure le

{- | A pending signature whose definition has not arrived (design §4.8): it
waits in the scratch, and storing the scratch refuses until it does.
-}
orphanSignature :: Session -> Maybe Text
orphanSignature session = case orphans of
  n : _ ->
    Just
      ( "`"
          <> shortestName session.scope session.staging n
          <> "` has a signature but no definition; define it, or :forget "
          <> shortestName session.scope session.staging n
      )
  [] -> Nothing
 where
  orphans =
    [ n.text
    | S.DSig _ n _ <- session.scratch
    , n.text `notElem` [b.name.text | S.DBind _ b <- session.scratch]
    , isNothing (lookupName n.text session.staging)
    ]
