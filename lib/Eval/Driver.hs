{- | Runs source text through the whole pipeline for the CLI and the tests
(design §7.3, §7.5).

Definitions typed at the prompt or read from a file go into the
**scratch**: they are desugared, typechecked, hashed and usable by
expressions, but not stored. @:add@ and @:update@ move them into the
codebase; @:update@ also propagates the new versions to the dependents
that still typecheck.
-}
module Eval.Driver (
  Session (..),
  LastExpr (..),
  emptySession,
  seededSession,
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
import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.Char (isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Graph (flattenSCC, stronglyConnComp)
import Data.List (partition, sortOn)
import Data.Map.Lazy qualified as LazyMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Eval.Affine (
  Collapsed (..),
  Magnitude (..),
  addM,
  collapse,
 )
import Eval.Builtin
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Dimension (Dim, Spelling (..), dimMul, dimPow, renderDimIn)
import Eval.Eval
import Eval.Hash (hashTerm)
import Eval.Infer qualified as I
import Eval.Parser (parseExpr, parseProgram, parseType)
import Eval.Prelude (isLibraryPath, stdlibCodebase)
import Eval.Pretty
import Eval.Resolve
import Eval.Syntax qualified as S
import Eval.TCore
import Eval.Type (
  Arg (..),
  Scheme (..),
  Type (..),
  TypeDef (..),
  dataConstructors,
  renderForallIn,
  renderScheme,
  renderTypeDef,
  varArg,
 )
import Eval.Update

data Session = Session
  { codebase :: Codebase
  , scratch :: [S.Decl]
  -- ^ pending definitions, oldest first
  , sources :: Map Text Text
  -- ^ the input text each pending definition came from, for error excerpts
  , staging :: Codebase
  -- ^ codebase with the scratch entered on top; what expressions see
  , config :: Config
  -- ^ evaluation settings, changed with @:set@
  , preferred :: Preferences
  -- ^ the codebase's preference texts, evaluated to hints keyed by dimension (design §3.2.12)
  , lastExpr :: Maybe LastExpr
  {- ^ the last expression statement that evaluated, which expressions and
  inspection commands see as @it@ (design §7.3); never stored
  -}
  , scope :: S.Scope
  {- ^ the current namespace, set with @:namespace@, and the @use@s in
  effect (design §7.6); never stored
  -}
  }

{- | An expression as it was checked: its Core, types and Typed Core, and the
codebase it was checked against, whose terms it may reference after the
scratch that defined them has changed.
-}
data LastExpr = LastExpr
  { term :: Term Z
  , schemes :: [Scheme]
  , typed :: TTerm Z
  , base :: !Codebase
  }

emptySession :: Session
emptySession =
  Session
    emptyCodebase
    []
    Map.empty
    emptyCodebase
    defaultConfig
    Map.empty
    Nothing
    S.rootScope

{- | A session on a seeded codebase (design §7.7): the standard library
entered by domain as one group and added, with its six stored default
@use@s, as a new codebase starts and as @--no-codebase@ runs. Fails only if
the library itself does not check, which is a build error.
-}
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
      stmts <- parseProgram src
      -- Namespaces flattened (design §7.6): full paths, each with its scope.
      -- The top-level `use`s last for the session.
      let (decls, exprs, scope') = S.flatten session.scope stmts
      (session', notes) <-
        if null decls then Right (session, []) else propose session src decls
      -- Each expression that evaluates becomes `it` for the next one.
      let step (s, outs) (scope, e) = do
            (out, le) <- evalExpr s.config s.preferred scope (exprCodebase s) src e
            le' <- absorbLast s le
            pure (s{lastExpr = Just le'}, out : outs)
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
  (term, typed, _, linted) <- checkExpr scope cb src e
  let h = hashTerm term
  v <-
    either (Left . renderEvalError) Right (evalAt cfg (runtimeOf cfg cb) h typed)
  pure (h, v, LastExpr term linted typed cb)

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
      , scaleName = \h i written -> scaleNameFor (Reference h i) written cb
      , shared = (`Map.lookup` values)
      }
  values = LazyMap.mapWithKey (\h (_, t) -> evalAt cfg rt h t) cb.derived

{- | Desugar, typecheck, elaborate and lint an expression against a codebase.
Returns the Core, the Typed Core, the inferred type and the types lint
found, which are what a stored term carries.
-}
checkExpr ::
  S.Scope ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Term Z, TTerm Z, Maybe Scheme, [Scheme])
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
  (schemes, typed) <-
    either
      (Left . typeErr checkProv)
      Right
      (I.elaborateClosedWith (annotationsWith cb asc) (typeLookupFor cb) checkTerm)
  linted <-
    either
      (Left . ("internal error: elaboration produced ill-typed core: " <>))
      Right
      (lintClosed (typeLookupFor cb) typed)
  pure (term, typed, listToMaybe schemes, linted)
 where
  typeErr prov err = case provenanceAt err.path prov of
    Just (sp, hint) -> S.renderSpanError (Just src) sp (withHint hint err.message)
    Nothing -> S.renderSpanError (Just src) e.span err.message

-- Commands ----------------------------------------------------------------------

command :: Session -> Text -> [Text] -> Either Text (Session, [Text])
command session src = \case
  ["set"] ->
    keep
      ( Right
          [ "precision " <> tshow cfg.precision
          , "sigma " <> tshow cfg.sigma
          , "unicode " <> (if cfg.unicode then "on" else "off")
          ]
      )
  ["set", "precision", n] ->
    setting n (\k -> cfg{precision = k}) "precision must be a non-negative integer"
  ["set", "sigma", n] -> setting n (\k -> cfg{sigma = k}) "sigma must be a non-negative integer"
  -- Output spelling (design §2.8, §7.3).
  ["set", "unicode", "on"] -> Right (session{config = cfg{unicode = True}}, [])
  ["set", "unicode", "off"] -> Right (session{config = cfg{unicode = False}}, [])
  ["set", "unicode", _] -> Left "unicode is on or off"
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
        pure (renderBudget (inputNamer h) cfg.precision units (foldr addM (Exact 0) xs))
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
            covValue = covarianceMatrix (dimPow 2 d) covHint xs xs
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
                block d hh = covarianceMatrix d (unpinned hh)
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
  ("type" : rest) -> keep $ do
    e <- parseExpr (T.unwords rest)
    (_, _, ty, _) <- checkExpr scope ecb (T.unwords rest) e
    pure [maybe "" (renderForallIn spelling) ty]
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
  ["history", n] -> keep $ case historyOf (argIn cb n) cb of
    [] -> Left ("unknown name `" <> n <> "`")
    r : rs -> pure ((showReference r <> "  (current)") : map showReference rs)
  ["view", n] ->
    keep
      $ let full = argIn ecb n
         in case lookupName full ecb of
              -- A chart's right-hand side, `step at origin`, is not an
              -- expression, so it is viewed with its keyword (design §3.8).
              Just r ->
                (: [])
                  <$> definitionLine
                    spelling
                    scope
                    ecb
                    (if isScaleName full ecb then "chart " else "")
                    (short ecb full)
                    r
              Nothing -> viewData spelling scope cb full
  ["dependents", n] -> keep $ withName n $ \r -> pure (map (short cb) (dependents (argIn cb n) r.hash cb))
  -- An alias of a unit or chart is one too; an alias of a namespace aliases
  -- every label under it (design §7.6).
  ["alias", new, old]
    | Just r <- lookupName (argIn session.codebase old) session.codebase -> do
        let old' = argIn session.codebase old
            new' = newPath new
            flagged =
              (if isUnitName old' cb then markUnit new' else id)
                . (if isScaleName old' cb then markScale new' else id)
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
    Left
      ( "commands: :add  :update [--no-upgrade]  :upgrade name  :todo  :scratch  :forget name  :edit [name|namespace]  :type expr\n"
          <> "          :ls [glob|namespace] [--all|--units|--charts|--types] [: type]  :view name  :core name  :hash name  :names #hash\n"
          <> "          :history name  :dependents name  :alias new old  :unname name  :rename old new  :move name… namespace\n"
          <> "          :namespace [path|.]  :uses  :use path [as alias]  :unuse path  :export [namespace] [file]  :stdlib upgrade\n"
          <> "          :exact expr  :budget expr  :covariance expr  :set [precision n | sigma k | unicode on|off]  :prefer [unit]  :unprefer unit  :colour on|off"
      )
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
  setting n adjust err = case reads (T.unpack n) of
    [(k, "")] | k >= (0 :: Int) -> Right (session{config = adjust k}, [])
    _ -> Left err
  evalOf rest = do
    e <- parseExpr (T.unwords rest)
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
  withName n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName (argIn cb n) cb)
  withExprName n k =
    let full = argIn ecb n
     in maybe (Left ("unknown name `" <> n <> "`")) (k full) (lookupName full ecb)
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

{- | A name given to a command: relative to the current namespace, through
the uses, or absolute with a leading dot (design §7.6).
-}
argPath :: S.Scope -> Codebase -> Text -> Text
argPath scope c n
  | Just p <- T.stripPrefix "." n = p
  | otherwise = case qualifyWith c.uses known scope n of
      Found full -> full
      _ -> n
 where
  known x =
    isLabel TermLabel c x
      || isLabel TypeLabel c x
      || isLabel FieldLabel c x
      || Map.member x c.history
      || isNamespace c x

{- | A word naming a stored namespace: relative to the current one, else
from the root; absolute with a leading dot.
-}
namespaceArg :: Session -> Text -> Maybe Text
namespaceArg session w
  | Just p <- T.stripPrefix "." w = if isNamespace cb p then Just p else Nothing
  | not (null session.scope.namespace)
  , here <- S.qualify session.scope.namespace w
  , isNamespace cb here =
      Just here
  | isNamespace cb w = Just w
  | otherwise = Nothing
 where
  cb = session.codebase

-- | @namespace orbital@, or the root.
namespaceLine :: [Text] -> Text
namespaceLine = \case
  [] -> "namespace . (the root)"
  ns -> "namespace " <> T.intercalate "." ns

-- | @1 label@, @5 labels@.
labelsText :: Int -> Text
labelsText k = T.pack (show k) <> (if k == 1 then " label" else " labels")

-- | What a label names, for messages.
labelNoun :: Codebase -> Text -> Text
labelNoun cb n
  | Map.member n cb.names = "definition"
  | Map.member n cb.conNames = "constructor"
  | Map.member n cb.typeNames = "type"
  | Map.member n cb.fieldNames = "field"
  | otherwise = "name"

-- | The labels of each kind among some paths: a type and its constructor of one name are two.
labelKinds :: Codebase -> [Text] -> [(Text, LabelKind)]
labelKinds cb paths =
  [(p, k) | p <- paths, k <- [TermLabel, TypeLabel, FieldLabel], isLabel k cb p]

-- | Remove a label of every kind; history keeps it.
removeLabel :: Text -> Codebase -> Codebase
removeLabel n = unbindName n . unbindName ("." <> n)

{- | Relabel (design §7.2, §7.6): each new path gets the labels of every kind
its old path has, with their unit and chart flags, and unless aliasing the
old labels go. History keeps both. All or nothing: a new path that is
already a label of the same kind, two old paths given one new path, or a
new path that would be both a label and a namespace refuses the whole
change. Returns the codebase and the number of labels given.
-}
relabel :: Bool -> [(Text, Text)] -> Codebase -> Either Text (Codebase, Int)
relabel keepOld pairs cb = do
  let moves = [(o, n, k) | (o, n) <- pairs, (_, k) <- labelKinds cb [o]]
      base = if keepOld then cb else foldr (removeLabel . fst) cb pairs
      clashes =
        [ n
        | (i, (o, n, k)) <- zip [0 :: Int ..] moves
        , (o /= n && isLabel k base n)
            || any (\(_, n', k') -> n' == n && k' == k) (take i moves)
        ]
  case clashes of
    n : _ -> Left ("`" <> n <> "` is already a label; nothing was changed")
    [] -> Right ()
  case disjointness
    base
    [(n, labelNoun cb o, S.Span (S.Pos 1 1) (S.Pos 1 1)) | (o, n, _) <- moves] of
    Just (_, msg) -> Left (msg <> "; nothing was changed")
    Nothing -> Right ()
  pure (foldl copy base moves, length moves)
 where
  -- A signature moves with its name, and an alias, being the hash, is
  -- unsigned (design §4.8).
  copy acc (o, n, k) = case k of
    TermLabel
      | Just r <- lookupName o cb ->
          (if isUnitName o cb then markUnit n else id)
            . (if isScaleName o cb then markScale n else id)
            . maybe id (setSignature n) (if keepOld then Nothing else signatureOf o cb)
            $ bindName n r acc
      | Just (h, i) <- lookupConName o cb -> bindConName n h i acc
    TypeLabel | Just h <- lookupTypeName o cb -> bindTypeName n h acc
    FieldLabel | Just (h, i, j) <- lookupFieldName o cb -> bindFieldName n h i j acc
    _ -> acc

{- | @:edit@ (design §7.5): a stored definition or a data declaration as
source to paste back. A name outside the current namespace is printed in a
@namespace@ block, its names relative to that block (design §7.6), for
pasting at the root.
-}
editSource :: Spelling -> S.Scope -> Codebase -> Text -> Either Text [Text]
editSource spelling scope cb full
  | ns == scope.namespace = definitionSource spelling scope cb full
  | null ns = definitionSource spelling scope{S.namespace = []} cb full
  | otherwise =
      (\ls -> ("namespace " <> T.intercalate "." ns) : map ("  " <>) ls)
        <$> definitionSource spelling scope{S.namespace = ns} cb full
 where
  ns = init (T.splitOn "." full)

{- | A stored definition or data declaration as source in a scope: @let@,
@unit@ or @chart@ and the name relative to the scope's namespace, or the
@data@ declaration. Declared types are named in the scope too.
-}
definitionSource ::
  Spelling -> S.Scope -> Codebase -> Text -> Either Text [Text]
definitionSource spelling scope cb full = case lookupName full cb of
  Just r ->
    let keyword
          | isUnitName full cb = "unit "
          | isScaleName full cb = "chart "
          | otherwise = "let "
     in ( \line ->
            map
              (nameTypes scope cb)
              (signatureSource spelling cb full ++ [line])
        )
          <$> definitionLine spelling scope cb keyword (S.lastSegment full) r
  Nothing -> map (nameTypes scope cb) <$> viewData spelling scope cb full

{- | The line @name :: type@ that goes before a signed definition's @let@
in source (design §4.8), as a block of the scope writes it; none for a
name without a signature. Declared types print by hash, for 'nameTypes'.
-}
signatureSource :: Spelling -> Codebase -> Text -> [Text]
signatureSource spelling cb full =
  [ S.lastSegment full <> " :: " <> signatureText spelling sig
  | Just sig <- [signatureOf full cb]
  ]

-- | A declared type as it could be written again (design §7.2), named in a scope.
viewData :: Spelling -> S.Scope -> Codebase -> Text -> Either Text [Text]
viewData spelling scope cb n =
  case lookupTypeName n cb >>= \h -> (h,) <$> lookupTypeDef h cb of
    Just (h, def) ->
      pure
        [ renderTypeDef
            spelling
            (shortestNameOf TypeLabel scope cb n)
            [ maybe
                (showHash h <> "." <> T.pack (show i))
                (shortestName scope cb)
                (conNameOf h i cb)
            | i <- [0 .. length def.constructors - 1]
            ]
            [ map (fmap S.lastSegment) (fieldNamesOf h i (length fs) cb)
            | (i, fs) <- zip [0 ..] def.constructors
            ]
            def
        ]
    Nothing -> Left ("unknown name `" <> n <> "`")

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

{- | @area :: Shape -> Num [m^2]@: a name and its signature as written back
in a scope (design §4.8), the name by its shortest spelling.
-}
signatureLine :: Spelling -> S.Scope -> Codebase -> Text -> Text
signatureLine spelling scope cb n =
  shortestName scope cb n
    <> " :: "
    <> maybe "?" (signatureText spelling) (signatureOf n cb)

-- | What propagation did, with names spelled by the given namer (design §7.6).
upgradeReport :: (Text -> Text) -> Propagation -> [Text]
upgradeReport short result =
  [ "upgraded "
      <> short n
      <> " "
      <> showReference old
      <> " -> "
      <> showReference new
  | (n, old, new) <- result.upgraded
  ]
    ++ [ "left " <> short n <> " on " <> showReference r <> ": " <> why
       | (n, r, why) <- result.skipped
       ]

{- | Move every current definition still using an old version of a name to
its current version, where it typechecks.
-}
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
          . (if isScaleName n shipped then markScale n else id)
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

{- | Print the definition behind a reference (design §7.2). Cycle members
are shown one at a time, with the other members by name.
-}
viewReference ::
  Spelling -> S.Scope -> Codebase -> Reference -> Either Text Text
viewReference spelling scope cb (Reference h idx) = case lookupTerm h cb of
  Nothing -> Left ("missing term " <> showHash h)
  Just t -> case (idx, t) of
    (Nothing, _) -> Right (renderTermUnits spelling (refNamer scope cb) (unitRef cb) VNil t)
    (Just i, Cycle hints bodies) ->
      let memberName j (Hint hint) =
            shortestName
              scope
              cb
              (fromMaybe hint (listToMaybe (namesOf (Reference h (Just j)) cb)))
          ctx = vecAppend (vecMapIndexed memberName hints) VNil
       in case vecIndex i bodies of
            Just body -> Right (renderTermUnits spelling (refNamer scope cb) (unitRef cb) ctx body)
            Nothing -> Left ("no member " <> T.pack (show i) <> " in " <> showHash h)
    (Just _, _) -> Left (showHash h <> " is not a cycle")

{- | A definition as a line of source: its keyword, its name and its body.
A chart's leading lambdas are its parameters, written before the @=@
(@chart ecef t = …@, design §3.8), since a chart's right-hand side is not
an expression.
-}
definitionLine ::
  Spelling -> S.Scope -> Codebase -> Text -> Text -> Reference -> Either Text Text
definitionLine spelling scope cb keyword shown r = case (keyword, r.index, lookupTerm r.hash cb) of
  ("chart ", Nothing, Just t) ->
    let (ps, body) = renderParamsUnits spelling (refNamer scope cb) (unitRef cb) t
     in Right (keyword <> T.unwords (shown : ps) <> " = " <> body)
  _ ->
    (\body -> keyword <> shown <> " = " <> body)
      <$> viewReference spelling scope cb r

-- | Print the Typed Core behind a reference (design §5.3), for inspection.
viewTyped :: S.Scope -> Codebase -> Reference -> Either Text Text
viewTyped scope cb (Reference h idx) = case lookupTyped h cb of
  Nothing -> Left ("no typed core for " <> showHash h)
  Just t -> case (idx, t) of
    (Nothing, _) -> Right (renderTTerm (refNamer scope cb) VNil t)
    (Just i, TCycle _ members bodies) ->
      let memberName j (Hint hint, _) =
            shortestName
              scope
              cb
              (fromMaybe hint (listToMaybe (namesOf (Reference h (Just j)) cb)))
          ctx = vecAppend (vecMapIndexed memberName members) VNil
       in case vecIndex i bodies of
            Just body -> Right (renderTTerm (refNamer scope cb) ctx body)
            Nothing -> Left ("no member " <> T.pack (show i) <> " in " <> showHash h)
    (Just _, _) -> Left (showHash h <> " is not a cycle")

vecMapIndexed :: forall a b k. (Int -> a -> b) -> Vec k a -> Vec k b
vecMapIndexed f = go 0
 where
  go :: forall m. Int -> Vec m a -> Vec m b
  go _ VNil = VNil
  go i (VCons x xs) = VCons (f i x) (go (i + 1) xs)

{- | A current name, else a stale @name#hash@, else a bare @#hash@, each
spelled as shortly as the scope allows (design §7.6).
-}

-- | Whether a reference prints as a unit, for a chart's origin (design §3.8).
unitRef :: Codebase -> UnitRef
unitRef cb h idx written = isJust (unitNameFor (Reference h idx) written cb)

refNamer :: S.Scope -> Codebase -> RefNamer
refNamer scope cb h idx written =
  let r = Reference h idx
      short = shortestName scope cb
   in -- `it` only stands in when nothing else names the reference.
      case filter (/= "it") (namesOf r cb) ++ filter (== "it") (namesOf r cb) of
        -- The name the author wrote, while it still points here; else any current name.
        ns | written `elem` ns -> short written
        n : _ -> short n
        [] -> case historicalNamesOf r cb of
          n : _ -> short n <> showReference r
          [] -> showReference r

{- | How values print in a session: names for references, units and record
fields from the codebase, in the configured spelling. A record's fields
print by their last segment, as a record is built (design §7.6).
-}
printerFor :: Config -> S.Scope -> Codebase -> Printer
printerFor cfg scope cb =
  Printer
    { refName = refNamer scope cb
    , fieldNames = \h i arity -> map (fmap S.lastSegment) (fieldNamesOf h i arity cb)
    , spelling = spellingOf cfg
    , unitName = shortestName scope cb
    }

-- | The spelling output uses (design §7.3, @:set unicode@).
spellingOf :: Config -> Spelling
spellingOf cfg = if cfg.unicode then Unicode else Ascii

renderEvalError :: EvalError -> Text
renderEvalError = \case
  DivideByZero -> "error: division by zero"
  Domain msg -> "error: " <> msg
  Undecided msg -> "error: cannot decide " <> msg
  Internal msg -> "internal error: " <> msg
  UnknownRef h -> "error: unknown reference " <> showHash h
  BadCycleIndex i -> "error: bad cycle index " <> T.pack (show i)
  Unsupported msg -> "not implemented: " <> msg

{- | Evaluate a preference text (@km/h@) to the unit it names and the exact
dimension it applies to. It must be a scalar with a display unit.
-}
preferenceHint :: Config -> Codebase -> Text -> Either Text (Dim, UnitHint)
preferenceHint cfg cb text = do
  e <- parseExpr text
  (_, v) <- evalValue cfg S.rootScope cb text e
  case v of
    VTensor [] d (Just h) _ | h.dim == d -> Right (d, h)
    VTensor [] _ Nothing _ ->
      Left ("`" <> text <> "` has no unit to prefer; write one, as in :prefer km/h")
    _ -> Left ("a preference must be a scalar unit expression, not `" <> text <> "`")

{- | Recompute the evaluated preferences from the codebase's texts, as after a
load or a change. A text that no longer evaluates (its unit was unnamed) is
dropped from the evaluated set but kept in the codebase.
-}
refreshPreferences :: Session -> Either Text Session
refreshPreferences session =
  let hints =
        [ (d, h)
        | t <- Set.toList session.staging.preferences
        , Right (d, h) <- [preferenceHint session.config session.staging t]
        ]
   in Right session{preferred = Map.fromList hints}

{- | Declared types and their constructors print by hash (@#a3f9k@,
@#a3f9k.1@) wherever a type or a value is rendered; here those become the
current names (design §7.2), spelled for the scope (design §7.6). A type
without a name keeps its hash.
-}
nameTypes :: S.Scope -> Codebase -> Text -> Text
nameTypes scope cb
  | Map.null cb.typeDefs = id
  | otherwise = go
 where
  go t = case T.breakOn "#" t of
    (before, rest) | T.null rest -> before
    (before, rest) ->
      let (hex, after) = T.span isBase32 (T.drop 1 rest)
          (idx, after') = case T.uncons after of
            Just ('.', more)
              | (ds, more') <- T.span isDigit more
              , not (T.null ds) ->
                  (Just (read (T.unpack ds) :: Int), more')
            _ -> (Nothing, after)
       in case [h | h <- Map.keys cb.typeDefs, showHash h == "#" <> hex] of
            h : _
              | Just i <- idx
              , Just c <- conNameOf h i cb ->
                  before <> shortestName scope cb c <> go after'
              | Nothing <- idx
              , Just n <- typeNameOf h cb ->
                  before <> shortestNameOf TypeLabel scope cb n <> go after'
            _ -> before <> "#" <> go (T.drop 1 rest)
  isBase32 c = isDigit c || (c >= 'a' && c <= 'v')

{- | @:ls [glob|namespace] [--all | --units | --charts | --types] [: type]@
(design §7.3): names in the codebase with their types, one per line,
sorted. Alone, the current namespace's own labels (the root's at the
root), then a line for each namespace directly under it with the number of
names in it (@namespace si (800 names)@). A word that names a namespace
lists everything under it, relative to it; @--all@ lists everything by its
full path; a glob (@*@ anywhere, else a case-insensitive substring; on the
full path or its last segment), a
kind flag or a type query searches everything. The type query is a written
type whose unknown names are variables, matched by unification both ways,
so @: a -> a@ finds @Num [m] -> Num [m]@ and @: Num -> Num@ finds @a -> a@.
-}
listNames :: Session -> [Text] -> Either Text [Text]
listNames session args = do
  let (before, after) = break (== ":") args
      -- @--scales@ is the old spelling of @--charts@ (design §3.6).
      flags =
        map
          (\f -> if f == "--scales" then "--charts" else f)
          (filter (T.isPrefixOf "--") before)
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
        | "--charts" `elem` flags = isScaleName n cb
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
        Just sc <- [signatureOf n cb <|> typeOf r cb]
        , typeOk sc
        ]
      types =
        [ line
        | "--units" `notElem` flags
        , "--charts" `notElem` flags
        , (n, h) <- sortOn (T.toLower . fst) (Map.toList cb.typeNames)
        , Just def <- [lookupTypeDef h cb]
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
    | isScaleName n cb = "chart "
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

-- Export (design §7.4) --------------------------------------------------------------

{- | @:export [path] [file]@: what to export and where. No argument, or
@.@, is the whole codebase; a word that names a namespace (relative to the
current one, or absolute) is that namespace; any other single word is the
file when it looks like a path (it has a @/@ or a @.@), and otherwise most
likely a misspelt namespace, which is refused rather than written to a
file of that name. With two words, the first is the path and the second
the file. Returns the file, if any, and the source.
-}
exportRequest :: Session -> [Text] -> Either Text (Maybe FilePath, Text)
exportRequest session = \case
  [] -> (Nothing,) <$> exportSource session Nothing
  [w]
    | w == "." -> (Nothing,) <$> exportSource session Nothing
    | Just ns <- namespaceArg session w ->
        (Nothing,) <$> exportSource session (Just ns)
    | T.any (`elem` ['/', '.']) w ->
        (Just (T.unpack w),) <$> exportSource session Nothing
    | otherwise ->
        Left
          ( "`"
              <> w
              <> "` is not a namespace; to write a file give a path like "
              <> w
              <> ".ev"
          )
  [p, f]
    | p == "." -> (Just (T.unpack f),) <$> exportSource session Nothing
    | Just ns <- namespaceArg session p ->
        (Just (T.unpack f),) <$> exportSource session (Just ns)
    | otherwise -> Left ("`" <> p <> "` is not a namespace")
  _ -> Left "usage: :export [namespace] [file]"

{- | The stored codebase, or the namespace at a path, as source that @:load@
reads back (design §7.4): every label, except the standard library's namespaces
unless one is the path asked for, as a @namespace@ block per
namespace, nested as the paths nest, with root definitions outside any
block. The codebase's stored @use@s head it as @use@ statements (design
§7.7), and every name is spelled for them: a @use@ in a file comes before
the root, so a root name that a stored @use@ also offers prints with its
leading dot, and the text means the same in any codebase that has the
library. Types come first, each after the types it uses, then the terms,
each after what it references and a cycle's members together. Inside a
block, names print as that block's scope spells them (design §7.6). The
pending scratch is not exported; a closing comment says so. A definition
that refers to a version no name points at any more cannot be written as
source, and refuses the export.
-}
exportSource :: Session -> Maybe Text -> Either Text Text
exportSource session = \case
  Just p -> exportLabels session ((p <> ".") `T.isPrefixOf`)
  Nothing -> exportLabels session (not . isLibraryPath)

{- | 'exportSource' for the labels whose full paths pass a test: the
definitions, and the types with their constructors and fields.
-}
exportLabels :: Session -> (Text -> Bool) -> Either Text Text
exportLabels session under = do
  case [ (n, r)
       | (n, Reference h _) <- terms
       , Just t <- [lookupTerm h cb]
       , r <- Set.toList (refsWithIndex t)
       , null (namesOf (uncurry Reference r) cb)
       ] of
    (n, (h, i)) : _ ->
      Left
        ( "cannot export: `"
            <> n
            <> "` uses "
            <> refNamer S.rootScope cb h i ""
            <> ", which no name points at; :upgrade or :update it first"
        )
    [] -> Right ()
  typeItems <- mapM typeItem orderedTypes
  termItems <- concat <$> mapM termItems' orderedTerms
  let body = nest [] (typeItems ++ termItems)
      header = ["use " <> S.renderUse u | not (null body), u <- stored]
      pendingNote =
        [ "-- not exported: "
            <> T.pack (show (Set.size (Set.fromList (map (.name.text) session.scratch))))
            <> " pending definitions (:add or :update them first)"
        | not (null session.scratch)
        ]
  pure (T.intercalate "\n" (header ++ body ++ pendingNote))
 where
  -- The stored uses are written as statements, so they spell the names as
  -- a file's uses do, before the root, and not as the codebase's fallback.
  stored = session.codebase.uses
  cb = session.codebase{uses = []}
  terms = [(n, r) | (n, r) <- Map.toList cb.names, under n]
  types = [(n, h) | (n, h) <- Map.toList cb.typeNames, under n]
  namespaceOf n = init (T.splitOn "." n)
  -- Types after the types their fields use.
  orderedTypes =
    dependencyOrder
      [ ((n, h), n, maybe [] (defRefs h) (lookupTypeDef h cb))
      | (n, h) <- types
      ]
  defRefs self def =
    let used = Set.delete self (foldMap (foldMap typeRefs) def.constructors)
     in [n | (n, h) <- types, h `Set.member` used]
  typeItem (n, _) =
    let scope = S.Scope (namespaceOf n) stored
     in (namespaceOf n,) . map (nameTypes scope cb) <$> viewData Ascii scope cb n
  -- Terms by hash, so that a cycle's members and aliases stay together,
  -- after what they reference.
  byHash = Map.fromListWith (++) [(r.hash, [(n, r)]) | (n, r) <- terms]
  keyOf = Map.map (minimum . map fst) byHash
  orderedTerms =
    dependencyOrder
      [ ( sortOn (\(n, r) -> (r.index, n)) members
        , Map.findWithDefault "" h keyOf
        , maybe
            []
            (mapMaybe (`Map.lookup` keyOf) . Set.toList . Set.delete h . refs)
            (lookupTerm h cb)
        )
      | (h, members) <- Map.toList byHash
      ]
  termItems' = mapM $ \(n, r) ->
    let scope = S.Scope (namespaceOf n) stored
        keyword
          | isUnitName n cb = "unit "
          | isScaleName n cb = "chart "
          | otherwise = "let "
     in ( \line ->
            ( namespaceOf n
            , map
                (nameTypes scope cb)
                (signatureSource Ascii cb n ++ [line])
            )
        )
          <$> definitionLine Ascii scope cb keyword (S.lastSegment n) r
  -- Open and close blocks as the namespaces of consecutive items change.
  nest :: [Text] -> [([Text], [Text])] -> [Text]
  nest _ [] = []
  nest current ((ns, ls) : rest) =
    let common = length (takeWhile id (zipWith (==) current ns))
        opens =
          [ indent k <> "namespace " <> seg
          | (k, seg) <- zip [common ..] (drop common ns)
          ]
     in opens ++ map (indent (length ns) <>) ls ++ nest ns rest
  indent k = T.replicate (2 * k) " "

{- | Dependencies first; among what is ready, what stays in the namespace of
the last item, then by namespace and name, so that an export reopens as few
blocks as it can (design §7.4). Each node is an item, its key (a full
path) and the keys it depends on; mutually dependent nodes come out
together.
-}
dependencyOrder :: [(a, Text, [Text])] -> [a]
dependencyOrder nodes = map fst (go [] Set.empty (Map.keysSet comps))
 where
  comps =
    Map.fromList
      ( zip
          [0 :: Int ..]
          (map flattenSCC (stronglyConnComp [((a, k), k, ds) | (a, k, ds) <- nodes]))
      )
  compOf = Map.fromList [(k, i) | (i, members) <- Map.toList comps, (_, k) <- members]
  depsOf = Map.fromList [(k, ds) | (_, k, ds) <- nodes]
  compDeps i =
    Set.delete
      i
      ( Set.fromList
          [ j
          | (_, k) <- Map.findWithDefault [] i comps
          , d <- Map.findWithDefault [] k depsOf
          , Just j <- [Map.lookup d compOf]
          ]
      )
  key i = minimum (map snd (Map.findWithDefault [] i comps))
  space i = init (T.splitOn "." (key i))
  go current done remaining
    | Set.null remaining = []
    | otherwise =
        let ready = [i | i <- Set.toList remaining, compDeps i `Set.isSubsetOf` done]
            pick = case sortOn (\i -> (space i /= current, space i, key i)) ready of
              i : _ -> i
              -- Not reachable: the components form a DAG.
              [] -> Set.findMin remaining
         in Map.findWithDefault [] pick comps
              ++ go (space pick) (Set.insert pick done) (Set.delete pick remaining)

-- | The declared types a type mentions.
typeRefs :: Type -> Set.Set Hash
typeRefs = \case
  TData h args -> Set.insert h (foldMap argRefs args)
  TFun a b -> typeRefs a <> typeRefs b
  _ -> Set.empty
 where
  argRefs = \case
    AType t -> typeRefs t
    _ -> Set.empty

-- Edit (design §7.3) ----------------------------------------------------------------

-- | What an @:edit@ round trip covers (design §7.3).
data EditScope
  = -- | @:edit@: the stored codebase but the library under @std@
    EditCodebase
  | -- | @:edit orbital@: the labels under a namespace, by its full path
    EditNamespace Text
  | -- | @:edit period@: one definition or type, by its full path; nothing is removed
    EditName Text
  deriving stock (Eq, Show)

-- | What @:edit …@ asks for.
data EditRequest
  = {- | Open an editor on the scope: the file to open (or why there is
    none), and what to print instead when there is no editor.
    -}
    EditOpen EditScope (Either Text Text) [Text]
  | -- | @:edit --file path@: reconcile the file as it is, without an editor.
    EditResume EditScope FilePath
  deriving stock (Eq, Show)

{- | @:edit [name|namespace]@ and @:edit --file path [name|namespace]@
(design §7.3). No argument, or @.@, is the codebase without @std@; a word
naming a stored namespace (relative to the current one, else from the
root, or absolute with a leading dot) is that namespace; any other word is
a definition or type. The file is the scope as 'exportSource' writes it,
under a header that says what saving does. What prints without an editor
is the source it would open: for one name, the pasteable statement
@:edit@ always printed (spelled for the session, and a pending definition
too); for a namespace or the codebase, the export.
-}
editRequest :: Session -> [Text] -> Either Text EditRequest
editRequest session = \case
  "--file" : p : rest -> (`EditResume` T.unpack p) <$> scopeOf rest
  ["--file"] -> Left usage
  args -> do
    target <- scopeOf args
    case target of
      EditName full -> do
        paste <-
          editSource (spellingOf session.config) session.scope session.staging full
        pure (EditOpen target (editFile session target) paste)
      _ -> do
        file <- editFile session target
        body <- editBody session target
        pure (EditOpen target (Right file) [body | not (T.null body)])
 where
  usage = "usage: :edit [name|namespace], or :edit --file path [name|namespace]"
  scopeOf = \case
    [] -> Right EditCodebase
    ["."] -> Right EditCodebase
    [w]
      | Just ns <- namespaceArg session w -> Right (EditNamespace ns)
      | otherwise -> Right (EditName (argPath session.scope session.staging w))
    _ -> Left usage

-- | The scope as the source 'exportSource' writes.
editBody :: Session -> EditScope -> Either Text Text
editBody session = \case
  EditCodebase -> exportSource session Nothing
  EditNamespace ns -> exportSource session (Just ns)
  -- A cycle's members come together: one alone would re-enter as another term.
  EditName full -> exportLabels session $ case lookupName full session.codebase of
    Just (Reference h (Just _)) ->
      \n -> n == full || ((.hash) <$> lookupName n session.codebase) == Just h
    _ -> (== full)

-- | The file an editor opens: a header saying what saving does, then the source.
editFile :: Session -> EditScope -> Either Text Text
editFile session target = do
  case target of
    EditName full
      | not (isLabel TermLabel cb full || isLabel TypeLabel cb full) ->
          Left
            ( "`"
                <> shortestName session.scope session.staging full
                <> "` is not stored; :add or :update it before editing it in place"
            )
    _ -> Right ()
  body <- editBody session target
  pure (T.unlines (editHeader target ++ [body | not (T.null body)]))
 where
  cb = session.codebase

-- | What saving the file does (design §7.3), as comments.
editHeader :: EditScope -> [Text]
editHeader target =
  map
    ("-- " <>)
    ( [ ":edit" <> args <> ": " <> what <> " as source."
      , "When you save and quit, the file is entered as one group, all or nothing:"
      , "  a definition or type that is new is added;"
      , "  one whose text changed is updated, and its dependents upgraded, as :update does;"
      ]
        ++ removal
        ++ [ "Blocks are full paths from the root: the current :namespace does not change"
           , "what this file means."
           , "On an error nothing changes, and the file is kept to fix and resume with"
           , ":edit --file. Quit without saving to change nothing."
           ]
    )
 where
  (args, what) = case target of
    EditCodebase -> ("", "the codebase, but the library under std,")
    EditNamespace ns -> (" " <> ns, "the namespace " <> ns)
    EditName full -> (" " <> full, full)
  removal = case target of
    EditName full ->
      [ "  nothing is removed; deleting " <> full <> " is refused (:unname removes it)."
      ]
    _ ->
      [ "  a label here that the file no longer defines is removed, as :unname does;"
      , "  history keeps it. A definition moved to another namespace block is removed"
      , "  and added under its new path. Deleting everything is refused."
      ]

{- | The arguments that name a scope again in a command, @ orbital@; with a
leading dot outside the root, where a word is relative.
-}
editScopeArgs :: Session -> EditScope -> Text
editScopeArgs session = \case
  EditCodebase -> ""
  EditNamespace ns -> " " <> dotted ns
  EditName full -> " " <> dotted full
 where
  dotted p = if null session.scope.namespace then p else "." <> p

{- | The note under what @:edit@ prints when it opens no editor (scripted,
one-shot, or no @VISUAL@ or @EDITOR@), saying why.
-}
editorNote :: Text -> Text
editorNote why = "note: " <> why <> "; this is the source :edit would open"

{- | Reconcile an edited file with the codebase (design §7.3). The file is
read as a program from the root with no @use@ of the session, as it was
written: its own @use@ lines and @namespace@ blocks say what every name
means. Its definitions and types are entered as one group on top of the
codebase. By full path: a label the file defines that the codebase did
not have is added; one bound to another reference is updated, or
upgraded when its old term with the group's new references put in is the
new term (only what it uses moved); a label of the scope (a definition,
type, constructor or field) that the file does not define is removed, as
@:unname@ does, except for one name, where nothing is removed. Then
propagation moves the dependents outside the file, as @:update@ does. All
or nothing: a parse, type or namespace error, an expression, a file that
no longer defines the one name, one that would remove every label of the
scope, or a pending scratch that would no longer check, changes nothing.
-}
applyEdit :: EditScope -> Text -> Session -> Either Text (Session, [Text])
applyEdit target text session = case reconcile of
  Left err -> Left (nameTypes session.scope naming err)
  Right (s, outs) -> Right (s, map (nameTypes s.scope s.staging) outs)
 where
  cb0 = session.codebase
  -- An error names the file's own types, as the staging codebase does for
  -- an input.
  naming = case parseProgram text of
    Right stmts ->
      let (decls, _, _) = S.flatten S.rootScope stmts
       in fromRight cb0 (processGroup cb0 [d | d@(S.DData _ _) <- decls])
    Left _ -> cb0
  short0 = shortestName session.scope cb0
  inTarget n = case target of
    EditCodebase -> not (isLibraryPath n)
    EditNamespace ns -> (ns <> ".") `T.isPrefixOf` n
    EditName _ -> False
  scopeText = case target of
    EditCodebase -> "the codebase"
    EditNamespace ns -> "`" <> ns <> "`"
    EditName full -> "`" <> short0 full <> "`"
  reconcile = do
    stmts <- parseProgram text
    let (decls, exprs, _) = S.flatten S.rootScope stmts
    case exprs of
      (_, e) : _ ->
        Left
          ( S.renderSpanError
              (Just text)
              e.span
              "an edited file holds definitions; evaluate expressions at the prompt"
          )
      [] -> Right ()
    case [b.name | S.DBind _ b <- decls, b.name.text == "it"] of
      n : _ ->
        Left
          ( S.renderSpanError
              (Just text)
              n.span
              "`it` is the last result and cannot be defined; choose another name"
          )
      [] -> Right ()
    -- A definition the file writes without its signature line loses its
    -- signature (design §4.8), before the group is checked against it.
    let fileSigned = [n.text | S.DSig _ n _ <- decls]
        unsigned =
          [ b.name.text
          | S.DBind _ b <- decls
          , isJust (signatureOf b.name.text cb0)
          , b.name.text `notElem` fileSigned
          ]
    staged <-
      first
        (renderResolveErrorWith Map.empty text)
        (processGroup (foldr dropSignature cb0 unsigned) decls)
    let defined = Set.fromList (concatMap declLabels decls)
    case target of
      EditName full
        | not
            (Set.member (TermLabel, full) defined || Set.member (TypeLabel, full) defined) ->
            Left
              ( "the file no longer defines `"
                  <> short0 full
                  <> "`; use :unname to remove it"
              )
      _ -> Right ()
    let inScope =
          [ (k, n)
          | (k, ns) <-
              [ (TermLabel, Map.keys cb0.names ++ Map.keys cb0.conNames)
              , (TypeLabel, Map.keys cb0.typeNames)
              , (FieldLabel, Map.keys cb0.fieldNames)
              ]
          , n <- ns
          , inTarget n
          ]
        removed = filter (`Set.notMember` defined) inScope
    when (not (null inScope) && length removed == length inScope)
      $ Left
        ( "the file defines nothing in "
            <> scopeText
            <> "; if you mean to remove it all, use :unname"
            <> ( case target of
                   EditNamespace ns -> " " <> ns
                   _ -> " on its names and namespaces"
               )
        )
    let termNames = [b.name.text | S.DBind _ b <- decls]
        added = [n | n <- termNames, isNothing (lookupName n cb0)]
        changed =
          [ (n, old, new)
          | n <- termNames
          , Just old <- [lookupName n cb0]
          , Just new <- [lookupName n staged]
          , old /= new
          ]
        refmap = Map.fromList [(old, new) | (_, old, new) <- changed]
        written = Map.fromListWith Set.union [(old, Set.singleton n) | (n, old, _) <- changed]
        dataNames = [d.name.text | S.DData _ d <- decls]
        -- The types the file replaced, and their constructors by name.
        replaced =
          [ (n, old, new)
          | n <- dataNames
          , Just old <- [lookupTypeName n cb0]
          , Just new <- [lookupTypeName n staged]
          , old /= new
          ]
        cons =
          Map.fromList
            [ (old, new)
            | (c, old@(h, _)) <- Map.toList cb0.conNames
            , h `elem` [o | (_, o, _) <- replaced]
            , Just new <- [lookupConName c staged]
            ]
        newCon = \case
          UserCon h i | Just (h', i') <- Map.lookup (h, i) cons -> UserCon h' i'
          c -> c
        -- Only what it uses moved: its old term with the new references and
        -- constructors put in is the new term.
        follows (_, old, new) = case lookupTerm old.hash cb0 of
          Just t ->
            hashTerm
              ( rewriteRefsWritten
                  ( \rh ri w ->
                      if appliesTo cb0 written (Reference rh ri) w
                        then (\(Reference nh ni) -> (nh, ni)) <$> Map.lookup (Reference rh ri) refmap
                        else Nothing
                  )
                  (restampTerm id newCon t)
              )
              == new.hash
          Nothing -> False
        (followed, updated) = partition follows changed
        -- A body unchanged under another keyword: @unit km@ became @let km@.
        keyword c n
          | isUnitName n c = "unit"
          | isScaleName n c = "chart"
          | otherwise = "let" :: Text
        rekeyed =
          [ "updated " <> short n <> ": " <> keyword cb0 n <> " -> " <> keyword staged n
          | n <- termNames
          , isJust (lookupName n cb0)
          , lookupName n cb0 == lookupName n staged
          , keyword cb0 n /= keyword staged n
          ]
        types =
          [ ( if Map.member n cb0.typeNames
                then "updated data "
                else "added data "
            )
              <> shortestNameOf TypeLabel session.scope staged n
          | n <- dataNames
          , lookupTypeName n cb0 /= lookupTypeName n staged
          ]
        -- A type outside the file whose fields use a replaced type keeps
        -- the old one.
        typesLeft =
          [ "left data "
              <> shortestNameOf TypeLabel session.scope final n
              <> " on the old version of "
              <> shortestNameOf TypeLabel session.scope final r
          | (n, h) <- Map.toList final.typeNames
          , n `notElem` dataNames
          , Just def <- [lookupTypeDef h final]
          , let used = foldMap (foldMap typeRefs) def.constructors
          , (r, old, _) <- replaced
          , Set.member old used
          ]
        -- A removed type takes its constructors and fields with it.
        goneTypes =
          Set.fromList [h | (TypeLabel, n) <- removed, Just h <- [lookupTypeName n cb0]]
        removals =
          [ line
          | (k, n) <- removed
          , line <- case k of
              TermLabel
                | Map.member n cb0.names -> ["removed " <> short0 n]
                | Just (h, _) <- lookupConName n cb0
                , not (Set.member h goneTypes) ->
                    ["removed constructor " <> short0 n]
              TypeLabel -> ["removed data " <> shortestNameOf TypeLabel session.scope cb0 n]
              FieldLabel
                | Just (h, _, _) <- lookupFieldName n cb0
                , not (Set.member h goneTypes) ->
                    ["removed field " <> n]
              _ -> []
          ]
        result =
          propagateScoped
            (appliesTo cb0 written)
            cons
            refmap
            (foldr removeKind staged removed)
        final = result.codebase
        short = shortestName session.scope final
        -- Dependents of what was removed are left on it.
        removedTerms = Set.fromList [n | (TermLabel, n) <- removed, Map.member n cb0.names]
        staleBefore = Set.fromList (staleReferences cb0)
        stale =
          [ "left "
              <> short n
              <> " stale: it uses "
              <> short0 m
              <> showReference r
              <> ", which was removed"
          | entry@(n, r, m) <- staleReferences final
          , Set.notMember entry staleBefore
          , Set.member m removedTerms
          ]
        report =
          types
            ++ ["added " <> short n | n <- added]
            ++ [ "updated " <> short n <> " " <> showReference old <> " -> " <> showReference new
               | (n, old, new) <- updated
               ]
            ++ rekeyed
            ++ removals
            ++ [ "upgraded "
                   <> short n
                   <> " "
                   <> showReference old
                   <> " -> "
                   <> showReference new
               | (n, old, new) <- followed
               ]
            ++ upgradeReport short result
            ++ typesLeft
            ++ stale
            ++ signatureChanges
        -- Signatures given, changed or taken away on names still defined (design §4.8).
        signatureChanges =
          [ (if isJust new then "signed " else "unsigned ") <> short n
          | n <- Set.toList (Map.keysSet cb0.signatures <> Map.keysSet final.signatures)
          , Map.member n final.names
          , let new = signatureOf n final
          , -- A signature that only followed a replaced type is unchanged.
          ( retypeScheme (Map.fromList [(o, nw) | (_, o, nw) <- replaced])
              <$> signatureOf n cb0
          )
            /= new
          ]
    if null report
      then Right (session, ["nothing changed"])
      else do
        staging' <-
          first
            ( \err ->
                "the pending definitions would not check after this edit; nothing was changed:\n"
                  <> renderResolveError err
            )
            (processGroup final session.scratch)
        s <- refreshPreferences session{codebase = final, staging = staging'}
        pure (s, report)

-- | The labels a declaration defines, by kind and full path.
declLabels :: S.Decl -> [(LabelKind, Text)]
declLabels = \case
  S.DBind _ b -> [(TermLabel, b.name.text)]
  S.DData _ d ->
    (TypeLabel, d.name.text)
      : [(TermLabel, c.text) | (c, _) <- d.constructors]
      ++ [(FieldLabel, n.text) | (_, fs) <- d.constructors, S.FieldDecl (Just n) _ <- fs]
  -- A signature labels nothing: it belongs to its definition (design §4.8).
  S.DSig{} -> []

-- | Remove one label of one kind; history keeps a definition's.
removeKind :: (LabelKind, Text) -> Codebase -> Codebase
removeKind (k, n) cb = case k of
  TermLabel ->
    cb
      { names = Map.delete n cb.names
      , units = Set.delete n cb.units
      , scales = Set.delete n cb.scales
      , conNames = Map.delete n cb.conNames
      , signatures = Map.delete n cb.signatures
      }
  TypeLabel -> cb{typeNames = Map.delete n cb.typeNames}
  FieldLabel -> unbindName ("." <> n) cb

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
