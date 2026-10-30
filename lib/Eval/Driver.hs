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
  emptySession,
  preludeSession,
  feed,
  refreshPreferences,
) where

import Data.List (partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Eval.Affine (
  Collapsed (..),
  Magnitude (..),
  addM,
  collapse,
  statCoefficients,
 )
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Dimension (Dim, dimPow, renderDim)
import Eval.Eval
import Eval.Hash (hashTerm, showHash)
import Eval.Infer qualified as I
import Eval.Parser (parseExpr, parseProgram)
import Eval.Prelude (preludeSource)
import Eval.Pretty
import Eval.Resolve
import Eval.Syntax qualified as S
import Eval.TCore
import Eval.Type (renderScheme)
import Eval.Update

data Session = Session
  { codebase :: Codebase
  , scratch :: [S.Binding]
  -- ^ pending definitions, oldest first
  , sources :: Map Text Text
  -- ^ the input text each pending definition came from, for error excerpts
  , staging :: Codebase
  -- ^ codebase with the scratch entered on top; what expressions see
  , config :: Config
  , preferred :: Preferences
  {- ^ the codebase's preference texts, evaluated to hints keyed by dimension (design §3.2.12)
  ^ evaluation settings, changed with @:set@
  -}
  }

emptySession :: Session
emptySession = Session emptyCodebase [] Map.empty emptyCodebase defaultConfig Map.empty

{- | A session with the prelude (design §3.2.11) entered and added, as every
interactive session starts. Fails only if the prelude itself does not
check, which is a build error.
-}
preludeSession :: Either Text Session
preludeSession = do
  (s, _) <- feed emptySession preludeSource
  (s', _) <- feed s ":add"
  pure s'

{- | Parse and run one input (a line, a file). Returns the new session and
the lines to print, or the first error.
-}
feed :: Session -> Text -> Either Text (Session, [Text])
feed session src
  | Just cmd <- T.stripPrefix ":" (T.stripStart src) =
      command session src (T.words cmd)
  | otherwise = do
      stmts <- parseProgram src
      let lets = [b | S.SLet b <- stmts]
          exprs = [e | S.SExpr e <- stmts]
      (session', notes) <-
        if null lets then Right (session, []) else propose session src lets
      outs <-
        mapM (evalExpr session'.config session'.preferred session'.staging src) exprs
      pure (session', notes ++ outs)

{- | Put definitions into the scratch. A name already pending is replaced
(the scratch is a workspace, not a scope); a name defined twice in one
input is an error. The whole scratch is re-entered on top of the codebase
so that errors surface now.
-}
propose :: Session -> Text -> [S.Binding] -> Either Text (Session, [Text])
propose session src lets = do
  let incoming = map (.name.text) lets
      (replaced, kept) = partition (\b -> b.name.text `elem` incoming) session.scratch
      scratch' = kept ++ lets
      sources' = foldr (\b -> Map.insert b.name.text src) session.sources lets
  staging' <-
    either
      (Left . renderResolveErrorWith sources' src)
      Right
      (processGroup session.codebase scratch')
  let notes = ["replaced pending definition of `" <> b.name.text <> "`" | b <- replaced]
  pure
    (session{scratch = scratch', sources = sources', staging = staging'}, notes)

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
  err@(LintFailure _ _) -> renderResolveError err

-- | Desugar, typecheck and elaborate, lint, evaluate, print.
evalExpr ::
  Config -> Preferences -> Codebase -> Text -> S.Expr -> Either Text Text
evalExpr cfg prefs cb src e = do
  (_, v) <- evalValue cfg cb src e
  either
    (Left . renderEvalError)
    Right
    (renderValue (refNamer cb) cfg.precision prefs v)

{- | Evaluate an expression. An expression typed at the prompt belongs to no
definition; its own hash stands in as the site of any @±@ in it (design
§3.2.4), so re-evaluating the same text gives the same nudges.
-}
evalValue :: Config -> Codebase -> Text -> S.Expr -> Either Text (Hash, Value)
evalValue cfg cb src e = do
  (term, typed, _) <- checkExpr cb src e
  let h = hashTerm term
  (h,)
    <$> either (Left . renderEvalError) Right (evalAt cfg (runtimeOf cb) h typed)

runtimeOf :: Codebase -> Runtime
runtimeOf cb =
  Runtime
    { typedOf = (`lookupTyped` cb)
    , unitName = \h i written -> unitNameFor (Reference h i) written cb
    , scaleName = \h i written -> scaleNameFor (Reference h i) written cb
    }

{- | Desugar, typecheck, elaborate and lint an expression against a codebase.
Returns the Core, the Typed Core and the printed type.
-}
checkExpr :: Codebase -> Text -> S.Expr -> Either Text (Term Z, TTerm Z, Text)
checkExpr cb src e = do
  (term, prov) <-
    either
      (Left . renderResolveErrorWith Map.empty src . Desugar)
      Right
      (desugarClosed (resolverFor cb) e)
  (schemes, typed) <-
    either (Left . typeErr prov) Right (I.elaborateClosed (typeLookupFor cb) term)
  _ <-
    either
      (Left . ("internal error: elaboration produced ill-typed core: " <>))
      Right
      (lintClosed (typeLookupFor cb) typed)
  pure (term, typed, maybe "" renderScheme (listToMaybe schemes))
 where
  typeErr prov err =
    S.renderSpanError
      (Just src)
      (fromMaybe e.span (Map.lookup err.path prov))
      err.message

-- Commands ----------------------------------------------------------------------

command :: Session -> Text -> [Text] -> Either Text (Session, [Text])
command session src = \case
  ["set"] ->
    keep (Right ["precision " <> tshow cfg.precision, "sigma " <> tshow cfg.sigma])
  ["set", "precision", n] ->
    setting n (\k -> cfg{precision = k}) "precision must be a non-negative integer"
  ["set", "sigma", n] -> setting n (\k -> cfg{sigma = k}) "sigma must be a non-negative integer"
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
      (refreshed, ["values of dimension " <> renderDim d <> " print in " <> text])
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
            (inputNamer h)
            cfg.precision
            session.preferred
            (renderExact (inputNamer h) cfg.precision)
            v
        )
  -- The error budget (design §3.2.6) of a scalar, or of the sum of a
  -- tensor's components.
  ("budget" : rest) -> keep $ do
    (h, v) <- evalOf rest
    case displayParts (inputNamer h) cfg.precision session.preferred v of
      Right (_, xs, units) ->
        pure (renderBudget (inputNamer h) cfg.precision units (foldr addM (Exact 0) xs))
      Left (Internal _) -> Left "budget: not a number"
      Left err -> Left (renderEvalError err)
  -- The covariance view (design §3.5): Σ cᵢcᵢᵀ over the statistical nudges of
  -- a vector, with the bound radii beside it as a bias box.
  ("covariance" : rest) -> keep $ do
    (h, v) <- evalOf rest
    case v of
      VTensor dims d hint buf | length dims <= 1 -> do
        xs <- either (Left . renderEvalError) Right (sequence (V.toList buf))
        let n = length xs
            cols = map statCoefficients xs
            cov i j = Exact (sum (Map.elems (Map.intersectionWith (*) (cols !! i) (cols !! j))))
            covValue =
              VTensor
                [n, n]
                (dimPow 2 d)
                ((\hh -> hh{pinned = False}) <$> (hintPow (precisionOf cfg) 2 =<< hint))
                (V.fromList [Right (cov i j) | i <- [0 .. n - 1], j <- [0 .. n - 1]])
            bounds = VTensor dims d hint (V.fromList [Right (Exact (collapse x).bound) | x <- xs])
        let scalarVar =
              VTensor
                []
                (dimPow 2 d)
                ((\hh -> hh{pinned = False}) <$> (hintPow (precisionOf cfg) 2 =<< hint))
                (V.singleton (Right (cov 0 0)))
        covText <-
          either
            (Left . renderEvalError)
            Right
            ( renderValue
                (inputNamer h)
                cfg.precision
                session.preferred
                (if null dims then scalarVar else covValue)
            )
        boundText <-
          either
            (Left . renderEvalError)
            Right
            ( renderValueWith
                (inputNamer h)
                cfg.precision
                session.preferred
                renderRough
                bounds
            )
        pure
          [ (if null dims then "variance " else "covariance ") <> covText
          , (if null dims then "bound " else "bound box ") <> boundText
          ]
      _ -> Left "covariance: a number or a vector"
  ["add"] -> add session
  ["update"] -> update True session
  ["update", "--no-upgrade"] -> update False session
  ["upgrade", n] -> upgrade n session
  ["todo"] -> keep (todo session)
  ["scratch"] -> keep (Right (map pending session.scratch))
  ["forget", n] -> forget n session
  ("type" : rest) -> keep $ do
    e <- parseExpr (T.unwords rest)
    (_, _, ty) <- checkExpr cb (T.unwords rest) e
    pure [ty]
  ["edit", n] -> keep $ withName n $ \r ->
    let keyword
          | isUnitName n cb = "unit "
          | isScaleName n cb = "scale "
          | otherwise = "let "
     in (\body -> [keyword <> n <> " = " <> body]) <$> viewReference cb r
  ["lint", n] -> keep $ withName n $ \r -> case lookupTyped r.hash cb of
    Nothing -> Left ("no typed core for " <> showHash r.hash)
    Just t -> case lintClosed (typeLookupFor cb) t of
      Left err -> Left ("lint failed: " <> err)
      Right schemes -> pure (map renderScheme schemes)
  ["core", n] -> keep $ withName n $ \r -> (: []) . ((n <> " = ") <>) <$> viewTyped cb r
  ["hash", n] -> keep $ withName n $ \r -> pure [showReference r]
  ["names", h] -> keep $ case findByPrefix h cb of
    [] -> Left ("no definition with hash " <> h)
    hs ->
      pure
        [ showHash h'
            <> " "
            <> T.unwords (historicalNamesOf (Reference h' Nothing) cb ++ cycleNames h')
        | h' <- hs
        ]
  ["history", n] -> keep $ case historyOf n cb of
    [] -> Left ("unknown name `" <> n <> "`")
    r : rs -> pure ((showReference r <> "  (current)") : map showReference rs)
  ["view", n] -> keep $ withName n $ \r -> (: []) . ((n <> " = ") <>) <$> viewReference cb r
  ["dependents", n] -> keep $ withName n $ \r -> pure (dependents r.hash cb)
  -- An alias of a unit or scale is one too.
  ["alias", new, old] -> withName' old $ \r ->
    let flagged =
          (if isUnitName old cb then markUnit new else id)
            . (if isScaleName old cb then markScale new else id)
     in commit
          (flagged (bindName new r cb))
          ["`" <> new <> "` now also names " <> showReference r]
  ["unname", n] -> withName' n $ \_ -> commit (unbindName n cb) ["removed the label `" <> n <> "`"]
  _ ->
    Left
      ( "commands: :add  :update [--no-upgrade]  :upgrade name  :todo  :scratch  :forget name  :edit name  :type expr\n"
          <> "          :view name  :core name  :hash name  :names #hash  :history name  :dependents name  :alias new old  :unname name\n"
          <> "          :exact expr  :budget expr  :covariance expr  :set [precision n | sigma k]  :prefer [unit]  :unprefer unit"
      )
 where
  cb = session.staging
  cfg = session.config
  keep = fmap (session,)
  tshow = T.pack . show
  setting n adjust err = case reads (T.unpack n) of
    [(k, "")] | k >= (0 :: Int) -> Right (session{config = adjust k}, [])
    _ -> Left err
  evalOf rest = do
    e <- parseExpr (T.unwords rest)
    evalValue cfg cb (T.unwords rest) e
  -- Nudges declared in the expression itself are labelled "input".
  inputNamer h h' i written = if h' == h then "input" else refNamer cb h' i written
  preferenceOf = preferenceHint cfg cb
  commit cb' outs = Right (session{codebase = cb', staging = cb'}, outs)
  withName n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n cb)
  withName' n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n session.codebase)
  cycleNames h' = case lookupTerm h' cb of
    Just (Cycle hints _) ->
      [ T.intercalate "," (historicalNamesOf (Reference h' (Just i)) cb)
      | i <- [0 .. vecLength hints - 1]
      ]
    _ -> []
  pending b = "pending: " <> b.name.text
  _ = src

{- | Store scratch definitions whose names are new (or unchanged). A name
that exists with a different definition is a conflict.
-}
add :: Session -> Either Text (Session, [Text])
add session
  | null session.scratch = Right (session, ["nothing to add"])
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
        , ["added " <> n | n <- names]
        )
 where
  names = map (.name.text) session.scratch
  conflicts =
    [ n
    | n <- names
    , Just old <- [lookupName n session.codebase]
    , lookupName n session.staging /= Just old
    ]

{- | Store scratch definitions, re-binding names that already exist, then
propagate the new versions to every dependent that still typechecks
(unless told not to).
-}
update :: Bool -> Session -> Either Text (Session, [Text])
update doUpgrade session
  | null session.scratch = Right (session, ["nothing to update"])
  | otherwise =
      let names = map (.name.text) session.scratch
          changed =
            [ (n, old, new)
            | n <- names
            , Just old <- [lookupName n session.codebase]
            , Just new <- [lookupName n session.staging]
            , old /= new
            ]
          added = [n | n <- names, Nothing <- [lookupName n session.codebase]]
          refmap = Map.fromList [(old, new) | (_, old, new) <- changed]
          result =
            if doUpgrade
              then propagate refmap session.staging
              else Propagation session.staging [] []
          report =
            ["added " <> n | n <- added]
              ++ [ "updated " <> n <> " " <> showReference old <> " -> " <> showReference new
                 | (n, old, new) <- changed
                 ]
              ++ upgradeReport result
              ++ [ "dependents left on old versions: "
                     <> T.unwords [n | (n, _, _) <- staleReferences result.codebase]
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

upgradeReport :: Propagation -> [Text]
upgradeReport result =
  [ "upgraded " <> n <> " " <> showReference old <> " -> " <> showReference new
  | (n, old, new) <- result.upgraded
  ]
    ++ [ "left " <> n <> " on " <> showReference r <> ": " <> why
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
        result = propagate (Map.fromList [(r, current) | r <- stale]) session.codebase
        cb' = result.codebase
        staging' = either (const cb') id (processGroup cb' session.scratch)
     in Right
          ( session{codebase = cb', staging = staging'}
          , if null result.upgraded && null result.skipped
              then ["nothing to upgrade"]
              else upgradeReport result
          )

todo :: Session -> Either Text [Text]
todo session =
  Right
    $ ["pending: " <> b.name.text <> " (use :add or :update)" | b <- session.scratch]
      ++ [ "stale: "
             <> n
             <> " uses "
             <> m
             <> showReference r
             <> " (use :upgrade "
             <> m
             <> ")"
         | (n, r, m) <- staleReferences session.codebase
         ]
      ++ [ "nothing to do" | null session.scratch, null (staleReferences session.codebase)
         ]

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
                    , sources = Map.delete n session.sources
                    , staging = staging'
                    }
                , ["forgot `" <> n <> "`"]
                )

{- | Print the definition behind a reference (design §7.2). Cycle members
are shown one at a time, with the other members by name.
-}
viewReference :: Codebase -> Reference -> Either Text Text
viewReference cb (Reference h idx) = case lookupTerm h cb of
  Nothing -> Left ("missing term " <> showHash h)
  Just t -> case (idx, t) of
    (Nothing, _) -> Right (renderTerm (refNamer cb) VNil t)
    (Just i, Cycle hints bodies) ->
      let memberName j (Hint hint) = fromMaybe hint (listToMaybe (namesOf (Reference h (Just j)) cb))
          ctx = vecAppend (vecMapIndexed memberName hints) VNil
       in case vecIndex i bodies of
            Just body -> Right (renderTerm (refNamer cb) ctx body)
            Nothing -> Left ("no member " <> T.pack (show i) <> " in " <> showHash h)
    (Just _, _) -> Left (showHash h <> " is not a cycle")

-- | Print the Typed Core behind a reference (design §5.3), for inspection.
viewTyped :: Codebase -> Reference -> Either Text Text
viewTyped cb (Reference h idx) = case lookupTyped h cb of
  Nothing -> Left ("no typed core for " <> showHash h)
  Just t -> case (idx, t) of
    (Nothing, _) -> Right (renderTTerm (refNamer cb) VNil t)
    (Just i, TCycle _ members bodies) ->
      let memberName j (Hint hint, _) = fromMaybe hint (listToMaybe (namesOf (Reference h (Just j)) cb))
          ctx = vecAppend (vecMapIndexed memberName members) VNil
       in case vecIndex i bodies of
            Just body -> Right (renderTTerm (refNamer cb) ctx body)
            Nothing -> Left ("no member " <> T.pack (show i) <> " in " <> showHash h)
    (Just _, _) -> Left (showHash h <> " is not a cycle")

vecMapIndexed :: forall a b k. (Int -> a -> b) -> Vec k a -> Vec k b
vecMapIndexed f = go 0
 where
  go :: forall m. Int -> Vec m a -> Vec m b
  go _ VNil = VNil
  go i (VCons x xs) = VCons (f i x) (go (i + 1) xs)

-- | A current name, else a stale @name#hash@, else a bare @#hash@.
refNamer :: Codebase -> RefNamer
refNamer cb h idx written =
  let r = Reference h idx
   in case namesOf r cb of
        -- The name the author wrote, while it still points here; else any current name.
        ns | written `elem` ns -> written
        n : _ -> n
        [] -> case historicalNamesOf r cb of
          n : _ -> n <> showReference r
          [] -> showReference r

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
  (_, v) <- evalValue cfg cb text e
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
