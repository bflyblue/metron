-- | Runs source text through the whole pipeline for the CLI and the tests
-- (design §7.3, §7.5).
--
-- Definitions typed at the prompt or read from a file go into the
-- **scratch**: they are desugared, typechecked, hashed and usable by
-- expressions, but not stored. @:add@ and @:update@ move them into the
-- codebase; @:update@ also propagates the new versions to the dependents
-- that still typecheck.
module Eval.Driver
  ( Session (..)
  , emptySession
  , preludeSession
  , feed
  ) where

import Data.List (partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Eval
import Eval.Hash (showHash)
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
  , scratch :: [S.Binding] -- ^ pending definitions, oldest first
  , sources :: Map Text Text -- ^ the input text each pending definition came from, for error excerpts
  , staging :: Codebase -- ^ codebase with the scratch entered on top; what expressions see
  }

emptySession :: Session
emptySession = Session emptyCodebase [] Map.empty emptyCodebase

-- | A session with the prelude (design §3.2.11) entered and added, as every
-- interactive session starts. Fails only if the prelude itself does not
-- check, which is a build error.
preludeSession :: Either Text Session
preludeSession = do
  (s, _) <- feed defaultConfig emptySession preludeSource
  (s', _) <- feed defaultConfig s ":add"
  pure s'

-- | Parse and run one input (a line, a file). Returns the new session and
-- the lines to print, or the first error.
feed :: Config -> Session -> Text -> Either Text (Session, [Text])
feed cfg session src
  | Just cmd <- T.stripPrefix ":" (T.stripStart src) = command cfg session src (T.words cmd)
  | otherwise = do
      stmts <- parseProgram src
      let lets = [b | S.SLet b <- stmts]
          exprs = [e | S.SExpr e <- stmts]
      (session', notes) <- if null lets then Right (session, []) else propose session src lets
      outs <- mapM (evalExpr cfg session'.staging src) exprs
      pure (session', notes ++ outs)

-- | Put definitions into the scratch. A name already pending is replaced
-- (the scratch is a workspace, not a scope); a name defined twice in one
-- input is an error. The whole scratch is re-entered on top of the codebase
-- so that errors surface now.
propose :: Session -> Text -> [S.Binding] -> Either Text (Session, [Text])
propose session src lets = do
  let incoming = map (.name.text) lets
      (replaced, kept) = partition (\b -> b.name.text `elem` incoming) session.scratch
      scratch' = kept ++ lets
      sources' = foldr (\b -> Map.insert b.name.text src) session.sources lets
  staging' <- either (Left . renderResolveErrorWith sources' src) Right (processGroup session.codebase scratch')
  let notes = ["replaced pending definition of `" <> b.name.text <> "`" | b <- replaced]
  pure (session {scratch = scratch', sources = sources', staging = staging'}, notes)

-- | Type errors point into the input that defined the offending name.
renderResolveErrorWith :: Map Text Text -> Text -> ResolveError -> Text
renderResolveErrorWith sources src = \case
  TypeErrorIn n sp msg ->
    S.renderSpanError (Just (Map.findWithDefault src n.text sources)) (fromMaybe n.span sp) ("in `" <> n.text <> "`: " <> msg)
  DuplicateDefinition n ->
    S.renderSpanError (Just src) n.span ("`" <> n.text <> "` is defined twice in the same group")
  Desugar (UnknownName sp n) -> S.renderSpanError (Just src) sp ("unknown name `" <> n <> "`")
  err@(LintFailure _ _) -> renderResolveError err

-- | Desugar, typecheck and elaborate, lint, evaluate, print.
evalExpr :: Config -> Codebase -> Text -> S.Expr -> Either Text Text
evalExpr cfg cb src e = do
  (typed, _) <- checkExpr cb src e
  v <- either (Left . renderEvalError) Right (evalClosed cfg (`lookupTyped` cb) typed)
  either (Left . renderEvalError) Right (renderValue cfg.scale v)

-- | Desugar, typecheck, elaborate and lint an expression against a codebase.
-- Returns the Typed Core and the printed type.
checkExpr :: Codebase -> Text -> S.Expr -> Either Text (TTerm Z, Text)
checkExpr cb src e = do
  (term, prov) <- either (Left . renderResolveErrorWith Map.empty src . Desugar) Right (desugarClosed (resolverFor cb) e)
  (schemes, typed) <- either (Left . typeErr prov) Right (I.elaborateClosed (typeLookupFor cb) term)
  _ <- either (Left . ("internal error: elaboration produced ill-typed core: " <>)) Right (lintClosed (typeLookupFor cb) typed)
  pure (typed, maybe "" renderScheme (listToMaybe schemes))
  where
    typeErr prov err = S.renderSpanError (Just src) (fromMaybe e.span (Map.lookup err.path prov)) err.message

-- Commands ----------------------------------------------------------------------

command :: Config -> Session -> Text -> [Text] -> Either Text (Session, [Text])
command _cfg session src = \case
  ["add"] -> add session
  ["update"] -> update True session
  ["update", "--no-upgrade"] -> update False session
  ["upgrade", n] -> upgrade n session
  ["todo"] -> keep (todo session)
  ["scratch"] -> keep (Right (map pending session.scratch))
  ["forget", n] -> forget n session
  ("type" : rest) -> keep $ do
    e <- parseExpr (T.unwords rest)
    (_, ty) <- checkExpr cb (T.unwords rest) e
    pure [ty]
  ["edit", n] -> keep $ withName n $ \r -> (\body -> ["let " <> n <> " = " <> body]) <$> viewReference cb r
  ["lint", n] -> keep $ withName n $ \r -> case lookupTyped r.hash cb of
    Nothing -> Left ("no typed core for " <> showHash r.hash)
    Just t -> case lintClosed (typeLookupFor cb) t of
      Left err -> Left ("lint failed: " <> err)
      Right schemes -> pure (map renderScheme schemes)
  ["core", n] -> keep $ withName n $ \r -> (: []) . ((n <> " = ") <>) <$> viewTyped cb r
  ["hash", n] -> keep $ withName n $ \r -> pure [showReference r]
  ["names", h] -> keep $ case findByPrefix h cb of
    [] -> Left ("no definition with hash " <> h)
    hs -> pure [showHash h' <> " " <> T.unwords (historicalNamesOf (Reference h' Nothing) cb ++ cycleNames h') | h' <- hs]
  ["history", n] -> keep $ case historyOf n cb of
    [] -> Left ("unknown name `" <> n <> "`")
    r : rs -> pure ((showReference r <> "  (current)") : map showReference rs)
  ["view", n] -> keep $ withName n $ \r -> (: []) . ((n <> " = ") <>) <$> viewReference cb r
  ["dependents", n] -> keep $ withName n $ \r -> pure (dependents r.hash cb)
  ["alias", new, old] -> withName' old $ \r -> commit (bindName new r cb) ["`" <> new <> "` now also names " <> showReference r]
  ["unname", n] -> withName' n $ \_ -> commit (unbindName n cb) ["removed the label `" <> n <> "`"]
  _ ->
    Left
      ( "commands: :add  :update [--no-upgrade]  :upgrade name  :todo  :scratch  :forget name  :edit name  :type expr\n"
          <> "          :view name  :core name  :hash name  :names #hash  :history name  :dependents name  :alias new old  :unname name"
      )
  where
    cb = session.staging
    keep = fmap (session,)
    commit cb' outs = Right (session {codebase = cb', staging = cb'}, outs)
    withName n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n cb)
    withName' n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n session.codebase)
    cycleNames h' = case lookupTerm h' cb of
      Just (Cycle hints _) -> [T.intercalate "," (historicalNamesOf (Reference h' (Just i)) cb) | i <- [0 .. vecLength hints - 1]]
      _ -> []
    pending b = "pending: " <> b.name.text
    _ = src

-- | Store scratch definitions whose names are new (or unchanged). A name
-- that exists with a different definition is a conflict.
add :: Session -> Either Text (Session, [Text])
add session
  | null session.scratch = Right (session, ["nothing to add"])
  | not (null conflicts) =
      Left
        ( T.intercalate "\n" $
            ["`" <> n <> "` already exists with a different definition" | n <- conflicts]
              ++ ["use :update to replace " <> (if length conflicts == 1 then "it" else "them") <> " and upgrade dependents"]
        )
  | otherwise = Right (Session session.staging [] Map.empty session.staging, ["added " <> n | n <- names])
  where
    names = map (.name.text) session.scratch
    conflicts = [n | n <- names, Just old <- [lookupName n session.codebase], lookupName n session.staging /= Just old]

-- | Store scratch definitions, re-binding names that already exist, then
-- propagate the new versions to every dependent that still typechecks
-- (unless told not to).
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
              ++ ["updated " <> n <> " " <> showReference old <> " -> " <> showReference new | (n, old, new) <- changed]
              ++ upgradeReport result
              ++ [ "dependents left on old versions: " <> T.unwords [n | (n, _, _) <- staleReferences result.codebase]
                 | not doUpgrade
                 , not (null (staleReferences result.codebase))
                 ]
       in Right (Session result.codebase [] Map.empty result.codebase, report)

upgradeReport :: Propagation -> [Text]
upgradeReport result =
  ["upgraded " <> n <> " " <> showReference old <> " -> " <> showReference new | (n, old, new) <- result.upgraded]
    ++ ["left " <> n <> " on " <> showReference r <> ": " <> why | (n, r, why) <- result.skipped]

-- | Move every current definition still using an old version of a name to
-- its current version, where it typechecks.
upgrade :: Text -> Session -> Either Text (Session, [Text])
upgrade n session = case lookupName n session.codebase of
  Nothing -> Left ("unknown name `" <> n <> "`")
  Just current ->
    let stale = [r | r <- historyOf n session.codebase, r /= current]
        result = propagate (Map.fromList [(r, current) | r <- stale]) session.codebase
        cb' = result.codebase
        staging' = either (const cb') id (processGroup cb' session.scratch)
     in Right
          ( Session cb' session.scratch session.sources staging'
          , if null result.upgraded && null result.skipped then ["nothing to upgrade"] else upgradeReport result
          )

todo :: Session -> Either Text [Text]
todo session =
  Right $
    ["pending: " <> b.name.text <> " (use :add or :update)" | b <- session.scratch]
      ++ ["stale: " <> n <> " uses " <> m <> showReference r <> " (use :upgrade " <> m <> ")" | (n, r, m) <- staleReferences session.codebase]
      ++ ["nothing to do" | null session.scratch, null (staleReferences session.codebase)]

forget :: Text -> Session -> Either Text (Session, [Text])
forget n session
  | n `notElem` map (.name.text) session.scratch = Left ("`" <> n <> "` is not pending")
  | otherwise =
      let scratch' = filter (\b -> b.name.text /= n) session.scratch
       in case processGroup session.codebase scratch' of
            Left err -> Left (renderResolveError err)
            Right staging' -> Right (session {scratch = scratch', sources = Map.delete n session.sources, staging = staging'}, ["forgot `" <> n <> "`"])

-- | Print the definition behind a reference (design §7.2). Cycle members
-- are shown one at a time, with the other members by name.
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
refNamer cb h idx =
  let r = Reference h idx
   in case namesOf r cb of
        n : _ -> n
        [] -> case historicalNamesOf r cb of
          n : _ -> n <> showReference r
          [] -> showReference r

renderEvalError :: EvalError -> Text
renderEvalError = \case
  DivideByZero -> "error: division by zero"
  Internal msg -> "internal error: " <> msg
  UnknownRef h -> "error: unknown reference " <> showHash h
  BadCycleIndex i -> "error: bad cycle index " <> T.pack (show i)
  Unsupported msg -> "not implemented: " <> msg
