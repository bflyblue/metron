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
  preludeSession,
  feed,
  refreshPreferences,
) where

import Control.Monad (foldM)
import Data.Char (isDigit)
import Data.List (partition, sortOn)
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
  statCoefficients,
 )
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Dimension (Dim, Spelling (..), dimPow, dimVar, renderDimIn)
import Eval.Eval
import Eval.Hash (hashTerm)
import Eval.Infer qualified as I
import Eval.Lexer (prepare)
import Eval.Parser (parseExpr, parseProgram, parseType)
import Eval.Prelude (preludeNames, preludeSource)
import Eval.Pretty
import Eval.Resolve
import Eval.Syntax qualified as S
import Eval.TCore
import Eval.Type (
  Arg (..),
  Kind (..),
  Len (..),
  Scheme (..),
  Shape (..),
  Type (..),
  TypeDef (..),
  dataConstructors,
  renderScheme,
  renderSchemeIn,
  renderTypeDef,
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
  Session emptyCodebase [] Map.empty emptyCodebase defaultConfig Map.empty Nothing

{- | A session with the prelude (design §3.2.11) entered and added, as every
interactive session starts. Fails only if the prelude itself does not
check, which is a build error.
-}
preludeSession :: Either Text Session
preludeSession = do
  (s, _) <- feed emptySession preludeSource
  (s', _) <- feed s ":add"
  pure s'{lastExpr = Nothing}

{- | Parse and run one input (a line, a file). Returns the new session and
the lines to print, or the first error.
-}
feed :: Session -> Text -> Either Text (Session, [Text])
feed session src = case feed' session src of
  -- Declared types print by hash below here; the session names them (design §7.2).
  Left err -> Left (nameTypes session.staging err)
  Right (session', outs) -> Right (session', echo ++ map (nameTypes session'.staging) outs)
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
      let decls = mapMaybe S.declOf stmts
          exprs = [e | S.SExpr e <- stmts]
      (session', notes) <-
        if null decls then Right (session, []) else propose session src decls
      -- Each expression that evaluates becomes `it` for the next one.
      let step (s, outs) e = do
            (out, le) <- evalExpr s.config s.preferred (exprCodebase s) src e
            pure (s{lastExpr = Just le}, out : outs)
      (session'', outs) <- foldM step (session', []) exprs
      pure (session'', notes ++ reverse outs)

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
  let incoming = map (.name.text) decls
      (replaced, kept) = partition (\b -> b.name.text `elem` incoming) session.scratch
      scratch' = kept ++ decls
      sources' = foldr (\b -> Map.insert b.name.text src) session.sources decls
  -- `it` is session-local (design §7.5): it is neither defined nor stored.
  case [b.name | S.DBind b <- decls, b.name.text == "it"] of
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
  let notes = ["replaced pending definition of `" <> b.name.text <> "`" | b <- replaced]
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
  err@(LintFailure _ _) -> renderResolveError err

-- | Desugar, typecheck and elaborate, lint, evaluate, print.
evalExpr ::
  Config ->
  Preferences ->
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Text, LastExpr)
evalExpr cfg prefs cb src e = do
  (_, v, le) <- evalChecked cfg cb src e
  out <-
    either
      (Left . renderEvalError)
      Right
      (renderValue (printerFor cfg cb) cfg.precision prefs v)
  pure (out, le)

{- | Evaluate an expression. An expression typed at the prompt belongs to no
definition; its own hash stands in as the site of any @±@ in it (design
§3.2.4), so re-evaluating the same text gives the same nudges.
-}
evalValue :: Config -> Codebase -> Text -> S.Expr -> Either Text (Hash, Value)
evalValue cfg cb src e = (\(h, v, _) -> (h, v)) <$> evalChecked cfg cb src e

-- | 'evalValue', keeping what was checked, to become @it@.
evalChecked ::
  Config -> Codebase -> Text -> S.Expr -> Either Text (Hash, Value, LastExpr)
evalChecked cfg cb src e = do
  (term, typed, _, linted) <- checkExpr cb src e
  let h = hashTerm term
  v <- either (Left . renderEvalError) Right (evalAt cfg (runtimeOf cb) h typed)
  pure (h, v, LastExpr term linted typed cb)

runtimeOf :: Codebase -> Runtime
runtimeOf cb =
  Runtime
    { typedOf = (`lookupTyped` cb)
    , unitName = \h i written -> unitNameFor (Reference h i) written cb
    , scaleName = \h i written -> scaleNameFor (Reference h i) written cb
    }

{- | Desugar, typecheck, elaborate and lint an expression against a codebase.
Returns the Core, the Typed Core, the inferred type and the types lint
found, which are what a stored term carries.
-}
checkExpr ::
  Codebase ->
  Text ->
  S.Expr ->
  Either Text (Term Z, TTerm Z, Maybe Scheme, [Scheme])
checkExpr cb src e = do
  (term, prov) <-
    either
      (Left . renderResolveErrorWith Map.empty src . Desugar)
      Right
      (desugarClosed (resolverFor cb) e)
  (schemes, typed) <-
    either (Left . typeErr prov) Right (I.elaborateClosed (typeLookupFor cb) term)
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
                (inputPrinter h)
                cfg.precision
                session.preferred
                (if null dims then scalarVar else covValue)
            )
        boundText <-
          either
            (Left . renderEvalError)
            Right
            ( renderValueWith
                (inputPrinter h)
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
    (_, _, ty, _) <- checkExpr ecb (T.unwords rest) e
    pure [maybe "" (renderSchemeIn spelling) ty]
  ["edit", n] -> keep $ case lookupName n cb of
    Just r ->
      let keyword
            | isUnitName n cb = "unit "
            | isScaleName n cb = "scale "
            | otherwise = "let "
       in (\body -> [keyword <> n <> " = " <> body]) <$> viewReference spelling cb r
    Nothing -> viewData n
  ["lint", n] -> keep $ withExprName n $ \r -> case lookupTyped r.hash ecb of
    Nothing -> Left ("no typed core for " <> showHash r.hash)
    Just t -> case lintClosed (typeLookupFor ecb) t of
      Left err -> Left ("lint failed: " <> err)
      Right schemes -> pure (map renderScheme schemes)
  ["core", n] -> keep $ withExprName n $ \r -> (: []) . ((n <> " = ") <>) <$> viewTyped ecb r
  -- Browse the codebase (design §7.3): names with their types, filtered.
  ("ls" : rest) -> keep (listNames session rest)
  ["hash", n] -> keep $ withExprName n $ \r -> pure [showReference r]
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
  ["view", n] -> keep $ case lookupName n ecb of
    Just r -> (: []) . ((n <> " = ") <>) <$> viewReference spelling ecb r
    Nothing -> viewData n
  ["dependents", n] -> keep $ withName n $ \r -> pure (dependents r.hash cb)
  -- An alias of a unit or scale is one too.
  ["alias", new, old] -> withName' old $ \r ->
    let flagged =
          (if isUnitName old cb then markUnit new else id)
            . (if isScaleName old cb then markScale new else id)
     in commit
          (flagged (bindName new r cb))
          ["`" <> new <> "` now also names " <> showReference r]
  ["unname", n]
    | labelled n -> commit (unbindName n cb) ["removed the label `" <> n <> "`"]
    | otherwise -> Left ("unknown name `" <> n <> "`")
  _ ->
    Left
      ( "commands: :add  :update [--no-upgrade]  :upgrade name  :todo  :scratch  :forget name  :edit name  :type expr\n"
          <> "          :ls [glob] [--all|--units|--scales|--types] [: type]  :view name  :core name  :hash name  :names #hash\n"
          <> "          :history name  :dependents name  :alias new old  :unname name\n"
          <> "          :exact expr  :budget expr  :covariance expr  :set [precision n | sigma k | unicode on|off]  :prefer [unit]  :unprefer unit"
      )
 where
  cb = session.staging
  -- Read-only commands also see `it`; nothing built from this is kept.
  ecb = exprCodebase session
  cfg = session.config
  spelling = spellingOf cfg
  keep = fmap (session,)
  tshow = T.pack . show
  setting n adjust err = case reads (T.unpack n) of
    [(k, "")] | k >= (0 :: Int) -> Right (session{config = adjust k}, [])
    _ -> Left err
  evalOf rest = do
    e <- parseExpr (T.unwords rest)
    evalValue cfg ecb (T.unwords rest) e
  -- Nudges declared in the expression itself are labelled "input".
  inputNamer h h' i written = if h' == h then "input" else refNamer ecb h' i written
  inputPrinter h = (printerFor cfg ecb){refName = inputNamer h}
  preferenceOf = preferenceHint cfg cb
  commit cb' outs = Right (session{codebase = cb', staging = cb'}, outs)
  withName n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n cb)
  withExprName n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n ecb)
  withName' n k = maybe (Left ("unknown name `" <> n <> "`")) k (lookupName n session.codebase)
  cycleNames h' = case lookupTerm h' cb of
    Just (Cycle hints _) ->
      [ T.intercalate "," (historicalNamesOf (Reference h' (Just i)) cb)
      | i <- [0 .. vecLength hints - 1]
      ]
    _ -> []
  pending = \case
    S.DBind b -> "pending: " <> b.name.text
    S.DData d -> "pending: data " <> d.name.text
  -- A declared type as it could be written again (design §7.2).
  viewData n = case lookupTypeName n cb >>= \h -> (h,) <$> lookupTypeDef h cb of
    Just (h, def) ->
      pure
        [ renderTypeDef
            spelling
            h
            n
            [ fromMaybe (showHash h <> "." <> tshow i) (conNameOf h i cb)
            | i <- [0 .. length def.constructors - 1]
            ]
            [fieldNamesOf h i (length fs) cb | (i, fs) <- zip [0 ..] def.constructors]
            def
        ]
    Nothing -> Left ("unknown name `" <> n <> "`")
  -- A label of any kind: a definition, a type, a constructor, or a field written with its dot.
  labelled n = case T.stripPrefix "." n of
    Just f -> Map.member f session.codebase.fieldNames
    Nothing ->
      Map.member n session.codebase.names
        || Map.member n session.codebase.typeNames
        || Map.member n session.codebase.conNames
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
  | otherwise =
      let names = map (.name.text) session.scratch
          changed =
            [ (n, old, new)
            | n <- names
            , Just old <- [lookupName n session.codebase]
            , Just new <- [lookupName n session.staging]
            , old /= new
            ]
          added =
            [ n
            | S.DBind b <- session.scratch
            , let n = b.name.text
            , Nothing <- [lookupName n session.codebase]
            ]
          types =
            [ ( if Map.member n session.codebase.typeNames
                  then "updated data "
                  else "added data "
              )
                <> n
            | S.DData d <- session.scratch
            , let n = d.name.text
            , lookupTypeName n session.codebase /= lookupTypeName n session.staging
            ]
          refmap = Map.fromList [(old, new) | (_, old, new) <- changed]
          result =
            if doUpgrade
              then propagate refmap session.staging
              else Propagation session.staging [] []
          report =
            types
              ++ ["added " <> n | n <- added]
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
viewReference :: Spelling -> Codebase -> Reference -> Either Text Text
viewReference spelling cb (Reference h idx) = case lookupTerm h cb of
  Nothing -> Left ("missing term " <> showHash h)
  Just t -> case (idx, t) of
    (Nothing, _) -> Right (renderTermIn spelling (refNamer cb) VNil t)
    (Just i, Cycle hints bodies) ->
      let memberName j (Hint hint) = fromMaybe hint (listToMaybe (namesOf (Reference h (Just j)) cb))
          ctx = vecAppend (vecMapIndexed memberName hints) VNil
       in case vecIndex i bodies of
            Just body -> Right (renderTermIn spelling (refNamer cb) ctx body)
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
   in -- `it` only stands in when nothing else names the reference.
      case filter (/= "it") (namesOf r cb) ++ filter (== "it") (namesOf r cb) of
        -- The name the author wrote, while it still points here; else any current name.
        ns | written `elem` ns -> written
        n : _ -> n
        [] -> case historicalNamesOf r cb of
          n : _ -> n <> showReference r
          [] -> showReference r

{- | How values print in a session: names for references and record fields
from the codebase, in the configured spelling.
-}
printerFor :: Config -> Codebase -> Printer
printerFor cfg cb =
  Printer
    { refName = refNamer cb
    , fieldNames = \h i arity -> fieldNamesOf h i arity cb
    , spelling = spellingOf cfg
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

{- | Declared types and their constructors print by hash (@#a3f9k@,
@#a3f9k.1@) wherever a type or a value is rendered; here those become the
current names (design §7.2). A type without a name keeps its hash.
-}
nameTypes :: Codebase -> Text -> Text
nameTypes cb
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
              | Just i <- idx, Just c <- conNameOf h i cb -> before <> c <> go after'
              | Nothing <- idx, Just n <- typeNameOf h cb -> before <> n <> go after'
            _ -> before <> "#" <> go (T.drop 1 rest)
  isBase32 c = isDigit c || (c >= 'a' && c <= 'v')

{- | @:ls [glob] [--all | --units | --scales | --types] [: type]@ (design
§7.3): every name in the codebase with its type, one per line, sorted.
Without a filter the prelude is hidden; a glob (@*@ anywhere, else a
case-insensitive substring), a kind flag or a type query searches everything.
The type query is a written type whose unknown names are variables, matched
by unification both ways, so @: a -> a@ finds @Num [m] -> Num [m]@ and
@: Num -> Num@ finds @a -> a@.
-}
listNames :: Session -> [Text] -> Either Text [Text]
listNames session args = do
  let (before, after) = break (== ":") args
      flags = filter (T.isPrefixOf "--") before
      globs = filter (not . T.isPrefixOf "--") before
      typeText = T.unwords (drop 1 after)
  mapM_
    ( \f ->
        if f `elem` ["--all", "--units", "--scales", "--types"]
          then Right ()
          else
            Left ("unknown flag " <> f <> "; :ls takes --all, --units, --scales, --types")
    )
    flags
  query <-
    if null after
      then Right Nothing
      else do
        t <- parseType typeText
        either (Left . renderResolveError) (Right . Just) (queryScheme cb t)
  let filtered = not (null globs) || not (null flags) || isJust query
      hidePrelude = not filtered
      kindOk n
        | "--units" `elem` flags = isUnitName n cb
        | "--scales" `elem` flags = isScaleName n cb
        | "--types" `elem` flags = False
        | otherwise = True
      nameOk n =
        all (`matchesGlob` n) globs && (not hidePrelude || n `Set.notMember` preludeSet)
      typeOk sc = maybe True (`I.matchesQuery` sc) query
      definitions =
        [ prefix n <> n <> " : " <> renderSchemeIn (spellingOf session.config) sc
        | (n, r) <- sortOn (T.toLower . fst) (Map.toList cb.names)
        , kindOk n
        , nameOk n
        , Just sc <- [typeOf r cb]
        , typeOk sc
        ]
      types =
        [ line
        | "--units" `notElem` flags
        , "--scales" `notElem` flags
        , (n, h) <- sortOn (T.toLower . fst) (Map.toList cb.typeNames)
        , Just def <- [lookupTypeDef h cb]
        , line <-
            [ declaration h n def
            | nameOk n
            , isNothing query
            ]
              ++ [ c <> " : " <> renderSchemeIn (spellingOf session.config) sc
                 | (i, fields) <- zip [0 ..] def.constructors
                 , Just c <- [conNameOf h i cb]
                 , nameOk c
                 , let sc = constructorScheme h def i fields
                 , typeOk sc
                 ]
        ]
      hidden =
        if hidePrelude
          then length (filter (`Set.member` preludeSet) (Map.keys cb.names))
          else 0
      footer =
        [ "("
            <> tshow hidden
            <> " prelude names hidden; :ls --all or a filter shows them)"
        | hidden > 0
        ]
  pure
    ( case definitions ++ types of
        [] -> "nothing matches" : footer
        ls -> ls ++ footer
    )
 where
  cb = session.staging
  tshow = T.pack . show
  preludeSet = Set.fromList (map prepare preludeNames)
  prefix n
    | isUnitName n cb = "unit "
    | isScaleName n cb = "scale "
    | otherwise = ""
  declaration h n def =
    renderTypeDef
      (spellingOf session.config)
      h
      n
      [ fromMaybe (showHash h <> "." <> tshow i) (conNameOf h i cb)
      | i <- [0 .. length def.constructors - 1]
      ]
      [fieldNamesOf h i (length fs) cb | (i, fs) <- zip [0 ..] def.constructors]
      def
  -- A constructor's type: its fields to the type at its own parameters.
  constructorScheme h def i fields =
    let tyArgs = [paramArg v k | (v, k) <- def.params]
        self = TData h tyArgs
        instantiated = case dataConstructors (`lookupTypeDef` cb) self of
          Just table | Just fs <- lookup (UserCon h i) table -> fs
          _ -> fields
     in Forall def.params (foldr TFun self instantiated)
  paramArg v = \case
    KType -> AType (TVar v)
    KLen -> ALen (LVar v 0)
    KShape -> AShape (SVar v)
    KDim -> ADim (dimVar v)

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
