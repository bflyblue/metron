-- | Resolve names through scopes and namespaces, independently of binding-group compilation.
module Metron.NameResolution (
  LabelKind (..),
  Qualified (..),
  isLabel,
  qualifyWith,
  qualifyName,
  shortestName,
  shortestNameOf,
  namespaceLabels,
  isNamespace,
  disjointness,
  resolverFor,
  groupResolver,
) where

import Control.Monad (when)
import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict qualified as Map (
  findWithDefault,
  fromListWith,
  keys,
  lookupGE,
  member,
 )
import Data.Maybe (isJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set (
  empty,
  fromList,
  member,
  toList,
 )
import Data.Text (Text)
import Data.Text qualified as T (
  all,
  any,
  breakOn,
  drop,
  intercalate,
  isPrefixOf,
  null,
  pack,
  splitOn,
  stripPrefix,
  unpack,
 )
import Metron.Builtin (isSpaceDef)
import Metron.Codebase (
  Codebase (conNames, fieldNames, history, names, typeNames, uses),
  Reference (..),
  fieldNamesOf,
  findByPrefix,
  historyOf,
  isChartName,
  isUnitName,
  lookupConName,
  lookupFieldName,
  lookupName,
  lookupTerm,
  lookupTypeDef,
  lookupTypeName,
  typeOf,
 )
import Metron.Core (
  ConRef (UserCon),
  Hash,
  Term (Cycle, Lam),
  showFullHash,
  vecIndex,
 )
import Metron.Desugar (
  ConInfo (ConInfo),
  FieldInfo (FieldInfo),
  Resolution (Resolution),
  Resolved (..),
  Resolver,
 )
import Metron.Desugar qualified as D (spaceQuery)
import Metron.Syntax qualified as S (
  Scope (namespace, uses),
  Span,
  Use (alias, path),
  lastSegment,
  qualify,
 )
import Metron.Type (
  Scheme (Forall),
  Type (TChart, TFun, TUnit),
  TypeDef (constructors),
 )
import Text.Read (readMaybe)

-- Names and namespaces (design §7.6) ----------------------------------------------

{- | The kinds of label, each its own set of names: definitions and
constructors share one, as they share expressions.
-}
data LabelKind = TermLabel | TypeLabel | FieldLabel
  deriving stock (Eq, Ord, Show)

-- | Whether a full path is a label of a kind.
isLabel :: LabelKind -> Codebase -> Text -> Bool
isLabel kind cb n = case kind of
  TermLabel -> Map.member n cb.names || Map.member n cb.conNames
  TypeLabel -> Map.member n cb.typeNames
  FieldLabel -> Map.member n cb.fieldNames

-- | What a written name stands for.
data Qualified
  = -- | this full path
    Found Text
  | -- | two @use@d namespaces offer it, as these full paths
    Ambiguous [Text]
  | NotFound
  deriving stock (Eq, Show)

{- | The full path a written name stands for, given which full paths exist
(design §7.6). A leading dot writes an absolute path. Otherwise, in order:
the current namespace (@x@ is @current.x@), then the @use@d namespaces
(@u.x@ for each @use u@, and @u.y@ for @k.y@ under @use u as k@), which
must not offer it twice, then the root (@x@ itself), and last the
codebase's stored default @use@s (design §7.7), which must not offer it
twice either. So a root name shadows the library's @physics.c@ that @use physics@
offers, while a @use@ of the session still beats a root name. A local
binder comes before all of these, in the desugarer. A full path written
out resolves as itself at the root step, unless something nearer takes it
first.
-}
qualifyWith :: [S.Use] -> (Text -> Bool) -> S.Scope -> Text -> Qualified
qualifyWith stored exists scope written
  | Just p <- T.stripPrefix "." written = if exists p then Found p else NotFound
  | here : _ <-
      [ n
      | not (null scope.namespace)
      , let n = S.qualify scope.namespace written
      , exists n
      ] =
      Found here
  | otherwise = case offered scope.uses of
      [one] -> Found one
      many@(_ : _ : _) -> Ambiguous many
      []
        | exists written -> Found written
        | otherwise -> case offered stored of
            [one] -> Found one
            many@(_ : _ : _) -> Ambiguous many
            [] -> NotFound
 where
  offered = nubOrd . filter exists . mapMaybe through
  through u = case u.alias of
    Nothing -> Just (u.path <> "." <> written)
    Just k -> (\rest -> u.path <> "." <> rest) <$> T.stripPrefix (k <> ".") written

-- | 'qualifyWith' over the labels of one kind in a codebase.
qualifyName :: LabelKind -> S.Scope -> Codebase -> Text -> Qualified
qualifyName kind scope cb = qualifyWith cb.uses (isLabel kind cb) scope

-- | What a full path labels among definitions and constructors.
resolvedAt :: Codebase -> Text -> Maybe Resolved
resolvedAt cb n = case lookupName n cb of
  Just (Reference h i) ->
    Just
      ( ATerm
          ( Resolution
              (h, i)
              (isUnitName n cb)
              (isChartName n cb)
              (isChartName n cb && moving cb h i)
          )
      )
  Nothing -> case lookupConName n cb of
    Just (h, i)
      | Just def <- lookupTypeDef h cb ->
          let arity = length (def.constructors !! i)
           in Just
                ( AConstructor
                    ( ConInfo
                        (UserCon h i)
                        arity
                        [(UserCon h j, length fs) | (j, fs) <- zip [0 ..] def.constructors]
                        (fieldNamesOf h i arity cb)
                    )
                )
    _ -> Nothing

{- | Whether a definition is a function: what a chart declared with
parameters is, a moving chart (design §3.8). Read off the stored Core, so
that a store reload keeps it with no flag of its own.
-}
moving :: Codebase -> Hash -> Maybe Int -> Bool
moving cb h i = case (lookupTerm h cb, i) of
  (Just (Lam _ _), Nothing) -> True
  (Just (Cycle _ bodies), Just j) -> case vecIndex j bodies of
    Just (Lam _ _) -> True
    _ -> False
  _ -> False

-- | The record field a full path labels.
fieldAt :: Codebase -> Text -> Maybe Resolved
fieldAt cb f = case lookupFieldName f cb of
  Just (h, i, j)
    | Just def <- lookupTypeDef h cb
    , let arity = length (def.constructors !! i) ->
        Just (AField (FieldInfo (UserCon h i) arity j (fieldNamesOf h i arity cb)))
  _ -> Nothing

{- | Free names resolve through the scope to whatever the codebase currently
binds (design §7.6). The resolver answers the three kinds of query of
'Resolver': a name, @.f@ for a field and @§p@ for an absolute path.
-}
resolverFor :: S.Scope -> Codebase -> Resolver
resolverFor = groupResolver Set.empty Set.empty

{- | A resolver inside a binding group: the group's names exist before they
are entered, and the members of the cycle being desugared are local
binders.
-}
groupResolver :: Set Text -> Set Text -> S.Scope -> Codebase -> Resolver
groupResolver group members scope cb query
  | T.any (== '#') query = historicalReference scope cb query
  -- A chart's parent may be a space, a type (design §3.10, F2).
  | Just x <- T.stripPrefix D.spaceQuery query = case qualifyName TypeLabel scope cb x of
      Found full
        | Just h <- lookupTypeName full cb
        , Just def <- lookupTypeDef h cb
        , isSpaceDef def ->
            Just (ASpaceDecl h)
      _ -> Nothing
  -- A field is looked up under its dot, the one way it is written (design §2.3).
  | Just f <- T.stripPrefix "." query = case qualifyName FieldLabel scope cb f of
      Found full -> fieldAt cb full
      Ambiguous fulls -> Just (AAmbiguous fulls)
      NotFound -> Nothing
  | otherwise =
      let written = maybe query ("." <>) (T.stripPrefix "§" query)
          exists n = isLabel TermLabel cb n || Set.member n group
       in case qualifyWith cb.uses exists scope written of
            Found full
              | Set.member full members -> Just (ALocal full)
              | full == query -> resolvedAt cb full
              | otherwise -> AQualified full <$> resolvedAt cb full
            Ambiguous fulls -> Just (AAmbiguous fulls)
            NotFound -> Nothing

{- | Hashes select stored terms, never a local binder. A name narrows the
search to its current and historical references. Bare hashes search all
terms. Whether it is a unit or a chart comes from the selected term's type,
not from the name's current flags, which may describe a different version
entirely.
-}
historicalReference :: S.Scope -> Codebase -> Text -> Maybe Resolved
historicalReference scope cb query = Just $ either AInvalidReference id $ do
  let (written0, suffix) = T.breakOn "#" query
      written = maybe written0 ("." <>) (T.stripPrefix "§" written0)
      parts = T.splitOn "." (T.drop 1 suffix)
  (prefix, member) <- case parts of
    [p] -> Right (p, Nothing)
    [p, i] | Just j <- readMaybe (T.unpack i), j >= (0 :: Int) -> Right (p, Just j)
    _ -> Left "invalid hash reference: expected #hash or #hash.index"
  when
    ( T.null prefix
        || not (T.all (`elem` ("0123456789abcdefghijklmnopqrstuv" :: String)) prefix)
    )
    (Left "invalid hash prefix: use lowercase base32hex digits 0-9 and a-v")
  let hashes = findByPrefix prefix cb
  (full, candidates) <-
    if T.null written
      then Right ("", [Reference h member | h <- hashes])
      else case qualifyWith
        cb.uses
        (\n -> isLabel TermLabel cb n || Map.member n cb.history)
        scope
        written of
        Found n ->
          Right
            ( n
            , nubOrd
                [ r
                | r <- maybe [] pure (lookupName n cb) ++ historyOf n cb
                , r.hash `elem` hashes
                , maybe True (\i -> r.index == Just i) member
                ]
            )
        Ambiguous ns -> Left ("ambiguous historical name: " <> T.intercalate ", " ns)
        NotFound -> Left ("unknown historical name `" <> written <> "`")
  r <- case candidates of
    [] -> Left ("no stored version matches `" <> query <> "`")
    [r] -> Right r
    _ ->
      Left
        ( "ambiguous hash reference `"
            <> query
            <> "`: use a longer prefix or a member index; matches: "
            <> T.intercalate
              ", "
              [ showFullHash ref.hash <> maybe "" (\i -> "." <> T.pack (show i)) ref.index
              | ref <- candidates
              ]
        )
  case (lookupTerm r.hash cb, r.index) of
    (Just (Cycle _ bodies), Just i) | isJust (vecIndex i bodies) -> pure ()
    (Just (Cycle _ _), _) -> Left "a recursive group reference needs a valid .index member"
    (Just _, Nothing) -> pure ()
    (Just _, Just _) -> Left "a member index is only valid for a recursive group"
    _ -> Left "hash reference is not a stored term"
  Forall _ ty <-
    maybe (Left "hash reference has no stored type") Right (typeOf r cb)
  let unit = case ty of TUnit _ -> True; _ -> False
      chart = returnsChart ty
      parameterised = case ty of TFun _ _ -> chart; _ -> False
  pure
    (AQualified full (ATerm (Resolution (r.hash, r.index) unit chart parameterised)))
 where
  returnsChart = \case
    TChart _ -> True
    TFun _ result -> returnsChart result
    _ -> False

{- | How a full path prints in a scope (design §7.6), as Unison prints names:
the shortest spelling that resolves back to the same label. Tried in order:
the last segment alone; the path relative to the current namespace; the
path relative to each @use@ (under its alias, if it has one), the
session's and then the codebase's stored ones (design §7.7); the full
path; and, only when the full path itself would resolve to something else
here, the absolute @.full.path@. At the root with no @use@, every root
name prints as itself, and so does every library name the stored @use@s
reach and no root name shadows.
-}
shortestName :: S.Scope -> Codebase -> Text -> Text
shortestName = shortestNameOf TermLabel

-- | 'shortestName' for a kind of label.
shortestNameOf :: LabelKind -> S.Scope -> Codebase -> Text -> Text
shortestNameOf kind scope cb n =
  case [c | c <- candidates, qualifyName kind scope cb c == Found n] of
    c : _ -> c
    -- Nothing spells it here (a name that is no longer a label): in full.
    [] -> n
 where
  candidates =
    [S.lastSegment n]
      ++ [ rel
         | not (null scope.namespace)
         , Just rel <- [T.stripPrefix (S.qualify scope.namespace "") n]
         ]
      ++ [ maybe rel (\k -> k <> "." <> rel) u.alias
         | u <- scope.uses ++ cb.uses
         , Just rel <- [T.stripPrefix (u.path <> ".") n]
         ]
      ++ [n, "." <> n]

-- | Every label of every kind, with what kind of thing it names.
allLabels :: Codebase -> [(Text, Text)]
allLabels cb =
  [(n, "definition") | n <- Map.keys cb.names]
    ++ [(n, "type") | n <- Map.keys cb.typeNames]
    ++ [(n, "constructor") | n <- Map.keys cb.conNames]
    ++ [(n, "field") | n <- Map.keys cb.fieldNames]

-- | The labels of every kind under a namespace, by full path, without duplicates.
namespaceLabels :: Codebase -> Text -> [Text]
namespaceLabels cb ns =
  Set.toList
    (Set.fromList [n | (n, _) <- allLabels cb, (ns <> ".") `T.isPrefixOf` n])

-- | Whether a path is a namespace: some label lies under it.
isNamespace :: Codebase -> Text -> Bool
isNamespace cb ns =
  any
    under
    [ Map.keys cb.names
    , Map.keys cb.typeNames
    , Map.keys cb.conNames
    , Map.keys cb.fieldNames
    ]
 where
  under = any ((ns <> ".") `T.isPrefixOf`)

{- | The rule that keeps the dot unambiguous (design §7.6): a name is never
both a label and a namespace. Given the labels a change adds (full path,
what it names, where it was written), the first that breaks the rule
against the codebase or the others, as a message at its span.
-}
disjointness :: Codebase -> [(Text, Text, S.Span)] -> Maybe (S.Span, Text)
disjointness cb new =
  case [(sp, msg) | (n, what, sp) <- new, Just msg <- [clash n what]] of
    x : _ -> Just x
    [] -> Nothing
 where
  labels =
    Map.fromListWith
      (\_ old -> old)
      (allLabels cb ++ [(n, what) | (n, what, _) <- new])
  clash n what
    | Just (k, _) <- Map.lookupGE (n <> ".") labels
    , (n <> ".") `T.isPrefixOf` k =
        Just ("`" <> n <> "` is a namespace; a " <> what <> " cannot have its name")
    | p : _ <- [p | p <- properPrefixes n, Map.member p labels] =
        Just
          ( "`"
              <> p
              <> "` is a "
              <> Map.findWithDefault "name" p labels
              <> "; it cannot also be a namespace, as `"
              <> n
              <> "` would make it"
          )
    | otherwise = Nothing
  properPrefixes n =
    let segs = T.splitOn "." n
     in [T.intercalate "." (take k segs) | k <- [1 .. length segs - 1]]
