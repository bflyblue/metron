-- | Render stored definitions and dependency-ordered exports as source text.
module Metron.Source (
  editSource,
  definitionSource,
  signatureSource,
  viewData,
  viewReference,
  definitionLine,
  viewTyped,
  unitRef,
  refNamer,
  printerFor,
  spellingOf,
  nameTypes,
  signatureLine,
  upgradeReport,
  exportRequest,
  exportSource,
  exportLabels,
) where

import Data.Char ( isDigit )
import Data.Graph ( flattenSCC, stronglyConnComp )
import Data.List ( sortOn )
import Data.Maybe ( fromMaybe, isJust, listToMaybe, mapMaybe )
import Data.Text ( Text )
import Metron.Builtin ( frameDefMoving, isAxesDef )
import Metron.Codebase
    ( conNameOf,
      fieldNamesOf,
      historicalNamesOf,
      isChartName,
      isUnitName,
      lookupName,
      lookupTerm,
      lookupTypeDef,
      lookupTypeName,
      lookupTyped,
      namesOf,
      showReference,
      signatureOf,
      typeNameOf,
      unitNameFor,
      Codebase(uses, typeDefs, names, typeNames),
      Reference(..) )
import Metron.Core
    ( refs,
      refsWithIndex,
      showHash,
      vecAppend,
      vecIndex,
      vecMapIndexed,
      Hint(Hint),
      Term(Cycle),
      Vec(VNil) )
import Metron.Dimension ( Spelling(..) )
import Metron.Eval ( Config(nonlinear, unicode) )
import Metron.Prelude ( isLibraryPath )
import Metron.Pretty
    ( renderParamsUnits,
      renderTermUnits,
      Printer(..),
      RefNamer,
      UnitRef )
import Metron.NameResolution ( shortestName, shortestNameOf, LabelKind(TypeLabel) )
import Metron.Session.Names ( namespaceArg )
import Metron.Session.Types ( Session(scratch, codebase) )
import Metron.TCore ( renderTTerm, TTerm(TCycle) )
import Metron.Type ( TypeDef(constructors), renderForallIn, renderTypeDef, typeRefs )
import Metron.Update ( Propagation(skipped, upgraded) )
import Data.Map.Strict qualified as Map
    ( null,
      keys,
      keysSet,
      lookup,
      toList,
      findWithDefault,
      fromList,
      fromListWith,
      map )
import Metron.Syntax qualified as S
    ( lastSegment,
      renderUse,
      rootScope,
      Name(text),
      Scope(namespace, Scope) )
import Data.Set qualified as Set
    ( member,
      delete,
      empty,
      findMin,
      fromList,
      insert,
      isSubsetOf,
      null,
      size,
      toList )
import Data.Text qualified as T
    ( any,
      breakOn,
      drop,
      intercalate,
      isPrefixOf,
      null,
      replicate,
      span,
      splitOn,
      uncons,
      unwords,
      pack,
      unpack )

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
          | isChartName full cb = "chart "
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
  [ S.lastSegment full <> " :: " <> renderForallIn spelling sig
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
     in Right (keyword <> T.unwords (shown : ps ++ [body]))
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
    , nonlinear = cfg.nonlinear
    }

-- | The spelling output uses (design §7.3, @:set unicode@).
spellingOf :: Config -> Spelling
spellingOf cfg = if cfg.unicode then Unicode else Ascii

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
so @: a -> a@ finds @Num m -> Num m@ and @: Num -> Num@ finds @a -> a@.
-}
{- | @area :: Shape -> Num (m^2)@: a name and its signature as written back
in a scope (design §4.8), the name by its shortest spelling.
-}
signatureLine :: Spelling -> S.Scope -> Codebase -> Text -> Text
signatureLine spelling scope cb n =
  shortestName scope cb n
    <> " :: "
    <> maybe "?" (renderForallIn spelling) (signatureOf n cb)

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
              <> ".metron"
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
  -- A chart's frame and axes are minted again by its declaration (design
  -- §3.10, F3).
  types =
    [ (n, h)
    | (n, h) <- Map.toList cb.typeNames
    , under n
    , not
        ( maybe
            False
            (\d -> isAxesDef d || isJust (frameDefMoving d))
            (lookupTypeDef h cb)
        )
    ]
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
          | isChartName n cb = "chart "
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
