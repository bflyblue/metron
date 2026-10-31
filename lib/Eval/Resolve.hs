{- | Binding groups (design §2.2, §6.2, §6.3, §7.1): dependency analysis,
cycle construction and hashing, type inference, and entry into the
codebase. Nothing from a group is stored unless the whole group checks.
-}
module Eval.Resolve (
  ResolveError (..),
  renderResolveError,
  LabelKind (..),
  isLabel,
  Qualified (..),
  qualifyWith,
  qualifyName,
  resolveName,
  shortestName,
  shortestNameOf,
  namespaceLabels,
  isNamespace,
  disjointness,
  resolverFor,
  typeLookupFor,
  processGroup,
  enterData,
  queryScheme,
  signatureScheme,
  typeVariable,
  signatureText,
  annotationsFor,
  annotationsWith,
  ascriptionsIn,
  usesSignatures,
  storeTerm,
  withHint,
) where

import Control.Monad (when, zipWithM)
import Control.Monad.State.Strict (StateT, gets, lift, modify, runStateT)
import Data.Bifunctor (bimap)
import Data.Char (isLower)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (foldlM)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Builtin
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Desugar qualified as D
import Eval.Dimension
import Eval.Hash
import Eval.Infer
import Eval.Syntax qualified as S
import Eval.TCore (lintClosed, signatureHolds)
import Eval.Type

data ResolveError
  = DuplicateDefinition S.Name
  | Desugar DesugarError
  | {- | A type error in the named definition, at a span when provenance
    could place it.
    -}
    TypeErrorIn S.Name (Maybe S.Span) Text
  | -- | Elaboration produced ill-typed Typed Core: an internal error.
    LintFailure S.Name Text
  | -- | A @ declaration that cannot be entered, at the offending span.
    DataError S.Span Text
  | {- | A signature that cannot be entered or does not hold (design §4.8),
    at a span in the input of the declaration with the given key ('S.declKey').
    -}
    SignatureError Text S.Span Text
  deriving stock (Eq, Show)

-- | Render without source text; "Eval.Driver" renders with the excerpt.
renderResolveError :: ResolveError -> Text
renderResolveError = \case
  DuplicateDefinition n ->
    T.pack (show n.span.from.line)
      <> ":"
      <> T.pack (show n.span.from.col)
      <> ": `"
      <> n.text
      <> "` is defined twice in the same group"
  Desugar e -> renderDesugarError e
  TypeErrorIn n sp msg ->
    S.renderSpanError
      Nothing
      (fromMaybe n.span sp)
      ("in `" <> n.text <> "`: " <> msg)
  LintFailure n msg ->
    "internal error: elaboration of `"
      <> n.text
      <> "` produced ill-typed core: "
      <> msg
  DataError sp msg -> S.renderSpanError Nothing sp msg
  SignatureError _ sp msg -> S.renderSpanError Nothing sp msg

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

{- | A free name in an expression, resolved through the scope: its full path
and what it names. Two @use@s that both offer it give 'AAmbiguous'.
-}
resolveName :: S.Scope -> Codebase -> Text -> Maybe (Text, Resolved)
resolveName scope cb written = case qualifyName TermLabel scope cb written of
  Found full -> (full,) <$> resolvedAt cb full
  Ambiguous fulls -> Just (written, AAmbiguous fulls)
  NotFound -> Nothing

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

typeLookupFor :: Codebase -> TypeLookup
typeLookupFor cb = TypeLookup (`lookupTypes` cb) (withBuiltins (`lookupTypeDef` cb))

{- | The signatures of a codebase as inference sees them at a use (design
§4.8): a reference written under a signed name that still points where
the name does sees the signature.
-}
annotationsFor :: Codebase -> Annotations
annotationsFor cb = annotationsWith cb Map.empty

-- | 'annotationsFor' with the ascriptions of the term being checked.
annotationsWith :: Codebase -> Map.Map Text (Scheme, D.Path) -> Annotations
annotationsWith cb = Annotations $ \written h idx ->
  case (signatureOf written cb, lookupName written cb) of
    (Just sig, Just r) | r == Reference h idx -> Just sig
    -- An unsigned value is used with anonymous axes (design §3.9,
    -- decision 5).
    (Nothing, Just r)
      | r == Reference h idx
      , Just general <- typeOf r cb
      , let used = defaultAxes general
      , used /= general ->
          Just used
    _ -> Nothing

{- | The ascriptions the desugarer found (design §4.8), by marker, each
converted in the scope of its expression as a signature is, its
variables bound by its own @forall@ or by the signature of the definition
it is in (the given variables, which stay free in its scheme), with the
path an error in it is reported at: after the given prefix, a cycle
member's index, the key its span is recorded under ('D.ascriptionPath').
-}
ascriptionsIn ::
  S.Scope ->
  Codebase ->
  Bound ->
  D.Path ->
  Provenance ->
  Either ResolveError (Map.Map Text (Scheme, D.Path))
ascriptionsIn scope cb outer prefix prov =
  Map.fromList
    <$> sequence
      [ (\(sc, _) -> (marker, (sc, prefix ++ [D.ascriptionPath k])))
          <$> explicitScheme scope cb outer t
      | (k, (marker, t)) <- zip [0 ..] prov.ascriptions
      ]

{- | Whether a term references a signed name, or a value whose axes default
(design §3.9), so that checking it must see signatures.
-}
usesSignatures :: Codebase -> Term n -> Bool
usesSignatures cb t =
  any
    (\(h, i, w) -> isJust (annotationsFor cb `signatureAt` (w, h, i)))
    (Set.toList (refsWritten t))
 where
  signatureAt a (w, h, i) = a.signatureFor w h i

{- | A written lowercase name that names nothing a type can name (design
§7.3, §4.8): not @rank@, a built-in or declared type, a base unit or a
unit, in the scope. A @:ls@ query reads it as a variable; a signature or
an ascription refuses it unless a @forall@ binds it.
-}
typeVariable :: S.Scope -> Codebase -> Text -> Bool
typeVariable scope cb n =
  maybe False (isLower . fst) (T.uncons n)
    && n `notElem` ("rank" : builtinTypeNames)
    && qualifyName TypeLabel scope cb n == NotFound
    && n `notElem` [baseSymbol b | b <- [minBound .. maxBound]]
    && not isUnit
 where
  -- A chart's name is a unit's kin: a rescaling, whose frame is its
  -- parent's, is refused as such where a frame goes (design §3.10, F3).
  isUnit = case qualifyName TermLabel scope cb n of
    Found u -> isUnitName u cb || isChartName u cb
    _ -> False

{- | A signature as it is written back (design §4.8): headed by its
@forall@, so that it reads back as the same scheme in any scope, since a
bound variable shadows a unit of its name. Declared types print by hash,
for the driver to name ('Eval.Driver.nameTypes').
-}
signatureText :: Spelling -> Scheme -> Text
signatureText = renderForallWith showHash

{- | A signature after its definition was inferred (design §4.8): the
signature must hold of the definition's scheme, which must be at least as
general.
-}
checkSignature ::
  Text -> S.Span -> Text -> Scheme -> Scheme -> Either ResolveError ()
checkSignature key sp n sig general
  | signatureHolds sig general = Right ()
  | otherwise =
      Left
        ( SignatureError
            key
            sp
            ( "`"
                <> n
                <> "`'s definition has type `"
                <> renderScheme general
                <> "`, not as general as its signature `"
                <> renderScheme sig
                <> "`"
            )
        )

{- | A signature of the group: its key, its span, the scheme it was written
as, and the variables its @forall@ binds, which scope over the body of
its definition (design §4.8).
-}
data Signed = Signed {key :: Text, span :: S.Span, scheme :: Scheme, bound :: Bound}

{- | Enter a binding group into the codebase. Statements may refer to each
other in any order; strongly connected components are hashed as cycles.
Components are processed dependencies-first, so a reference from one
component to another always sees the new hash and its type.

Signatures (design §4.8) are converted in the scope they were written in,
after the group's types are entered. One for a name the group does not
define signs the stored definition; one for a name it defines is checked
when that name's component has been inferred, and a stored signature of a
name the group redefines is checked the same way unless the group gives a
new one.
-}
processGroup :: Codebase -> [S.Decl] -> Either ResolveError Codebase
processGroup cb0 decls
  | null charts = enterGroup True cb0 decls
  | otherwise = case enterGroup False cb0 part of
      -- The first pass, unchecked, may have dropped a signature that does
      -- not hold of a redefinition; the checked pass checks it.
      Right cb1 -> enterGroup True cb1{signatures = cb0.signatures} decls
      Left _ -> enterGroup True cb0 decls
 where
  -- A written type names a chart's axes by a label the chart's entry
  -- binds (design §3.9), and the group's signatures, data declarations
  -- and ascriptions are read before its definitions, or before a chart
  -- they do not use: so the group's charts, with the definitions they
  -- depend on, are entered first for their labels alone, unchecked
  -- against any annotation, and the whole group then again, which binds
  -- them to what they are. A chart that needs the group's own data
  -- declarations is entered with the group in one pass.
  bindings = [(s, b) | S.DBind s b <- decls]
  groupNames = Set.fromList [b.name.text | (_, b) <- bindings]
  charts = [b.name.text | (_, b) <- bindings, b.kind == S.ChartDecl]
  exists n = isLabel TermLabel cb0 n || Set.member n groupNames
  depsOf n =
    [ full
    | (s, b) <- bindings
    , b.name.text == n
    , w <- Set.toList (freeNames (asLambda b))
    , Found full <- [qualifyWith cb0.uses exists s w]
    , Set.member full groupNames
    ]
  closure = go Set.empty charts
   where
    go seen = \case
      [] -> seen
      n : ns
        | Set.member n seen -> go seen ns
        | otherwise -> go (Set.insert n seen) (depsOf n ++ ns)
  part =
    [d | d@S.DSpace{} <- decls]
      ++ [d | d@(S.DBind _ b) <- decls, Set.member b.name.text closure]

-- | 'processGroup' in one pass, checking annotations or not.
enterGroup :: Bool -> Codebase -> [S.Decl] -> Either ResolveError Codebase
enterGroup checking cb0 decls = do
  checkDuplicates (filter (not . S.isSignature) decls)
  checkDuplicates (filter S.isSignature decls)
  -- A name is never both a label and a namespace (design §7.6).
  case disjointness cb0 (concatMap newLabels decls) of
    Just (sp, msg) -> Left (DataError sp msg)
    Nothing -> pure ()
  -- Spaces first, then data declarations, in order: the definitions may
  -- use their constructors, and a chart its space (design §3.10, F2).
  cbSpaces <-
    foldlM
      (\cb (s, n, t) -> enterSpace s cb n t)
      cb0
      [(s, n, t) | S.DSpace s n t <- decls]
  cb1 <-
    foldlM (\cb (s, d) -> enterData s cb d) cbSpaces [(s, d) | S.DData s d <- decls]
  signed <-
    Map.fromList
      <$> sequence
        [ (n.text,) . uncurry (Signed (S.declKey d) d.span) <$> converted
        | d@(S.DSig s n t) <- decls
        , let converted = case signatureScheme s cb1 t of
                Left (DataError sp msg) -> Left (SignatureError (S.declKey d) sp msg)
                other -> other
        ]
  let bindings = [(s, b) | S.DBind s b <- decls]
      groupNames = Set.fromList [b.name.text | (_, b) <- bindings]
  -- A signature for a stored definition the group does not redefine.
  cb2 <-
    foldlM
      ( \cb (n, sig) -> case lookupName n cb of
          Just r
            | Just general <- typeOf r cb -> do
                checkSignature sig.key sig.span n sig.scheme general
                pure (setSignature n sig.scheme cb)
          -- No definition yet: the signature waits in the scratch for one
          -- (design §4.8); :add and :update refuse it if none comes.
          _ -> pure (setSignature n sig.scheme cb)
      )
      cb1
      [(n, sig) | (n, sig) <- Map.toList signed, Set.notMember n groupNames]
  let exists n = isLabel TermLabel cb2 n || Set.member n groupNames
      -- Dependencies by full path: a name written in the group resolves
      -- through its scope to the group's own names first (design §7.6).
      dependsOn (s, b) =
        Set.toList
          ( Set.fromList
              [ full
              | w <- Set.toList (freeNames (asLambda b))
              , Found full <- [qualifyWith cb2.uses exists s w]
              , Set.member full groupNames
              ]
          )
      nodes = [(sb, (snd sb).name.text, dependsOn sb) | sb <- bindings]
  foldlM (enterComponent checking groupNames signed) cb2 (stronglyConnComp nodes)
 where
  newLabels = \case
    S.DBind _ b -> [(b.name.text, "definition", b.name.span)]
    S.DData _ d ->
      (d.name.text, "type", d.name.span)
        : [(c.text, "constructor", c.span) | (c, _) <- d.constructors]
        ++ [ (n.text, "field", n.span)
           | (_, fs) <- d.constructors
           , S.FieldDecl (Just n) _ <- fs
           ]
    S.DSpace _ n _ -> [(n.text, "type", n.span)]
    S.DSig{} -> []

checkDuplicates :: [S.Decl] -> Either ResolveError ()
checkDuplicates = go Set.empty
 where
  go _ [] = Right ()
  go seen (b : bs)
    | b.name.text `Set.member` seen = Left (duplicate b)
    | otherwise = go (Set.insert b.name.text seen) bs
  duplicate = \case
    d@(S.DSig _ n _) ->
      SignatureError
        (S.declKey d)
        d.span
        ("`" <> n.text <> "` has two signatures in the same group")
    d -> DuplicateDefinition d.name

asLambda :: S.Binding -> S.Expr
asLambda b = case b.params of
  -- A unit's body is made a unit (design §3.10, U7).
  [] | b.kind == S.Unit -> S.Expr b.body.span (S.UnitBody b.body)
  [] -> b.body
  _ -> S.Expr b.span (S.Lam b.params b.body)

{- | Enter one component. A definition's declared uncertainties are labelled
with its full path (design §3.2.4), so that @lab.offset = 1 ± 0.1@ and
@field.offset = 1 ± 0.1@ are two measurements, not one.
-}
enterComponent ::
  Bool ->
  Set Text ->
  Map.Map Text Signed ->
  Codebase ->
  SCC (S.Scope, S.Binding) ->
  Either ResolveError Codebase
enterComponent checking group signed cb0 = \case
  AcyclicSCC (scope, b) -> do
    (written, prov) <-
      either
        (Left . Desugar)
        Right
        ( desugarDefinition
            b.name.text
            (groupResolver group Set.empty scope cb0)
            (asLambda b)
        )
    -- The axis type a chart mints is stored before the chart is checked,
    -- since its constructor's type is looked up (design §3.9, decision 1).
    let minted = mintedBy [b.name.text] written
        cb = mintTypes minted cb0
    -- The readings the types choose are written in before it is hashed
    -- (design §3.10, U4, U6), its signature taking part. Not its
    -- ascriptions: they are not in the term, so its printed source would
    -- not read back, where a signature is written back with it.
    term <-
      either
        (Left . typeErrorIn b prov)
        Right
        (withReadings cb [signedAs signed cb0 b.name.text] written)
    (schemes, typed) <-
      either
        (Left . typeErrorIn b prov)
        Right
        (elaborateClosed (typeLookupFor cb) term)
    linted <-
      either (Left . LintFailure b.name) Right (lintClosed (typeLookupFor cb) typed)
    -- With ascriptions, they are checked on the term desugared with markers.
    (checkTerm, checkProv, asc) <-
      if not checking || null prov.ascriptions
        then pure (term, prov, Map.empty)
        else do
          (marked, markedProv) <-
            either
              (Left . Desugar)
              Right
              ( desugarMarked
                  ""
                  b.name.text
                  (groupResolver group Set.empty scope cb)
                  VNil
                  (asLambda b)
              )
          (checkTerm, asc) <-
            scopedAscriptions scope cb signed 0 [] "" b.name.text marked markedProv
          pure (checkTerm, markedProv, asc)
    checked <-
      if checking
        then annotatedCheck cb asc checkTerm (typeErrorIn b checkProv)
        else pure Nothing
    let h = hashTerm term
        ref = Reference h Nothing
        stored = preferLint schemes linted
    cb' <-
      labelFrames
        minted
        [b]
        (bindName b.name.text ref (addTerm h term stored typed cb))

    signed' <-
      if checking
        then signMembers signed cb [(b, fromMaybe stored checked)]
        else pure id
    pure (signed' (markKind b.kind b.name.text cb'))
  CyclicSCC bs -> enterCycle checking group signed cb0 bs

{- | A member's ascriptions, desugared with markers, converted with the
variables of the member's signature in scope (design §4.8), and the term
to check them on. When an ascription names one of those variables, the
member's body is wrapped in a marker for the signature itself
('D.signatureMarker'), so that the definition's type and its ascriptions
meet the same variables: those of the signature, renumbered into a range
of the member's own ('scopedSignature'), which every marker shares and no
variable of inference meets. Their unification is flexible; the
signature's check afterwards, on the scheme this check gives, refuses a
definition whose ascriptions narrowed a variable or made two one.
-}
scopedAscriptions ::
  S.Scope ->
  Codebase ->
  Map.Map Text Signed ->
  Int ->
  D.Path ->
  Text ->
  Text ->
  Term n ->
  Provenance ->
  Either ResolveError (Term n, Map.Map Text (Scheme, D.Path))
scopedAscriptions scope cb signed member prefix tag n marked prov = do
  let scoped = scopedSignature member (Map.lookup n signed)
  asc <- ascriptionsIn scope cb (maybe Map.empty fst scoped) prefix prov
  pure $ case scoped of
    Just (bound, sigType)
      | any (mentions (Map.keysSet bound) . snd) prov.ascriptions ->
          let wrapper = D.signatureMarker tag
           in (PrimApp wrapper [marked], Map.insert wrapper (Forall [] sigType, prefix) asc)
    _ -> (marked, asc)
 where
  mentions vars t =
    not (Set.null (Set.intersection vars (Set.fromList (map (.text) (tyNames t)))))

{- | The variables a member's signature binds, renumbered into a range of
the member's own, far from every variable an inference run makes, with
the signature's type over them; none for a member without a signature or
one without variables.
-}
scopedSignature :: Int -> Maybe Signed -> Maybe (Bound, Type)
scopedSignature member = \case
  Just sig
    | not (Map.null sig.bound) ->
        let Forall vs ty = sig.scheme
            base = scopedBase + member * scopedStride
            moved = Map.fromList [(v, varArg k (base + v)) | (v, k) <- vs]
            bound =
              Map.map (renumberBound (base +)) sig.bound
         in Just (bound, substOnce moved ty)
  _ -> Nothing
 where
  -- Below 'axisBase', where axis variables start, and far above the
  -- variables of any other kind a run makes.
  scopedBase = 500000000
  scopedStride = 100000

{- | A definition's term, or a cycle's, with the readings the types choose
written in (design §3.10, U4, U6): each quantity whose literal is followed
by something its spelling does not make a unit or a chart is @scale@ or
@pointOn@, each such @to@ the display unit's or @toChart@. They are
inferred with each member's signature as an ascription of its body, and
with the signatures of the names it uses, so that @per u = 3 u@ under
@per :: forall d. Unit d -> Num d@ reads @scale@; the term written in
then stands alone, as a stored term must, its types its Core's, and its
printed source reads back with the signature written beside it. A term
with no such quantity or @to@ is returned as it is.
-}
withReadings ::
  Codebase -> [Maybe Scheme] -> Term Z -> Either TypeError (Term Z)
withReadings cb sigs term
  | not (hasReadingMarkers term) = Right term
  | otherwise = do
      chosen <-
        readingsOf
          (Annotations (annotationsWith cb Map.empty).signatureFor ascriptions)
          (typeLookupFor cb)
          signedTerm
      Right (rewriteReadings chosen term)
 where
  marker :: Int -> Text
  marker i = D.signatureMarker ("§readings" <> T.pack (show i))
  sigAt i = case drop i sigs of
    Just sc : _ -> Just sc
    _ -> Nothing
  wrap :: Int -> Term n -> Term n
  wrap i body = maybe body (const (PrimApp (marker i) [body])) (sigAt i)
  wrapMembers :: Int -> Vec k (Term n) -> Vec k (Term n)
  wrapMembers i = \case
    VNil -> VNil
    VCons b rest -> VCons (wrap i b) (wrapMembers (i + 1) rest)
  (signedTerm, ascriptions) = case term of
    Cycle hs bodies ->
      ( Cycle hs (wrapMembers 0 bodies)
      , Map.fromList [(marker i, (sc, [i])) | (i, Just sc) <- zip [0 ..] sigs]
      )
    _ ->
      (wrap 0 term, Map.fromList [(marker 0, (sc, [])) | Just sc <- take 1 sigs])

-- | The signature a name is to have: the group's for it, else the one it has.
signedAs :: Map.Map Text Signed -> Codebase -> Text -> Maybe Scheme
signedAs signed cb n = maybe (signatureOf n cb) (Just . (.scheme)) (Map.lookup n signed)

{- | The check of a definition that the annotations of the input take part
in (design §4.8): its uses of signed names see their signatures, and its
ascriptions narrow. Only when it has any; the schemes it gives are the
definition's as checked, never stored, since a stored term's types are its
Core's alone.
-}
annotatedCheck ::
  Codebase ->
  Map.Map Text (Scheme, D.Path) ->
  Term Z ->
  (TypeError -> ResolveError) ->
  Either ResolveError (Maybe [Scheme])
annotatedCheck cb asc term err
  | Map.null asc && not (usesSignatures cb term) = Right Nothing
  | otherwise =
      either
        (Left . err)
        (Right . Just . fst)
        (elaborateClosedWith (annotationsWith cb asc) (typeLookupFor cb) term)

{- | The signatures of a component's members, each with its scheme as
checked (design §4.8): the group's signature for a member, else the one the
name carried before, must hold. Given the codebase before the members were
bound; returns what gives the members their signatures.
-}
signMembers ::
  Map.Map Text Signed ->
  Codebase ->
  [(S.Binding, [Scheme])] ->
  Either ResolveError (Codebase -> Codebase)
signMembers signed before members =
  foldr (.) id
    <$> sequence
      [ case (Map.lookup n signed, signatureOf n before) of
          (Just sig, _) -> do
            checkSignature sig.key sig.span n sig.scheme general
            pure (setSignature n sig.scheme)
          (Nothing, Just old) -> do
            checkSignature n b.name.span n old general
            pure (setSignature n old)
          (Nothing, Nothing) -> pure id
      | (i, (b, schemes)) <- zip [0 :: Int ..] members
      , let n = b.name.text
            general = fromMaybe (Forall [] boolT) (nth i schemes)
      ]
 where
  nth i xs = case drop i xs of
    x : _ -> Just x
    [] -> Nothing

-- | Inference and lint must agree; lint is the authority if they ever differ.
preferLint :: [Scheme] -> [Scheme] -> [Scheme]
preferLint _ linted = linted

typeErrorIn :: S.Binding -> Provenance -> TypeError -> ResolveError
typeErrorIn b prov err =
  located
    b.name
    (provenanceAt err.path prov)
    (fillOperands err.path prov err.message)

-- | A type error at a located node, with the node's hint under the message.
located :: S.Name -> Maybe (S.Span, Maybe Text) -> Text -> ResolveError
located n at msg = case at of
  Just (sp, hint) -> TypeErrorIn n (Just sp) (withHint hint msg)
  Nothing -> TypeErrorIn n Nothing msg

withHint :: Maybe Text -> Text -> Text
withHint hint msg = maybe msg (\h -> msg <> "\n  hint: " <> h) hint

{- | Design §6.2. The members are first desugared in their input order to
compute ordering hashes with the cycle variables as placeholders, then
desugared again in the resulting order to build the stored 'Cycle'.
-}
enterCycle ::
  Bool ->
  Set Text ->
  Map.Map Text Signed ->
  Codebase ->
  [(S.Scope, S.Binding)] ->
  Either ResolveError Codebase
enterCycle checking group signed cb sbs = do
  ordering <- mapM (\sb -> (,sb) <$> placeholderHashOf sb) sbs
  let sortedScoped = map snd (sortOn fst ordering)
      sorted = map snd sortedScoped
  case vecFromList sortedScoped of
    SomeVec members -> do
      let ctx = vecAppend (vecMap ((.name.text) . snd) members) VNil
      desugared <- vecTraverse (desugarOne ctx) members
      let bodies = vecMap fst desugared
          provs = vecToList (vecMap snd desugared)
          written = Cycle (vecMap (Hint . (.name.text) . snd) members) bodies
          -- The axis types the members' charts mint (design §3.9).
          minted = mintedBy (map (.name.text) sorted) written
          cbm = mintTypes minted cb
      -- The readings the types choose, written in before the cycle is
      -- hashed (design §3.10, U4, U6), the members' signatures taking part.
      cycleTerm <-
        either
          (Left . cycleTypeError sorted provs)
          Right
          (withReadings cbm [signedAs signed cb b.name.text | b <- sorted] written)
      let h = hashTerm cycleTerm
      (schemes, typed) <-
        either
          (Left . cycleTypeError sorted provs)
          Right
          (elaborateClosed (typeLookupFor cbm) cycleTerm)
      linted <-
        either
          (Left . LintFailure (headName sorted))
          Right
          (lintClosed (typeLookupFor cbm) typed)
      -- With ascriptions, they are checked on the members desugared with
      -- markers, each member's tagged by its index.
      checked <-
        if not checking
          then pure Nothing
          else
            if all (null . (.ascriptions)) provs
              then annotatedCheck cbm Map.empty cycleTerm (cycleTypeError sorted provs)
              else do
                (marked, _) <-
                  runStateT
                    ( vecTraverse
                        ( \m -> do
                            i <- gets id
                            modify (+ 1)
                            lift (desugarMarkedOne ctx i m)
                        )
                        members
                    )
                    (0 :: Int)
                let markedProvs = vecToList (vecMap snd marked)
                -- Each member's body is wrapped in its signature's marker when
                -- its ascriptions name the signature's variables.
                (scoped, (_, asc)) <-
                  runStateT
                    ( vecTraverse
                        ( \(body, prov) -> do
                            i <- gets fst
                            let (s, b) = sortedScoped !! i
                            (body', asc) <-
                              lift
                                ( scopedAscriptions
                                    s
                                    cbm
                                    signed
                                    i
                                    [i]
                                    (T.pack (show i))
                                    b.name.text
                                    body
                                    prov
                                )
                            modify (\(_, acc) -> (i + 1, Map.union acc asc))
                            pure body'
                        )
                        marked
                    )
                    (0 :: Int, Map.empty)
                let markedTerm = Cycle (vecMap (Hint . (.name.text) . snd) members) scoped
                annotatedCheck cbm asc markedTerm (cycleTypeError sorted markedProvs)
      let stored = preferLint schemes linted
          cb' = addTerm h cycleTerm stored typed cbm
          bindMember acc (i, b) =
            let ref = Reference h (Just i)
                acc' = bindName b.name.text ref acc
             in markKind b.kind b.name.text acc'
      signed' <-
        if checking
          then signMembers signed cbm [(b, fromMaybe stored checked) | b <- sorted]
          else pure id
      labelled <-
        labelFrames minted sorted (foldl bindMember cb' (zip [0 ..] sorted))

      pure (signed' labelled)
 where
  -- The members are local binders by their full paths, found through each
  -- member's own scope (design §7.6).
  memberNames = Set.fromList [b.name.text | (_, b) <- sbs]
  desugarOne ::
    Vec k Text -> (S.Scope, S.Binding) -> Either ResolveError (Term k, Provenance)
  desugarOne ctx (scope, b) =
    either
      (Left . Desugar)
      Right
      ( D.desugarMember
          b.name.text
          (groupResolver group memberNames scope cb)
          ctx
          (asLambda b)
      )
  desugarMarkedOne ::
    Vec k Text ->
    Int ->
    (S.Scope, S.Binding) ->
    Either ResolveError (Term k, Provenance)
  desugarMarkedOne ctx i (scope, b) =
    either
      (Left . Desugar)
      Right
      ( D.desugarMarked
          (T.pack (show i))
          b.name.text
          (groupResolver group memberNames scope cb)
          ctx
          (asLambda b)
      )

  placeholderHashOf :: (S.Scope, S.Binding) -> Either ResolveError Hash
  placeholderHashOf sb = case vecFromList [b.name.text | (_, b) <- sbs] of
    SomeVec ns -> do
      (t, _) <- desugarOne (vecAppend ns VNil) sb
      pure (placeholderHash t)

  -- Inside a cycle the error path starts with the member index.
  cycleTypeError sorted provs err = case err.path of
    i : rest
      | Just b <- nth i sorted
      , Just prov <- nth i provs ->
          located b.name (provenanceAt rest prov) (fillOperands rest prov err.message)
    _ -> TypeErrorIn (headName sorted) Nothing err.message
  nth i xs = case drop i xs of
    x : _ | i >= 0 -> Just x
    _ -> Nothing
  headName = \case
    b : _ -> b.name
    [] -> S.Name (S.Span (S.Pos 1 1) (S.Pos 1 1)) "?"

{- | Names an expression mentions that are not bound inside it. A field chain
on a free name also mentions each of its dotted prefixes, any of which may
be a qualified name (design §7.6).
-}
freeNames :: S.Expr -> Set Text
freeNames = go Set.empty
 where
  chain ex = case ex.node of
    S.Var x -> Just (x, [])
    S.FieldOf a f -> (\(x, fs) -> (x, fs ++ [f])) <$> chain a
    _ -> Nothing
  go bound e = case e.node of
    S.FieldOf _ _
      | Just (x, fs) <- chain e
      , x `Set.notMember` bound ->
          Set.fromList [T.intercalate "." (x : take k fs) | k <- [0 .. length fs]]
    S.Num _ -> Set.empty
    S.Labelled _ a -> go bound a
    S.Tuple es -> foldMap (go bound) es
    S.List es -> foldMap (go bound) es
    S.CaseOf s alts ->
      go bound s
        <> foldMap
          (\(p, b) -> go (foldr (Set.insert . (.text)) bound (patternNames p)) b)
          alts
    S.Bool _ -> Set.empty
    S.Var x -> if x `Set.member` bound then Set.empty else Set.singleton x
    S.Lam ns b -> go (foldr (Set.insert . (.text)) bound ns) b
    S.App f a -> go bound f <> go bound a
    S.Let n ps rhs body ->
      go (foldr (Set.insert . (.text)) bound ps) rhs
        <> go (Set.insert n.text bound) body
    S.If c t f -> go bound c <> go bound t <> go bound f
    S.BinOp op a b -> opNames op <> go bound a <> go bound b
    S.Neg a -> go bound a
    S.Pow a _ -> go bound a
    S.SectionL op a -> opNames op <> go bound a
    S.SectionR a op -> opNames op <> go bound a
    S.Vec es -> foldMap (go bound) es
    S.Proj a _ -> go bound a
    S.Slice a _ _ -> go bound a
    S.FieldOf a _ -> go bound a
    S.Record hd fs -> go bound hd <> foldMap (go bound . snd) fs
    S.Ascribe a _ -> go bound a
    S.ChartForm cl ->
      go bound cl.parent
        <> foldMap (go bound) cl.origin
        <> foldMap (go bound) cl.step
        <> foldMap (go bound) cl.generators
        <> foldMap (go bound) cl.spin
    S.FromTo v c c1 -> go bound v <> go bound c <> go bound c1
    S.UnitBody a -> go bound a
  opNames = \case
    S.Infix n -> Set.singleton n
    _ -> Set.empty

{- | The types the members' charts mint (design §3.10, F3; §3.9, decision
1), by the member's full path: a frame, for a root, a chart with an origin
or one turned or spinning, and axes for one turned or spinning, each found
as a constructor in the chart's Core stamped with its path. A rescaling
mints neither.
-}
mintedBy :: [Text] -> Term n -> [(Text, [(Hash, TypeDef)])]
mintedBy names term =
  [ (n, found)
  | n <- names
  , let found =
          [ (h, def)
          | def <- [frameDef n False, frameDef n True, axesDef n]
          , let h = hashTypeDef def
          , Set.member h (conTypes term)
          ]
  , not (null found)
  ]

-- | Store the types charts mint, as declared types are.
mintTypes :: [(Text, [(Hash, TypeDef)])] -> Codebase -> Codebase
mintTypes minted cb = foldl (\acc (h, def) -> addTypeDef h def acc) cb (concatMap snd minted)

{- | Name the frame each chart mints as the chart (design §3.10, F3), a
type label under the chart's own full path, so that a type names it,
@Point degC@: types and terms are separate namespaces. A chart that mints
no frame, a rescaling, takes the label away from the frame it once
minted. A chart cannot take the name of a declared type or a space.
-}
labelFrames ::
  [(Text, [(Hash, TypeDef)])] ->
  [S.Binding] ->
  Codebase ->
  Either ResolveError Codebase
labelFrames minted members cb0 = foldlM label cb0 members
 where
  label cb b = case lookupTypeName n cb >>= (`lookupTypeDef` cb) of
    Just def
      | isNothing (frameDefMoving def) && isJust frame ->
          Left
            ( DataError
                b.name.span
                ("`" <> n <> "` names a type; a chart's frame is named as the chart")
            )
    Just def
      | Nothing <- frame
      , isJust (frameDefMoving def) ->
          Right cb{typeNames = Map.delete n cb.typeNames}
    _ -> Right (maybe cb (\h -> bindTypeName n h cb) frame)
   where
    n = b.name.text
    frame =
      case [ h
           | (m, found) <- minted
           , m == n
           , (h, def) <- found
           , isJust (frameDefMoving def)
           ] of
        h : _ -> Just h
        [] -> Nothing

{- | Enter a Core term that already has its hash, as when loading a store
(design §7.4): infer, lint and add. The term must only reference hashes the
codebase already holds, which the loader ensures by ordering.
-}
storeTerm :: Hash -> Term Z -> Codebase -> Either Text Codebase
storeTerm h term cb = do
  (schemes, typed) <-
    either (Left . (.message)) Right (elaborateClosed (typeLookupFor cb) term)
  linted <- lintClosed (typeLookupFor cb) typed
  pure (addTerm h term (preferLint schemes linted) typed cb)

{- | Record what a binding declared besides its value.
| Record what a binding declared besides its value. A plain `let` clears
any unit or chart flag the name carried: `let g = 9.81 m/s^2` is a
quantity even though `g` was the gram.
-}
markKind :: S.BindKind -> Text -> Codebase -> Codebase
markKind kind n cb = case kind of
  S.Plain -> clearFlags n cb
  S.Unit -> markUnit n cb
  S.ChartDecl -> markChart n cb

-- | The variables a pattern binds.
patternNames :: S.Pattern -> [S.Name]
patternNames p = case p.node of
  S.PCon _ ns -> ns
  S.PVar n -> [n]
  S.PWild -> []

-- Data declarations ----------------------------------------------------------------

{- | Enter a @data@ declaration (design §2.3). The parameters take their
kinds from the positions the fields use them in; the field types are
checked against the types in scope; the definition is hashed and stored,
and the type's and constructors' names bound to it.
-}
enterData :: S.Scope -> Codebase -> S.DataDecl -> Either ResolveError Codebase
enterData scope cb decl = do
  distinct "parameter" decl.params
  case [p | p <- decl.params, p.text == "rank"] of
    p : _ ->
      Left
        ( DataError
            p.span
            "`rank` is the type function on shapes and cannot be a parameter"
        )
    [] -> pure ()
  distinct "constructor" (map fst decl.constructors)
  distinct "field" (map fst fieldLabels)
  -- Field names make a record: a type of one constructor, so that @r.f@ is total.
  case (decl.constructors, fieldLabels) of
    (_ : _ : _, (n, _) : _) ->
      Left (DataError n.span "field names need a type with one constructor")
    _ -> pure ()
  -- Two passes: the first learns the parameters' kinds from where they
  -- appear, the second converts with the kinds known, so that the
  -- arguments of a recursive occurrence can be read by their kinds, and
  -- each length parameter with its companion axis parameter (design §3.9),
  -- each frame parameter with its axes and space (design §3.10).
  let preset =
        Map.fromList
          [ (p, KFrame)
          | p <- concatMap (framesNamed . (.ty)) (concatMap snd decl.constructors)
          , p `elem` env.paramNames
          ]
  (_, kinds1) <- runStateT (convertAll env) preset
  case [p | p <- decl.params, Map.member (vectorKey p.text) kinds1] of
    p : _ ->
      Left
        ( DataError
            p.span
            ( "the axes of the frame parameter `"
                <> p.text
                <> "` cannot be written in a declaration: no type says how many it has"
            )
        )
    [] -> pure ()
  let written = [(p, Map.findWithDefault KType p kinds1) | p <- env.paramNames]
      comps = companionsOf (length written) written Map.empty Set.empty env.params
  (fieldss, kinds) <-
    runStateT
      (convertAll (env :: DataEnv){axisOf = comps.compAxes, frames = comps.compFrames})
      kinds1
  let params =
        [(i, Map.findWithDefault KType p.text kinds) | (i, p) <- zip [0 ..] decl.params]
          ++ comps.compVars
      def =
        TypeDef
          params
          fieldss
          -- The declared full path (design §2.3, §7.6): @a.Body@ and
          -- @b.Body@ with the same fields are two types.
          ( if decl.structural
              then structuralLabel
              else Owner decl.name.text
          )
      h = hashTypeDef def
      cb' = bindTypeName decl.name.text h (addTypeDef h def cb)
  -- A built-in type's name is reserved, except that @Bool@ may name the
  -- declaration it is (design §7.7): the library's, or an equal one.
  when (S.lastSegment decl.name.text `elem` builtinTypeNames && h /= boolHash)
    $ Left
      ( DataError
          decl.name.span
          ("`" <> S.lastSegment decl.name.text <> "` is a built-in type")
      )
  let
    withCons =
      foldl
        (\acc (i, (c, _)) -> bindConName c.text h i acc)
        cb'
        (zip [0 ..] decl.constructors)
  pure
    (foldl (\acc (n, j) -> bindFieldName n.text h 0 j acc) withCons fieldLabels)
 where
  env = emptyEnv cb scope decl.name (map (.text) decl.params)
  convertAll e = mapM (mapM (tyType e . (.ty)) . snd) decl.constructors
  fieldLabels =
    [ (n, j)
    | (_, fs) <- decl.constructors
    , (j, S.FieldDecl (Just n) _) <- zip [0 :: Int ..] fs
    ]
  distinct what = go Set.empty
   where
    go _ [] = Right ()
    go seen (n : ns)
      | n.text `Set.member` seen =
          Left (DataError n.span (what <> " `" <> n.text <> "` appears twice"))
      | otherwise = go (Set.insert n.text seen) ns

{- | Enter a space's declaration (design §3.10, F2): a nominal space of the
amounts of a type, a number or a vector of literal length, minted as a
type stamped with its full path, beside its base axes for a vector space,
and named as declared.
-}
enterSpace ::
  S.Scope -> Codebase -> S.Name -> S.TyExpr -> Either ResolveError Codebase
enterSpace scope cb n t = do
  ty <- fst <$> runStateT (tyType (emptyEnv cb scope n []) t) Map.empty
  (lens, d) <- case ty of
    TTensor SNil d -> Right ([], d)
    TTensor (SCons (LLit k) AAnon SNil) d -> Right ([k], d)
    _ ->
      Left
        (DataError t.span "a space is of numbers or of vectors, as in Num K or Vec 3 m")
  when (S.lastSegment n.text `elem` builtinTypeNames)
    $ Left (DataError n.span ("`" <> S.lastSegment n.text <> "` is a built-in type"))
  let def = spaceDef n.text lens d
      h = hashTypeDef def
      withBase =
        if null lens
          then id
          else addTypeDef (axesHash n.text) (axesDef n.text)
  pure (bindTypeName n.text h (withBase (addTypeDef h def cb)))

builtinTypeNames :: [Text]
builtinTypeNames =
  [ "Bool"
  , "Num"
  , "Unit"
  , "Quantity"
  , "Amount"
  , "Vec"
  , "Mat"
  , "Tensor"
  , "Point"
  , "Chart"
  , "Diff"
  , "Coords"
  ]

data DataEnv = DataEnv
  { codebase :: Codebase
  , scope :: S.Scope
  -- ^ where the type is written: its names resolve through this (design §7.6)
  , self :: S.Name
  -- ^ the type being declared, by its full path
  , params :: Map.Map Text VarId
  , paramNames :: [Text]
  , axisOf :: Map.Map Text VarId
  -- ^ each length parameter's companion axis parameter (design §3.9)
  , sized :: Map.Map Text Int
  -- ^ the length of each sized @forall@ binder, @(a : 3)@ (design §3.9)
  , frames :: Map.Map Text Frame
  -- ^ each frame variable's frame, with its companions (design §3.10, F1)
  , spaces :: Map.Map Text Space
  -- ^ each space variable's space, with its companions
  }

-- | An environment for a type with the given parameters, numbered in order.
emptyEnv :: Codebase -> S.Scope -> S.Name -> [Text] -> DataEnv
emptyEnv cb scope self ps =
  DataEnv
    { codebase = cb
    , scope = scope
    , self = self
    , params = Map.fromList (zip ps [0 ..])
    , paramNames = ps
    , axisOf = Map.empty
    , sized = Map.empty
    , frames = Map.empty
    , spaces = Map.empty
    }

{- | The companions of written variables with their kinds (design §3.9,
§3.10), numbered on from the given id: an axis set for each length; for
each space its shape, dimension and base axes; and for each frame its
axes and its space, the one its binder names (a declared one, or a space
variable) or one of its own. A frame or space whose axes are written as a
length has a space of one axis set, of a length of its own.
-}
data Companions = Companions
  { compAxes :: Map.Map Text VarId
  , compFrames :: Map.Map Text Frame
  , compSpaces :: Map.Map Text Space
  , compVars :: [(VarId, Kind)]
  }

companionsOf ::
  Int ->
  [(Text, Kind)] ->
  Map.Map Text (Either Space Text) ->
  Set Text ->
  Map.Map Text VarId ->
  Companions
companionsOf next written annotated vector ids = Companions axes frameMap spaceMap (reverse vs3)
 where
  idOf n = Map.findWithDefault 0 n ids
  -- Lengths' axes first, in order, then spaces', then frames'.
  (axes, k1, vs1) =
    foldl
      (\(m, k, vs) n -> (Map.insert n k m, k + 1, (k, KAxis) : vs))
      (Map.empty, next, [])
      [n | (n, KLen) <- written]
  (spaceMap, k2, vs2) =
    foldl
      ( \(m, k, vs) n ->
          let (sp, k', new) = freshSpace (SpVar (idOf n)) (Set.member n vector) k
           in (Map.insert n sp m, k', reverse new ++ vs)
      )
      (Map.empty, k1, vs1)
      [n | (n, KSpace) <- written]
  (frameMap, _, vs3) =
    foldl
      ( \(m, k, vs) n ->
          let (sp, k', new) = case Map.lookup n annotated of
                Just (Left named) -> (named, k + 1, [])
                Just (Right s) | Just sp' <- Map.lookup s spaceMap -> (sp', k + 1, [])
                _ -> freshSpace (SpVar (k + 1)) (Set.member n vector) (k + 2)
              spVars = case Map.lookup n annotated of
                Just _ -> []
                Nothing -> [(k + 1, KSpace)]
           in ( Map.insert n (Frame (FrVar (idOf n)) (AVar k) sp) m
              , k'
              , reverse new ++ reverse spVars ++ (k, KAxis) : vs
              )
      )
      (Map.empty, k2, vs2)
      [n | (n, KFrame) <- written]
  -- A space of its own: its shape (one axis set of a length of its own, if
  -- its axes are written), dimension and base axes.
  freshSpace slot isVector k =
    let (shape, shapeVar, k')
          | isVector = (SCons (LVar k 0) AAnon SNil, (k, KLen), k + 1)
          | otherwise = (SVar k, (k, KShape), k + 1)
     in ( Space slot shape (dimVar k') (AVar (k' + 1))
        , k' + 2
        , [shapeVar, (k', KDim), (k' + 1, KAxis)]
        )

-- | Conversion of written types, learning the parameters' kinds.
type Kinds = StateT (Map.Map Text Kind) (Either ResolveError)

{- | Where a variable's axes are written as a length (design §3.10, F4):
recorded beside the kinds, so that its space is one of one axis set.
-}
vectorKey :: Text -> Text
vectorKey = ("§vec:" <>)

bad :: S.TyExpr -> Text -> Kinds a
bad t msg = lift (Left (DataError t.span msg))

kindNoun :: Kind -> Text
kindNoun = \case
  KType -> "a type"
  KLen -> "a length"
  KShape -> "a shape"
  KDim -> "a dimension"
  KAxis -> "an axis set"
  KFrame -> "a frame"
  KSpace -> "a space"
  KRole -> "a role"

-- | A parameter used at a kind: record it, or report the clash.
useParam :: DataEnv -> S.TyExpr -> Text -> Kind -> Kinds VarId
useParam env t p k = do
  known <- gets (Map.lookup p)
  case known of
    Just k'
      | k' /= k ->
          bad
            t
            ( "parameter `"
                <> p
                <> "` is used both as "
                <> kindNoun k'
                <> " and as "
                <> kindNoun k
            )
    _ -> do
      modify (Map.insert p k)
      pure (Map.findWithDefault 0 p env.params)

{- | The names a written type uses where a frame goes (design §3.10, F4):
after @Point@, @Chart@, @Diff@ and @Coords@.
-}
framesNamed :: S.TyExpr -> [Text]
framesNamed e = case e.node of
  S.TyApp hd [a]
    | hd.text `elem` ["Point", "Chart", "Diff", "Coords"]
    , S.TyName n <- a.node ->
        [n]
  S.TyApp _ args -> concatMap framesNamed args
  S.TyTuple ts -> concatMap framesNamed ts
  S.TyList a -> framesNamed a
  S.TyFun a b -> framesNamed a ++ framesNamed b
  S.TyForall _ a -> framesNamed a
  _ -> []

tyType :: DataEnv -> S.TyExpr -> Kinds Type
tyType env t = case t.node of
  S.TyName n
    | Map.member n env.params -> TVar <$> useParam env t n KType
    | n == "Bool" -> pure boolT
    | n == "Num" -> pure numT
    | n == "Unit" -> pure (TUnit dimOne)
    | n == "Amount" ->
        bad t "Amount is a role, not a type: an amount is Num d, or Quantity Amount d"
    | n `elem` builtinTypeNames -> bad t ("`" <> n <> "` needs its arguments")
    | otherwise -> applied env t n []
  S.TyApp hd args
    | hd.text == "rank" ->
        bad
          t
          "rank s is a length, not a type; write it where a length goes, as in Vec (rank s)"
    | Map.member hd.text env.params ->
        bad t ("parameter `" <> hd.text <> "` takes no arguments")
    | otherwise -> case (hd.text, args) of
        ("Num", [d]) -> TTensor SNil <$> tyDim env d
        -- A unit takes its dimension as Num does (design §3.10, U1).
        ("Unit", [d]) -> TUnit <$> tyDim env d
        -- A quantity in a role (design §3.10, U9): @Quantity Amount d@ is
        -- @Num d@ and @Quantity Unit d@ is @Unit d@.
        ("Quantity", [r]) -> (\x -> TQty x SNil dimOne) <$> tyRole env r
        ("Quantity", [r, d]) -> (`TQty` SNil) <$> tyRole env r <*> tyDim env d
        ("Vec", [n]) -> (\l -> TTensor (position l SNil) dimOne) <$> tyLen env n
        ("Vec", [n, d]) -> (\l -> TTensor (position l SNil)) <$> tyLen env n <*> tyDim env d
        ("Mat", [m, n]) ->
          (\a b -> TTensor (position a (position b SNil)) dimOne)
            <$> tyLen env m
            <*> tyLen env n
        ("Mat", [m, n, d]) ->
          (\a b -> TTensor (position a (position b SNil)))
            <$> tyLen env m
            <*> tyLen env n
            <*> tyDim env d
        ("Tensor", [sh]) -> (`TTensor` dimOne) <$> tyShape env sh
        ("Tensor", [sh, d]) -> TTensor <$> tyShape env sh <*> tyDim env d
        -- A point and a chart take a frame (design §3.10, F4), and so do
        -- the amounts between its points and its coordinates.
        ("Point", [a]) -> TPoint <$> tyFrame env a
        ("Chart", [a]) -> TChart <$> tyFrame env a
        ("Diff", [a]) -> (`overType` Nothing) <$> tyFrame env a
        ("Coords", [a]) -> (`overType` Just dimOne) <$> tyFrame env a
        (n, _)
          | n `elem` builtinTypeNames ->
              bad t ("`" <> n <> "` does not take these arguments")
        (n, _) -> applied env t n args
  S.TyTuple ts -> tupleT <$> mapM (tyType env) ts
  S.TyList a -> listT <$> tyType env a
  S.TyFun a b -> TFun <$> tyType env a <*> tyType env b
  S.TyInt _ -> bad t "a number is a length, not a type"
  S.TyShape _ -> bad t "a bracket is a shape, not a type"
  S.TyDim _ -> bad t "a dimension is not a type: a quantity of it is Num (m/s)"
  S.TyForall _ _ -> bad t "forall goes only at the head of a signature or an ascription"

{- | A role (design §3.10, U9): @Amount@, @Unit@, or a variable of kind
role.
-}
tyRole :: DataEnv -> S.TyExpr -> Kinds Role
tyRole env a = case a.node of
  S.TyName p | Map.member p env.params -> RVar <$> useParam env a p KRole
  S.TyName "Amount" -> pure RAmount
  S.TyName "Unit" -> pure RUnit
  _ -> bad a "a role is Amount or Unit, or a variable, as in Quantity r m"

{- | A frame (design §3.10, F4): a frame variable, with its companions, or
a chart's name, which names the frame it minted, read off the chart's
type. A space, a rescaling's name or a type are refused with what to write.
-}
tyFrame :: DataEnv -> S.TyExpr -> Kinds Frame
tyFrame env a = case a.node of
  S.TyName p | Map.member p env.params -> do
    v <- useParam env a p KFrame
    pure
      ( fromMaybe
          (Frame (FrVar v) AAnon (Space (SpVar v) SNil dimOne AAnon))
          (Map.lookup p env.frames)
      )
  S.TyName n -> case namedType env n of
    Found full
      | Just (h, def) <- typeAt env full
      , Just _ <- frameDefMoving def ->
          maybe
            (bad a ("the frame `" <> n <> "` has no chart to read it from"))
            pure
            (chartFrameOf env.codebase h def)
      | Just (_, def) <- typeAt env full
      , isSpaceDef def ->
          bad
            a
            ("`" <> n <> "` is a space; a point is on a frame of it, as in Point degC")
      | otherwise -> bad a ("`" <> n <> "` is a type, not a frame")
    Ambiguous fulls -> ambiguousType a n fulls
    NotFound -> case qualifyName TermLabel env.scope env.codebase n of
      Found c
        | isChartName c env.codebase
        , Just r <- lookupName c env.codebase
        , Just (Forall _ t) <- typeOf r env.codebase
        , Just (FrNamed h) <- (.slot) <$> chartTypeFrame t ->
            bad
              a
              ( "`"
                  <> n
                  <> "` is a rescaling and shares the frame of its parent: write Point "
                  <> maybe
                    (showHash h)
                    (shortestNameOf TypeLabel env.scope env.codebase)
                    (typeNameOf h env.codebase)
              )
      _ -> bad a ("unknown frame `" <> n <> "` in a type")
  _ ->
    bad
      a
      "a point and a chart are typed by a frame, a chart's name or a variable, as in Point degC"

-- | The frame of a chart's type, after any parameters.
chartTypeFrame :: Type -> Maybe Frame
chartTypeFrame = \case
  TFun _ r -> chartTypeFrame r
  TChart f -> Just f
  _ -> Nothing

{- | A minted frame as a type (design §3.10, F3), read off the type of the
chart at its path.
-}
chartFrameOf :: Codebase -> Hash -> TypeDef -> Maybe Frame
chartFrameOf cb h def = do
  path <- mintedPath def
  r <- lookupName path cb
  Forall _ t <- typeOf r cb
  f <- chartTypeFrame t
  if f.slot == FrNamed h then Just f else Nothing

-- | A type name through the scope.
namedType :: DataEnv -> Text -> Qualified
namedType env = qualifyWith env.codebase.uses (isLabel TypeLabel env.codebase) env.scope

typeAt :: DataEnv -> Text -> Maybe (Hash, TypeDef)
typeAt env full = do
  h <- lookupTypeName full env.codebase
  (h,) <$> lookupTypeDef h env.codebase

ambiguousType :: S.TyExpr -> Text -> [Text] -> Kinds a
ambiguousType a n fulls =
  bad
    a
    ( "`"
        <> n
        <> "` is both "
        <> T.intercalate " and " (map (\f -> "`" <> f <> "`") fulls)
        <> "; write one of them"
    )

-- | A declared type, or the one being declared, applied to its arguments.
applied :: DataEnv -> S.TyExpr -> Text -> [S.TyExpr] -> Kinds Type
applied env t n args
  | resolved == Found env.self.text = do
      arity (length env.paramNames)
      kinds <- mapM (gets . Map.findWithDefault KType) env.paramNames
      TData selfType <$> argsAt env kinds args
  | Found full <- resolved
  , Just (_, def) <- typeAt env full
  , isSpaceDef def || isJust (frameDefMoving def) =
      bad
        t
        ( "`"
            <> n
            <> "` is "
            <> (if isSpaceDef def then "a space" else "a frame")
            <> ", not a type: a point on a frame is Point c, an amount along its axes Vec "
            <> n
            <> " m"
        )
  | Found full <- resolved
  , Just (h, def) <- typeAt env full = do
      let written = writtenParams def.params
      arity (length written)
      TData h <$> argsAt env (map snd written) args
  | Ambiguous fulls <- resolved = ambiguousType t n fulls
  | otherwise = bad t ("unknown type `" <> n <> "`")
 where
  -- The type's own name exists before it is entered.
  resolved =
    qualifyWith
      env.codebase.uses
      (\x -> x == env.self.text || isLabel TypeLabel env.codebase x)
      env.scope
      n
  arity k =
    when (length args /= k)
      $ bad
        t
        ( "`"
            <> n
            <> "` takes "
            <> T.pack (show k)
            <> (if k == 1 then " argument" else " arguments")
            <> ", given "
            <> T.pack (show (length args))
        )

{- | The arguments of a declared type at its written parameters' kinds:
the written arguments in order, then the companions (design §3.9,
§3.10): the axes of each length argument, then each frame argument's
axes and space.
-}
argsAt :: DataEnv -> [Kind] -> [S.TyExpr] -> Kinds [Arg]
argsAt env kinds args = do
  converted <- zipWithM (argOf env) kinds args
  pure
    ( map fst converted
        ++ [AAxis ax | (_, LenAxes ax) <- converted]
        ++ concat
          [ [ AAxis f.axes
            , ASpace f.space.slot
            , AShape f.space.shape
            , ADim f.space.dim
            , AAxis f.space.base
            ]
          | (_, FrameOf f) <- converted
          ]
    )

-- | What an argument brings with it: a length its axes, a frame itself.
data Companion = NoCompanion | LenAxes Axis | FrameOf Frame

-- | An argument at a written parameter's kind, with its companions.
argOf :: DataEnv -> Kind -> S.TyExpr -> Kinds (Arg, Companion)
argOf env k a = case k of
  KType -> (,NoCompanion) . AType <$> tyType env a
  KLen -> bimap ALen LenAxes <$> tyLen env a
  KShape -> (,NoCompanion) . AShape <$> tyShape env a
  KDim -> (,NoCompanion) . ADim <$> tyDim env a
  KFrame -> (\f -> (AFrame f.slot, FrameOf f)) <$> tyFrame env a
  KAxis -> bad a "an axis set cannot be written"
  KSpace -> bad a "a space is written as a frame's: (c : Temperature)"
  KRole -> (,NoCompanion) . ARole <$> tyRole env a

-- | A position of a shape: a length and its axes.
position :: (Len, Axis) -> Shape -> Shape
position = uncurry SCons

{- | A written length and the axes it means (design §3.9): a literal is
that many anonymous axes, a parameter a whole axis set (its length and
its companion axis parameter), and @rank s@ anonymous, as an index's
positions are numbers. A frame variable means its axes, and a space
variable its base axes, as many as its space has (design §3.10, F4).
-}
tyLen :: DataEnv -> S.TyExpr -> Kinds (Len, Axis)
tyLen env a = case a.node of
  S.TyInt k | k >= 0 -> pure (LLit (fromInteger k), AAnon)
  S.TyName p | Map.member p env.params -> do
    known <- gets (Map.lookup p)
    case known of
      Just KFrame -> do
        modify (Map.insert (vectorKey p) KLen)
        pure $ case Map.lookup p env.frames of
          Just f -> (spaceLength f.space, f.axes)
          Nothing -> (LLit 0, AAnon)
      Just KSpace -> do
        modify (Map.insert (vectorKey p) KLen)
        pure $ case Map.lookup p env.spaces of
          Just sp -> (spaceLength sp, sp.base)
          Nothing -> (LLit 0, AAnon)
      _ -> do
        v <- useParam env a p KLen
        -- A sized binder is its literal length beside its own axes.
        let len = maybe (LVar v 0) LLit (Map.lookup p env.sized)
        pure (len, maybe AAnon AVar (Map.lookup p env.axisOf))
  -- The one type-level function (design §4.1): the rank of a shape.
  S.TyApp hd [sh] | hd.text == "rank" -> (,AAnon) . rankLen <$> tyShape env sh
  S.TyName "rank" -> bad a "rank takes a shape: rank s"
  S.TyApp hd _ | hd.text == "rank" -> bad a "rank takes one shape: rank s"
  S.TyName n -> namedAxes env a n
  _ ->
    bad
      a
      "a length is a number, a parameter, a frame's or a space's axes, or rank s"

-- | The length of a space of one axis set.
spaceLength :: Space -> Len
spaceLength sp = case sp.shape of
  SCons l _ _ -> l
  _ -> LLit 0

{- | A name in a length position (design §3.10, F4): a frame's axes, as
many as its space has, or a space's base axes. @Vec lvlh m@ is a
three-vector along lvlh's axes, @Vec Inertial m@ along Inertial's base.
-}
namedAxes :: DataEnv -> S.TyExpr -> Text -> Kinds (Len, Axis)
namedAxes env a n = case namedType env n of
  Found full
    | Just (h, def) <- typeAt env full
    , Just _ <- frameDefMoving def ->
        case chartFrameOf env.codebase h def of
          Just f
            | SCons l _ SNil <- f.space.shape -> pure (l, f.axes)
          _ ->
            bad
              a
              ("the frame `" <> n <> "` has no axes: its space is not of vectors")
    | Just (h, def) <- typeAt env full
    , Just sp <- spaceOf h def ->
        case sp.shape of
          SCons l _ SNil -> pure (l, sp.base)
          _ -> bad a ("the space `" <> n <> "` has no axes: it is a space of numbers")
    | otherwise -> bad a ("`" <> n <> "` is a type, not a length or a frame's axes")
  Ambiguous fulls -> ambiguousType a n fulls
  NotFound
    | isJust (unitDim env n) ->
        bad
          a
          ( "`"
              <> n
              <> "` is a unit, not a length: a vector's length comes first, Vec 3 "
              <> n
          )
    | otherwise -> bad a ("unknown name `" <> n <> "` in a type")

tyShape :: DataEnv -> S.TyExpr -> Kinds Shape
tyShape env a = case a.node of
  S.TyShape items -> foldr position SNil <$> mapM (tyLen env) items
  S.TyName p | Map.member p env.params -> SVar <$> useParam env a p KShape
  _ -> bad a "a shape is a list of lengths like [2, 3], or a parameter"

{- | A dimension (design §4.1): a name, which is a variable when it is a
parameter and otherwise a unit, meaning its dimension (@Num km@ is @Num
m@); @1@; or a product of them with powers in parentheses, @(kg·m²/s²)@.
-}
tyDim :: DataEnv -> S.TyExpr -> Kinds Dim
tyDim env a = case a.node of
  S.TyInt 1 -> pure dimOne
  S.TyName n
    | Map.member n env.params -> dimVar <$> useParam env a n KDim
    | Just d <- unitDim env n -> pure d
    | otherwise -> bad a ("`" <> n <> "` is not a unit or a dimension variable")
  S.TyDim factors ->
    foldr dimMul dimOne
      <$> mapM (\(f, k) -> dimPow (fromInteger k) <$> tyDim env f) factors
  -- `Num (m s)` reads as an application: say how to write the product.
  S.TyApp hd args
    | Just names <- mapM nameOf args -> bad a (S.juxtaposedHint (hd.text : names))
  _ ->
    bad
      a
      "a dimension is a unit, a variable, 1, or a product of them in parentheses, like (m/s^2)"
 where
  nameOf f = case f.node of
    S.TyName n -> Just n
    _ -> Nothing

-- | The dimension of a base unit or a unit in scope, by its name.
unitDim :: DataEnv -> Text -> Maybe Dim
unitDim env n
  | Just b <- lookup n [(baseSymbol b', b') | b' <- [minBound .. maxBound]] =
      Just (dimBase b)
  | Found u <- qualifyName TermLabel env.scope env.codebase n
  , isUnitName u env.codebase
  , Just r <- lookupName u env.codebase
  , Just (Forall [] (TUnit d)) <- typeOf r env.codebase =
      Just d
  | otherwise = Nothing

{- | A type written as a search query (design §7.3): every name that is not
a built-in type, a declared type, a base unit or a unit is a variable, of
the kind its position gives it. A query headed by @forall@ is read as a
signature is ('signatureScheme'); one without stays implicit, a search
pattern.
-}
queryScheme :: S.Scope -> Codebase -> S.TyExpr -> Either ResolveError Scheme
queryScheme scope cb t = case t.node of
  S.TyForall _ _ -> fst <$> signatureScheme scope cb t
  _ -> do
    let vars = Set.toList (Set.filter isVar (Set.fromList (map (.text) (tyNames t))))
        env = emptyEnv cb scope (S.Name t.span "") vars
        preset = Map.fromList [(v, KFrame) | v <- framesNamed t, v `elem` vars]
    -- As for a declaration: kinds first, then each variable with its
    -- companions (design §3.9, §3.10).
    (_, kinds1) <- runStateT (tyType env t) preset
    let written = [(v, Map.findWithDefault KType v kinds1) | v <- vars]
        comps =
          companionsOf
            (length vars)
            written
            Map.empty
            (Set.fromList [v | v <- vars, Map.member (vectorKey v) kinds1])
            env.params
    (ty, kinds) <-
      runStateT
        ( tyType
            env
              { axisOf = comps.compAxes
              , frames = comps.compFrames
              , spaces = comps.compSpaces
              }
            t
        )
        kinds1
    pure
      ( Forall
          ( [(i, Map.findWithDefault KType v kinds) | (i, v) <- zip [0 ..] vars]
              ++ comps.compVars
          )
          ty
      )
 where
  -- Names resolve through the scope (design §7.6).
  isVar = typeVariable scope cb

-- | Every name a written type uses, with its span, in order.
tyNames :: S.TyExpr -> [S.Name]
tyNames e = case e.node of
  S.TyName n -> [S.Name e.span n]
  S.TyInt _ -> []
  S.TyApp hd args -> hd : concatMap tyNames args
  S.TyTuple ts -> concatMap tyNames ts
  S.TyList a -> tyNames a
  S.TyFun a b -> tyNames a ++ tyNames b
  S.TyShape items -> concatMap tyNames items
  S.TyDim factors -> concatMap (tyNames . fst) factors
  S.TyForall bs a -> map (.name) bs ++ [s | b <- bs, Just s <- [b.space]] ++ tyNames a

{- | The variables a @forall@ binds, by name (design §4.8): each with its
id and kind in the scheme, and its companions: for a length, its axis
variable (design §3.9) and the literal it is when the binder is sized; for
a frame its frame and for a space its space, companions and all (design
§3.10).
-}
type Bound = Map.Map Text BoundVar

data BoundVar = BoundVar
  { var :: VarId
  , kind :: Kind
  , axis :: Maybe VarId
  , size :: Maybe Int
  , frame :: Maybe Frame
  , space :: Maybe Space
  }

-- | A bound variable with every id it holds renumbered.
renumberBound :: (VarId -> VarId) -> BoundVar -> BoundVar
renumberBound f bv =
  BoundVar
    { var = f bv.var
    , kind = bv.kind
    , axis = f <$> bv.axis
    , size = bv.size
    , frame = movedFrame <$> bv.frame
    , space = movedSpace <$> bv.space
    }
 where
  moved t = substOnce (Map.fromList [(v, varArg k (f v)) | (v, k) <- freeVars t]) t
  movedFrame fr = case moved (TPoint fr) of
    TPoint fr' -> fr'
    _ -> fr
  movedSpace sp = case moved (TPoint (Frame (FrNamed selfType) AAnon sp)) of
    TPoint fr' -> fr'.space
    _ -> sp

{- | A signature's type (design §4.8, §3.9 decision 6), with the variables
its @forall@ binds. The variables are numbered in the order they first
appear, as 'canonicalScheme' numbers them, so that a signature and the
text it prints as convert to the same scheme.
-}
signatureScheme ::
  S.Scope -> Codebase -> S.TyExpr -> Either ResolveError (Scheme, Bound)
signatureScheme scope cb t = do
  (Forall _ ty, bound) <- explicitScheme scope cb Map.empty t
  let vs = freeVars ty
      renumber = Map.fromList (zip (map fst vs) [0 ..])
      moved = Map.fromList [(v, varArg k i) | ((v, k), i) <- zip vs [0 ..]]
      at v = Map.findWithDefault v v renumber
  pure
    ( Forall [(i, k) | ((_, k), i) <- zip vs [0 ..]] (substOnce moved ty)
    , Map.map (renumberBound at) bound
    )

{- | A type whose variables are bound explicitly (design §4.8, §3.9
decision 6): by its own @forall@, or, for an ascription, by the signature
of the definition it is in (the given variables, which stay free in the
scheme). Every other name is a name and resolves like one; an unknown
lowercase one is an error. A binder, or a signature's variable in an
ascription, shadows a unit, a base unit or a declared type of its name
throughout the type, dimensions included. Kinds
are learned from where the variables are used; a length variable stands
for a whole axis set, its length and a companion axis variable, and a
sized binder, @(a : 3)@, for that many axes of its own. A variable where a
frame goes is a frame, of the space its binder names, @(c : Temperature)@
or @(c : s)@, or of a space of its own (design §3.10, F1).
-}
explicitScheme ::
  S.Scope -> Codebase -> Bound -> S.TyExpr -> Either ResolveError (Scheme, Bound)
explicitScheme scope cb outer t0 = do
  let (binders, body) = case t0.node of
        S.TyForall bs b -> (bs, b)
        _ -> ([], t0)
  checkBinders Set.empty (map (.name) binders)
  let own = map (.name.text) binders
      -- Outer variables keep their ids; the type's own are numbered above them.
      base =
        1
          + maximum
            ( -1
                : concat
                  [ bv.var
                      : maybe [] pure bv.axis
                      ++ maybe [] frameIds bv.frame
                      ++ maybe [] spaceIds bv.space
                  | bv <- Map.elems outer
                  ]
            )
      ownIds = Map.fromList (zip own [base ..])
      visible = Map.withoutKeys outer (Set.fromList own)
      params = ownIds <> Map.map (.var) visible
      sizes =
        Map.fromList [(b.name.text, fromInteger k) | b <- binders, Just k <- [b.size]]
          <> Map.mapMaybe (.size) visible
      annotatedWith = [(b.name.text, s) | b <- binders, Just s <- [b.space]]
  case [ n | n <- tyNames body, Map.notMember n.text params, typeVariable scope cb n.text
       ] of
    n : _ ->
      Left
        ( DataError
            n.span
            ( "unknown name `"
                <> n.text
                <> "` in a type; bind it with forall if it is a variable"
            )
        )
    [] -> pure ()
  -- A binder's space: a declared one, or a space variable bound here.
  annotations <-
    Map.fromList
      <$> sequence
        [ (n,) <$> annotation s
        | (n, s) <- annotatedWith
        ]
  let env =
        (emptyEnv cb scope (S.Name t0.span "") (Map.keys params))
          { params = params
          , axisOf = Map.mapMaybe (.axis) visible
          , sized = sizes
          , frames = Map.mapMaybe (.frame) visible
          , spaces = Map.mapMaybe (.space) visible
          }
      known =
        Map.map (.kind) visible
          <> Map.fromList [(n, KLen) | n <- Map.keys sizes]
          <> Map.fromList [(n, KFrame) | (n, _) <- annotatedWith]
          <> Map.fromList [(s, KSpace) | Right s <- Map.elems annotations]
          <> Map.fromList [(n, KFrame) | n <- framesNamed body, n `elem` own]
  -- Kinds first, then each variable with its companions.
  (_, kinds) <- runStateT (tyType env body) known
  let used =
        [ (n, k)
        | n <- own
        , Just k <- [Map.lookup n kinds]
        ]
      vector = Set.fromList [n | n <- own, Map.member (vectorKey n) kinds]
      comps = companionsOf (base + length own) used annotations vector ownIds
      env' =
        env
          { axisOf = comps.compAxes <> env.axisOf
          , frames = comps.compFrames <> env.frames
          , spaces = comps.compSpaces <> env.spaces
          }
  (ty, _) <- runStateT (tyType env' body) kinds
  let idOf n = Map.findWithDefault 0 n ownIds
  pure
    ( Forall
        ([(idOf n, k) | (n, k) <- used, Map.notMember n sizes] ++ comps.compVars)
        ty
    , Map.fromList
        [ ( n
          , BoundVar
              (idOf n)
              k
              (Map.lookup n comps.compAxes)
              (Map.lookup n sizes)
              (Map.lookup n comps.compFrames)
              (Map.lookup n comps.compSpaces)
          )
        | (n, k) <- used
        ]
    )
 where
  annotation s
    | Just bv <- Map.lookup s.text outer
    , Just sp <- bv.space =
        Right (Left sp)
    | maybe False (isLower . fst) (T.uncons s.text) = Right (Right s.text)
    | otherwise = case qualifyWith cb.uses (isLabel TypeLabel cb) scope s.text of
        Found full
          | Just h <- lookupTypeName full cb
          , Just sp <- lookupTypeDef h cb >>= spaceOf h ->
              Right (Left sp)
        _ ->
          Left
            ( DataError
                s.span
                ( "`"
                    <> s.text
                    <> "` is not a space: a frame's binder names one, as in (c : Temperature)"
                )
            )
  frameIds f = map fst (freeVars (TPoint f))
  spaceIds sp = map fst (freeVars (TPoint (Frame (FrNamed selfType) AAnon sp)))
  checkBinders _ [] = Right ()
  checkBinders seen (n : ns)
    | not (maybe False (isLower . fst) (T.uncons n.text)) || n.text == "rank" =
        Left
          ( DataError
              n.span
              ("`" <> n.text <> "` cannot be a type variable; a variable is a lowercase name")
          )
    | Set.member n.text seen =
        Left (DataError n.span ("`" <> n.text <> "` is bound twice"))
    | otherwise = checkBinders (Set.insert n.text seen) ns
