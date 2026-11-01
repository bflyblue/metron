{- | Binding groups (design §2.2, §6.2, §6.3, §7.1): dependency analysis,
cycle construction and hashing, type inference, and entry into the
codebase. Nothing from a group is stored unless the whole group checks.
-}
module Metron.Resolve (
  typeLookupFor,
  processGroup,
  annotationsWith,
  ascriptionsIn,
  storeTerm,
  withHint,
) where

import Control.Monad.State.Strict
    ( StateT(runStateT), MonadTrans(lift), gets, modify )
import Data.Foldable ( foldlM )
import Data.Graph ( SCC(..), stronglyConnComp )
import Data.List ( sortOn )
import Data.Maybe ( fromMaybe, isJust, isNothing )
import Data.Set ( Set )
import Data.Text ( Text )
import Metron.Builtin ( axesDef, boolT, frameDef, frameDefMoving )
import Metron.Check
    ( checkCore,
      CheckError(CoreLintError, InferenceError),
      CheckedCore(typed, linted) )
import Metron.Codebase
    ( addTerm,
      addTypeDef,
      bindName,
      bindTypeName,
      clearFlags,
      lookupName,
      lookupTypeDef,
      lookupTypeName,
      lookupTypes,
      markChart,
      markUnit,
      setSignature,
      signatureOf,
      typeOf,
      Codebase(signatures, typeNames, uses),
      Reference(Reference) )
import Metron.Core
    ( conTypes,
      refsWritten,
      vecAppend,
      vecFromList,
      vecMap,
      vecToList,
      vecTraverse,
      Hash,
      Hint(Hint),
      Nat(Z),
      SomeVec(SomeVec),
      Term(PrimApp, Cycle),
      Vec(..) )
import Metron.Desugar
    ( desugarDefinition,
      desugarMarked,
      fillOperands,
      provenanceAt,
      Provenance(ascriptions) )
import Metron.Hash ( hashTypeDef, hashTerm, placeholderHash )
import Metron.Infer
    ( TypeLookup,
      elaborateClosedWith,
      hasReadingMarkers,
      noAnnotations,
      readingsOf,
      rewriteReadings,
      Annotations(signatureFor, Annotations),
      TypeError(message, path) )
import Metron.NameResolution
    ( disjointness,
      groupResolver,
      isLabel,
      qualifyWith,
      LabelKind(..),
      Qualified(..) )
import Metron.Resolve.Error ( ResolveError(..) )
import Metron.Type
    ( substOnce,
      varArg,
      Scheme(..),
      Type,
      TypeDef,
      TypeLookup(TypeLookup),
      defaultAxes,
      renderScheme,
      withBuiltins )
import Metron.Type.Match ( signatureHolds )
import Metron.Type.Syntax
    ( enterData,
      enterSpace,
      explicitScheme,
      renumberBound,
      signatureScheme,
      tyNames,
      Bound )
import Metron.Desugar qualified as D
    ( ascriptionPath,
      desugarMarked,
      desugarMember,
      signatureMarker,
      Path )
import Data.Map.Strict qualified as Map
    ( null,
      delete,
      Map,
      empty,
      keysSet,
      lookup,
      toList,
      union,
      fromList,
      insert,
      map )
import Metron.Syntax qualified as S
    ( declKey,
      isSignature,
      BindKind(..),
      Binding(name, kind, body, span, params),
      ChartClauses(spin, parent, origin, step, generators),
      DataDecl(constructors, name),
      Decl(..),
      Expr(..),
      FieldDecl(FieldDecl),
      Name(..),
      Node(UnitSyntax, Num, Labelled, Tuple, List, CaseOf, Bool, Var,
           Lam, App, Let, If, BinOp, Neg, Pow, SectionL, SectionR, Vec, Proj,
           Slice, FieldOf, Record, Ascribe, ChartForm, FromTo, UnitBody),
      Op(Infix),
      PatNode(PWild, PCon, PVar),
      Pattern(node),
      Pos(Pos),
      Scope,
      Span(Span) )
import Data.Set qualified as Set
    ( member,
      notMember,
      empty,
      fromList,
      insert,
      intersection,
      null,
      singleton,
      toList )
import Data.Text qualified as T ( intercalate, pack )

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
    checkedCore <- either (Left . \case
      InferenceError err -> typeErrorIn b prov err
      CoreLintError err -> LintFailure b.name err) Right (checkCore noAnnotations (typeLookupFor cb) term)
    let typed = checkedCore.typed
        linted = checkedCore.linted

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
        stored = linted
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
      checkedCore <-
        either
          (Left . \case
            InferenceError err -> cycleTypeError sorted provs err
            CoreLintError err -> LintFailure (headName sorted) err)
          Right
          (checkCore noAnnotations (typeLookupFor cbm) cycleTerm)
      let typed = checkedCore.typed
          linted = checkedCore.linted
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
      let stored = linted
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
    S.UnitSyntax a -> go bound a
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
  checked <- either (Left . message) Right (checkCore noAnnotations (typeLookupFor cb) term)
  pure (addTerm h term checked.linted checked.typed cb)
 where
  message (InferenceError err) = err.message
  message (CoreLintError err) = err

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
