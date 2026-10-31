-- | Plan and reconcile source edits atomically against a session codebase.
module Eval.Edit (
  EditScope (..),
  EditRequest (..),
  editRequest,
  editScopeArgs,
  editorNote,
  applyEdit,
) where

import Control.Monad ( when )
import Data.Bifunctor ( first )
import Data.Either ( fromRight )
import Data.List ( partition )
import Data.Maybe ( isJust, isNothing )
import Data.Text ( Text )
import Eval.Codebase
    ( dropSignature,
      isChartName,
      isUnitName,
      lookupConName,
      lookupFieldName,
      lookupName,
      lookupTerm,
      lookupTypeDef,
      lookupTypeName,
      showReference,
      signatureOf,
      unbindName,
      Codebase(names, units, charts, conNames, fieldNames, typeNames,
               signatures),
      Reference(hash, Reference) )
import Eval.Compile ( renderResolveErrorWith )
import Eval.Core ( rewriteRefsWritten, ConRef(UserCon) )
import Eval.Hash ( hashTerm )
import Eval.Parser ( parseProgram )
import Eval.Prelude ( isLibraryPath )
import Eval.Resolve.Error ( renderResolveError )
import Eval.NameResolution ( isLabel, shortestName, shortestNameOf, LabelKind(..) )
import Eval.Resolve ( processGroup )
import Eval.Session.Names ( argPath, namespaceArg )
import Eval.Session.Preferences ( refreshPreferences )
import Eval.Session.Types
    ( Session(config, codebase, scratch, staging, scope) )
import Eval.Source
    ( editSource,
      exportLabels,
      exportSource,
      nameTypes,
      spellingOf,
      upgradeReport )
import Eval.Type ( TypeDef(constructors), typeRefs )
import Eval.Update
    ( appliesTo,
      propagateScoped,
      restampTerm,
      retypeScheme,
      staleReferences,
      Propagation(codebase) )
import Data.Map.Strict qualified as Map
    ( delete,
      empty,
      keys,
      keysSet,
      lookup,
      member,
      toList,
      fromList,
      fromListWith )
import Eval.Syntax qualified as S
    ( flatten,
      renderSpanError,
      rootScope,
      BindKind(ChartDecl),
      Binding(name, kind),
      DataDecl(name, constructors),
      Decl(..),
      Expr(span),
      FieldDecl(FieldDecl),
      Name(text, span),
      Scope(namespace) )
import Data.Set qualified as Set
    ( member, notMember, union, delete, fromList, singleton, toList )
import Data.Text qualified as T
    ( isPrefixOf, null, unlines, unpack )

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
          | isChartName n c = "chart"
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
  -- A chart labels its frame too (design §3.10, F3).
  S.DBind _ b ->
    (TermLabel, b.name.text) : [(TypeLabel, b.name.text) | b.kind == S.ChartDecl]
  S.DData _ d ->
    (TypeLabel, d.name.text)
      : [(TermLabel, c.text) | (c, _) <- d.constructors]
      ++ [(FieldLabel, n.text) | (_, fs) <- d.constructors, S.FieldDecl (Just n) _ <- fs]
  -- A signature labels nothing: it belongs to its definition (design §4.8).
  S.DSig{} -> []
  -- A space labels its type (design §3.10, F2).
  S.DSpace _ n _ -> [(TypeLabel, n.text)]

-- | Remove one label of one kind; history keeps a definition's.
removeKind :: (LabelKind, Text) -> Codebase -> Codebase
removeKind (k, n) cb = case k of
  TermLabel ->
    cb
      { names = Map.delete n cb.names
      , units = Set.delete n cb.units
      , charts = Set.delete n cb.charts
      , conNames = Map.delete n cb.conNames
      , signatures = Map.delete n cb.signatures
      }
  TypeLabel -> cb{typeNames = Map.delete n cb.typeNames}
  FieldLabel -> unbindName ("." <> n) cb
