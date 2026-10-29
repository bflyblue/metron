{- | Binding groups (design §2.2, §6.2, §6.3, §7.1): dependency analysis,
cycle construction and hashing, type inference, and entry into the
codebase. Nothing from a group is stored unless the whole group checks.
-}
module Eval.Resolve (
  ResolveError (..),
  renderResolveError,
  resolverFor,
  typeLookupFor,
  processGroup,
  storeTerm,
) where

import Data.Foldable (foldlM)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Codebase
import Eval.Core
import Eval.Desugar
import Eval.Desugar qualified as D
import Eval.Hash
import Eval.Infer
import Eval.Syntax qualified as S
import Eval.TCore (lintClosed)
import Eval.Type (Scheme)

data ResolveError
  = DuplicateDefinition S.Name
  | Desugar DesugarError
  | {- | A type error in the named definition, at a span when provenance
    could place it.
    -}
    TypeErrorIn S.Name (Maybe S.Span) Text
  | -- | Elaboration produced ill-typed Typed Core: an internal error.
    LintFailure S.Name Text
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
      (maybe n.span id sp)
      ("in `" <> n.text <> "`: " <> msg)
  LintFailure n msg ->
    "internal error: elaboration of `"
      <> n.text
      <> "` produced ill-typed core: "
      <> msg

-- | Free names resolve to whatever the codebase currently binds.
resolverFor :: Codebase -> Resolver
resolverFor cb n =
  (\r@(Reference h i) -> Resolution (h, i) (isUnitRef r cb)) <$> lookupName n cb

typeLookupFor :: Codebase -> TypeLookup
typeLookupFor cb h = lookupTypes h cb

{- | Enter a binding group into the codebase. Statements may refer to each
other in any order; strongly connected components are hashed as cycles.
Components are processed dependencies-first, so a reference from one
component to another always sees the new hash and its type.
-}
processGroup :: Codebase -> [S.Binding] -> Either ResolveError Codebase
processGroup cb0 bindings = do
  checkDuplicates bindings
  let groupNames = Set.fromList (map (.name.text) bindings)
      nodes =
        [ ( b
          , b.name.text
          , Set.toList (Set.intersection groupNames (freeNames (asLambda b)))
          )
        | b <- bindings
        ]
  foldlM enterComponent cb0 (stronglyConnComp nodes)

checkDuplicates :: [S.Binding] -> Either ResolveError ()
checkDuplicates = go Set.empty
 where
  go _ [] = Right ()
  go seen (b : bs)
    | b.name.text `Set.member` seen = Left (DuplicateDefinition b.name)
    | otherwise = go (Set.insert b.name.text seen) bs

asLambda :: S.Binding -> S.Expr
asLambda b = case b.params of
  [] -> b.body
  _ -> S.Expr b.span (S.Lam b.params b.body)

enterComponent :: Codebase -> SCC S.Binding -> Either ResolveError Codebase
enterComponent cb = \case
  AcyclicSCC b -> do
    (term, prov) <-
      either
        (Left . Desugar)
        Right
        (desugarDefinition b.name.text (resolverFor cb) (asLambda b))
    (schemes, typed) <-
      either
        (Left . typeErrorIn b prov)
        Right
        (elaborateClosed (typeLookupFor cb) term)
    linted <-
      either (Left . LintFailure b.name) Right (lintClosed (typeLookupFor cb) typed)
    let h = hashTerm term
        ref = Reference h Nothing
        cb' =
          bindName b.name.text ref (addTerm h term (preferLint schemes linted) typed cb)
    pure (if b.isUnit then markUnit ref cb' else cb')
  CyclicSCC bs -> enterCycle cb bs

-- | Inference and lint must agree; lint is the authority if they ever differ.
preferLint :: [Scheme] -> [Scheme] -> [Scheme]
preferLint _ linted = linted

typeErrorIn :: S.Binding -> Provenance -> TypeError -> ResolveError
typeErrorIn b prov err = TypeErrorIn b.name (Map.lookup err.path prov) err.message

{- | Design §6.2. The members are first desugared in their input order to
compute ordering hashes with the cycle variables as placeholders, then
desugared again in the resulting order to build the stored 'Cycle'.
-}
enterCycle :: Codebase -> [S.Binding] -> Either ResolveError Codebase
enterCycle cb bs = do
  ordering <- mapM (\b -> (,b) <$> placeholderHashOf bs b) bs
  let sorted = map snd (sortOn fst ordering)
  case vecFromList sorted of
    SomeVec members -> do
      let ctx = vecAppend (vecMap (.name.text) members) VNil
      desugared <- vecTraverse (desugarOne ctx) members
      let bodies = vecMap fst desugared
          provs = vecToList (vecMap snd desugared)
          cycleTerm = Cycle (vecMap (Hint . (.name.text)) members) bodies
          h = hashTerm cycleTerm
      (schemes, typed) <-
        either
          (Left . cycleTypeError sorted provs)
          Right
          (elaborateClosed (typeLookupFor cb) cycleTerm)
      linted <-
        either
          (Left . LintFailure (headName sorted))
          Right
          (lintClosed (typeLookupFor cb) typed)
      let cb' = addTerm h cycleTerm (preferLint schemes linted) typed cb
          bindMember acc (i, b) =
            let ref = Reference h (Just i)
                acc' = bindName b.name.text ref acc
             in if b.isUnit then markUnit ref acc' else acc'
      pure (foldl bindMember cb' (zip [0 ..] sorted))
 where
  desugarOne ::
    Vec k Text -> S.Binding -> Either ResolveError (Term k, Provenance)
  desugarOne ctx b =
    either
      (Left . Desugar)
      Right
      (D.desugarMember b.name.text (resolverFor cb) ctx (asLambda b))

  placeholderHashOf :: [S.Binding] -> S.Binding -> Either ResolveError Hash
  placeholderHashOf group b = case vecFromList (map (.name.text) group) of
    SomeVec ns -> do
      (t, _) <- desugarOne (vecAppend ns VNil) b
      pure (placeholderHash t)

  -- Inside a cycle the error path starts with the member index.
  cycleTypeError sorted provs err = case err.path of
    i : rest
      | Just b <- nth i sorted
      , Just prov <- nth i provs ->
          TypeErrorIn b.name (Map.lookup rest prov) err.message
    _ -> TypeErrorIn (headName sorted) Nothing err.message
  nth i xs = case drop i xs of
    x : _ | i >= 0 -> Just x
    _ -> Nothing
  headName = \case
    b : _ -> b.name
    [] -> S.Name (S.Span (S.Pos 1 1) (S.Pos 1 1)) "?"

-- | Names an expression mentions that are not bound inside it.
freeNames :: S.Expr -> Set Text
freeNames = go Set.empty
 where
  go bound e = case e.node of
    S.Num _ -> Set.empty
    S.Labelled _ a -> go bound a
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
  opNames = \case
    S.Infix n -> Set.singleton n
    _ -> Set.empty

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
