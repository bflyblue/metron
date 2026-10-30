{- | Propagating a new version to its dependents (design §7.5).

Given a map from old references to new ones, every current definition
whose term mentions an old reference is rewritten to the new one,
re-typechecked, re-hashed, stored, and its names re-bound, in dependency
order so that each dependent is rewritten once. A dependent whose rewritten
term no longer typechecks is left on the old version and reported.
-}
module Eval.Update (
  RefMap,
  Propagation (..),
  propagate,
  staleReferences,
  Restamped (..),
  restamp,
) where

import Data.Bifunctor (first)
import Data.Foldable (foldlM)
import Data.Graph (flattenSCC, stronglyConnComp)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Eval.Codebase
import Eval.Core
import Eval.Hash (hashTerm, hashTypeDef)
import Eval.Infer
import Eval.Resolve (storeTerm, typeLookupFor)
import Eval.Type (Arg (..), Type (..), TypeDef (..))

type RefMap = Map Reference Reference

data Propagation = Propagation
  { codebase :: Codebase
  , upgraded :: [(Text, Reference, Reference)]
  -- ^ name, old, new
  , skipped :: [(Text, Reference, Text)]
  -- ^ name, its current ref, why it stayed
  }

propagate :: RefMap -> Codebase -> Propagation
propagate initial cb0 = go cb0 initial (Propagation cb0 [] []) affectedInOrder
 where
  initialHashes = Set.fromList (map (.hash) (Map.keys initial))

  -- Hashes of current definitions that mention an old reference, directly
  -- or through another affected definition.
  affected = Set.difference (closure initialHashes) initialHashes
  closure olds =
    let hs =
          Set.fromList
            [ h
            | Reference h _ <- Map.elems cb0.names
            , Just t <- [lookupTerm h cb0]
            , mentionsAny olds t
            ]
        olds' = Set.union olds hs
     in if olds' == olds then olds else closure olds'
  mentionsAny olds t = any (\(h, _) -> h `Set.member` olds) (Set.toList (refsWithIndex t))

  -- Dependencies first.
  affectedInOrder =
    concatMap
      flattenSCC
      ( stronglyConnComp
          [ ( h
            , h
            , [d | (d, _) <- Set.toList (refsWithIndex t), d `Set.member` affected, d /= h]
            )
          | h <- Set.toList affected
          , Just t <- [lookupTerm h cb0]
          ]
      )

  go cb _ acc [] =
    acc
      { codebase = cb
      , upgraded = reverse acc.upgraded
      , skipped = reverse acc.skipped
      }
  go cb refmap acc (h : hs) = case lookupTerm h cb of
    Nothing -> go cb refmap acc hs
    Just t ->
      let t' =
            rewriteRefs
              ( \rh ri -> (\(Reference nh ni) -> (nh, ni)) <$> Map.lookup (Reference rh ri) refmap
              )
              t
          holders = [(n, i) | (n, Reference rh i) <- Map.toList cb.names, rh == h]
       in case elaborateClosed (typeLookupFor cb) t' of
            Left err ->
              go
                cb
                refmap
                acc
                  { skipped = [(n, Reference h i, err.message) | (n, i) <- holders] ++ acc.skipped
                  }
                hs
            Right (schemes, typed) ->
              let h' = hashTerm t'
                  renamed = [(n, Reference h i, Reference h' i) | (n, i) <- holders]
                  refmap' = foldr (\(_, old, new) -> Map.insert old new) refmap renamed
                  rebind (n, _, new) = bindName n new
                  cb' = foldr rebind (addTerm h' t' schemes typed cb) renamed
               in go cb' refmap' acc{upgraded = reverse renamed ++ acc.upgraded} hs

{- | References in current definitions that a name once pointed at but no
longer does, with nothing else naming them: the work `:upgrade` would do.
Each entry is (dependent, stale reference, the name that moved on).
-}
staleReferences :: Codebase -> [(Text, Reference, Text)]
staleReferences cb =
  [ (n, r, m)
  | (n, Reference h _) <- Map.toList cb.names
  , Just t <- [lookupTerm h cb]
  , (rh, ri) <- Set.toList (refsWithIndex t)
  , let r = Reference rh ri
  , null (namesOf r cb)
  , m <- historicalNamesOf r cb
  ]

-- | What re-stamping after a relabelling did (design §7.2).
data Restamped = Restamped
  { codebase :: Codebase
  , terms :: [(Text, Reference, Reference)]
  -- ^ every current name that moved to a new hash: name, old, new
  , types :: [(Text, Hash, Hash)]
  -- ^ every type name that moved to a new hash
  }

{- | Re-stamp after a relabelling (design §3.2.4, §7.2). An owner stamp is a
full path, so when labels move (each old full path to its new one, already
relabelled in the codebase), a definition whose @±@ is stamped with an old
path, and a nominal type stamped with one, are stamped with the new path
and so re-hashed. Then every type that mentions a re-hashed type, and every
current definition that mentions a re-hashed type's constructors or a
re-hashed definition, is rewritten to the new hashes, dependencies first,
checked again and re-bound, as propagation does. Labels on the old hashes
follow them, so a cycle's other members and the type's constructors and
fields move too. All or nothing: a definition that no longer checks
refuses the change. Nothing to re-stamp gives the codebase back as it was.
-}
restamp :: [(Text, Text)] -> Codebase -> Either Text Restamped
restamp moves cb0 = do
  (cb, termMap) <- foldlM step (withTypes, Map.empty) inOrder
  let moved =
        [ (n, Reference h i, Reference h' i)
        | (n, Reference h i) <- Map.toList cb.names
        , Just h' <- [Map.lookup h termMap]
        ]
      rebound = foldl (\acc (n, _, new) -> bindName n new acc) cb moved
  pure
    Restamped
      { codebase = rebound
      , terms = moved
      , types =
          [ (n, h, h')
          | (n, h) <- Map.toList cb0.typeNames
          , Just h' <- [Map.lookup h typeMap]
          ]
      }
 where
  owners = Map.fromList moves
  relabelled = \case
    Owner o | Just n <- Map.lookup o owners -> Owner n
    l -> l

  -- Types: re-stamped, and their users rewritten, until nothing changes.
  -- Declared types do not refer to each other in cycles, so this ends.
  named = Set.toList (Set.fromList (Map.elems cb0.typeNames))
  changedTypes m =
    Map.fromList
      [ (h, (hashTypeDef def', def'))
      | h <- named
      , Just def <- [lookupTypeDef h cb0]
      , let def' =
              def
                { label = relabelled def.label
                , constructors = map (map (retype m)) def.constructors
                }
      , hashTypeDef def' /= h
      ]
  settle m = let m' = Map.map fst (changedTypes m) in if m' == m then m else settle m'
  typeMap = settle Map.empty
  newType h = Map.findWithDefault h h typeMap
  withTypes =
    ( foldl
        (\acc (h', def') -> addTypeDef h' def' acc)
        cb0
        (Map.elems (changedTypes typeMap))
    )
      { typeNames = Map.map newType cb0.typeNames
      , conNames = Map.map (first newType) cb0.conNames
      , fieldNames = Map.map (\(h, i, j) -> (newType h, i, j)) cb0.fieldNames
      }
  retype m = \case
    TData h as -> TData (Map.findWithDefault h h m) (map (argType m) as)
    TTuple ts -> TTuple (map (retype m) ts)
    TList t -> TList (retype m t)
    TFun a b -> TFun (retype m a) (retype m b)
    t -> t
  argType m = \case
    AType t -> AType (retype m t)
    a -> a
  constructor = \case
    UserCon h i -> UserCon (newType h) i
    c -> c

  -- Terms: every current definition, dependencies first.
  current = Set.fromList [h | Reference h _ <- Map.elems cb0.names]
  inOrder =
    concatMap
      flattenSCC
      ( stronglyConnComp
          [ ( h
            , h
            , [d | (d, _) <- Set.toList (refsWithIndex t), Set.member d current, d /= h]
            )
          | h <- Set.toList current
          , Just t <- [lookupTerm h cb0]
          ]
      )
  step (cb, termMap) h = case lookupTerm h cb0 of
    Nothing -> Right (cb, termMap)
    Just t ->
      let t' =
            rewriteRefs
              (\rh ri -> (,ri) <$> Map.lookup rh termMap)
              (restampTerm relabelled constructor t)
          h' = hashTerm t'
       in if h' == h
            then Right (cb, termMap)
            else case storeTerm h' t' cb of
              Left err ->
                Left
                  ( "`"
                      <> fromMaybe (showHash h) (firstName h)
                      <> "` would not check under its new stamp ("
                      <> err
                      <> "); nothing was changed"
                  )
              Right cb' -> Right (cb', Map.insert h h' termMap)
  firstName h = case [n | (n, Reference h' _) <- Map.toList cb0.names, h' == h] of
    n : _ -> Just n
    [] -> Nothing

-- | A term with its owner stamps and its declared constructors mapped.
restampTerm :: (Label -> Label) -> (ConRef -> ConRef) -> Term n -> Term n
restampTerm lab con = go
 where
  go :: Term m -> Term m
  go = \case
    Var i -> Var i
    Ref h i hint -> Ref h i hint
    PrimApp p as -> PrimApp p (map go as)
    Lit l -> Lit l
    Lam h b -> Lam h (go b)
    App a b -> App (go a) (go b)
    Let h e b -> Let h (go e) (go b)
    Con c as -> Con (con c) (map go as)
    Case s alts -> Case (go s) (map (\(Alt c hs b) -> Alt (con c) hs (go b)) alts)
    Pow t n -> Pow (go t) n
    Noise k l n -> Noise k (lab l) n
    Uncertain k l x e -> Uncertain k (lab l) (go x) (go e)
    Pack ts -> Pack (map go ts)
    Proj t i -> Proj (go t) i
    Cycle hs bs -> Cycle hs (vecMap go bs)
