{- | Propagating a new version to its dependents (design §7.5).

Given a map from old references to new ones, every current definition
whose term mentions an old reference is rewritten to the new one,
re-typechecked, re-hashed, stored, and its names re-bound, in dependency
order so that each dependent is rewritten once. A dependent whose rewritten
term no longer typechecks is left on the old version and reported.
-}
module Metron.Update (
  RefMap,
  ConMap,
  Propagation (..),
  propagate,
  propagateWith,
  propagateScoped,
  propagateNamed,
  Written,
  appliesTo,
  staleReferences,
  Restamped (..),
  restamp,
  restampTerm,
  retypeScheme,
  conTypes,
) where

import Data.Bifunctor ( first )
import Data.Foldable ( foldlM )
import Data.Graph ( flattenSCC, stronglyConnComp )
import Data.Map.Strict ( Map )
import Data.Maybe ( fromMaybe )
import Data.Text ( Text )
import Metron.Builtin ( axesHash )
import Metron.Codebase
    ( addTerm,
      addTypeDef,
      bindName,
      historicalNamesOf,
      lookupName,
      lookupTerm,
      lookupTypeDef,
      namesOf,
      setSignature,
      signatureOf,
      typeOf,
      writtenAs,
      Codebase(names, typeNames, conNames, fieldNames, signatures),
      Reference(hash, Reference) )
import Metron.Core
    ( conTypes,
      refsWithIndex,
      refsWritten,
      rewriteRefs,
      rewriteRefsWritten,
      showHash,
      vecMap,
      Alt(Alt),
      ConRef(..),
      Hash,
      Label(SpaceLabel, Owner, Axes, FrameLabel),
      Term(..) )
import Metron.Hash ( hashTerm, hashTypeDef )
import Metron.Infer ( elaborateClosed, TypeError(message) )
import Metron.Resolve ( storeTerm, typeLookupFor )
import Metron.Type
    ( Arg(..),
      Axis(..),
      Frame(..),
      FrameSlot(..),
      Scheme(..),
      Shape(..),
      Space(..),
      SpaceSlot(..),
      Type(..),
      TypeDef(..),
      renderScheme )
import Metron.Type.Match ( signatureHolds )
import Data.Map.Strict qualified as Map
    ( null,
      elems,
      empty,
      keys,
      lookup,
      toList,
      findWithDefault,
      fromList,
      insert,
      map,
      mapWithKey )
import Data.Set qualified as Set
    ( Set,
      member,
      union,
      difference,
      disjoint,
      fromList,
      null,
      toList )

type RefMap = Map Reference Reference

data Propagation = Propagation
  { codebase :: Codebase
  , upgraded :: [(Text, Reference, Reference)]
  -- ^ name, old, new
  , skipped :: [(Text, Reference, Text)]
  -- ^ name, its current ref, why it stayed
  }

-- | Constructors of replaced declared types: the old type and position to the new.
type ConMap = Map (Hash, Int) (Hash, Int)

propagate :: RefMap -> Codebase -> Propagation
propagate = propagateWith Map.empty

{- | 'propagate', also moving every current definition that builds or
matches a constructor of a replaced type to the new type's constructor
(design §7.3, @:edit@ of a type). One that no longer checks, as when the
constructor gained a field, is left on its version and reported.
-}

{- | The names each old reference is being rebound under: a dependent follows
the rebinding only through a reference written under one of them (design
§7.5). A reference written under no name (a format-1 term) always follows.
-}
type Written = Map Reference (Set.Set Text)

appliesTo :: Codebase -> Written -> Reference -> Text -> Bool
appliesTo cb written r w = maybe True (any (writtenAs cb w)) (Map.lookup r written)

{- | Propagation that follows rebindings only through the names they were
made under.
-}
propagateNamed :: Written -> RefMap -> Codebase -> Propagation
propagateNamed written refmap cb = propagateScoped (appliesTo cb written) Map.empty refmap cb

-- | By hash alone, every written name included: for re-stamping.
propagateWith :: ConMap -> RefMap -> Codebase -> Propagation
propagateWith = propagateScoped (\_ _ -> True)

propagateScoped ::
  (Reference -> Text -> Bool) -> ConMap -> RefMap -> Codebase -> Propagation
propagateScoped applies cons initial cb0 = go cb0 initial (Propagation cb0 [] []) affectedInOrder
 where
  initialHashes = Set.fromList (map (.hash) (Map.keys initial))
  oldTypes = Set.fromList (map fst (Map.keys cons))
  conUsers =
    Set.fromList
      [ h
      | not (Set.null oldTypes)
      , Reference h _ <- Map.elems cb0.names
      , Just t <- [lookupTerm h cb0]
      , not (Set.disjoint oldTypes (conTypes t))
      ]
  newCon = \case
    UserCon h i | Just (h', i') <- Map.lookup (h, i) cons -> UserCon h' i'
    c -> c

  -- Hashes of current definitions that mention an old reference or an old
  -- constructor, directly or through another affected definition.
  affected = Set.difference (closure (Set.union initialHashes conUsers)) initialHashes
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
  mentionsAny olds t =
    any
      (\(h, i, w) -> h `Set.member` olds && applies (Reference h i) w)
      (Set.toList (refsWritten t))

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

  -- Replaced types, old hash to new: a signature that names an old type
  -- follows it to the new one (design §4.8).
  typeMap = Map.fromList [(h, h') | ((h, _), (h', _)) <- Map.toList cons]
  retyped = retypeScheme typeMap
  -- Every other signature follows too where it holds of its name's
  -- definition; one on a name left on the old type keeps naming it.
  followSignatures cb
    | Map.null typeMap = cb
    | otherwise = cb{signatures = Map.mapWithKey follow cb.signatures}
   where
    follow n sig = case lookupName n cb >>= (`typeOf` cb) of
      Just general | signatureHolds (retyped sig) general -> retyped sig
      _ -> sig

  go cb _ acc [] =
    acc
      { codebase = followSignatures cb
      , upgraded = reverse acc.upgraded
      , skipped = reverse acc.skipped
      }
  go cb refmap acc (h : hs) = case lookupTerm h cb of
    Nothing -> go cb refmap acc hs
    Just t ->
      let t' =
            rewriteRefsWritten
              ( \rh ri w ->
                  if applies (Reference rh ri) w
                    then (\(Reference nh ni) -> (nh, ni)) <$> Map.lookup (Reference rh ri) refmap
                    else Nothing
              )
              (restampTerm id newCon t)
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
            -- A signed name stays on its version when its signature would not
            -- hold of the new one (design §4.8).
            Right (schemes, _)
              | (n, sig, general) : _ <-
                  [ (n, sig, general)
                  | (n, i) <- holders
                  , Just sig <- [retyped <$> signatureOf n cb]
                  , general : _ <- [drop (fromMaybe 0 i) schemes]
                  , not (signatureHolds sig general)
                  ] ->
                  go
                    cb
                    refmap
                    acc
                      { skipped =
                          [ ( m
                            , Reference h i
                            , "the new version of `"
                                <> n
                                <> "` has type "
                                <> renderScheme general
                                <> ", not as general as its signature "
                                <> renderScheme sig
                            )
                          | (m, i) <- holders
                          ]
                            ++ acc.skipped
                      }
                    hs
            Right (schemes, typed) ->
              let h' = hashTerm t'
                  renamed = [(n, Reference h i, Reference h' i) | (n, i) <- holders]
                  refmap' = foldr (\(_, old, new) -> Map.insert old new) refmap renamed
                  -- The signature, retyped, holds of the new version: set it
                  -- first, so that the rebinding keeps it.
                  rebind (n, _, new) acc' =
                    bindName
                      n
                      new
                      (maybe acc' (\s -> setSignature n (retyped s) acc') (signatureOf n acc'))
                  cb' = foldr rebind (addTerm h' t' schemes typed cb) renamed
               in go cb' refmap' acc{upgraded = reverse renamed ++ acc.upgraded} hs

-- | A type with declared types replaced, old hash to new.
retypeType :: Map Hash Hash -> Type -> Type
retypeType m = \case
  TData h as -> TData (new h) (map arg as)
  TFun a b -> TFun (retypeType m a) (retypeType m b)
  -- A chart's axes are a declared type's (design §3.9): a named slot
  -- follows it too.
  TQty r sh d -> TQty r (shape sh) d
  TPoint f -> TPoint (frame f)
  TChart f -> TChart (frame f)
  TOver f md -> TOver (frame f) md
  t -> t
 where
  new h = Map.findWithDefault h h m
  arg = \case
    AType t -> AType (retypeType m t)
    AShape sh -> AShape (shape sh)
    AAxis a -> AAxis (axis a)
    AFrame (FrNamed h) -> AFrame (FrNamed (new h))
    ASpace (SpNamed h) -> ASpace (SpNamed (new h))
    a -> a
  -- A frame and a space are declared types too (design §3.10).
  frame f =
    Frame
      (case f.slot of FrNamed h -> FrNamed (new h); s -> s)
      (axis f.axes)
      (space f.space)
  space sp =
    Space
      (case sp.slot of SpNamed h -> SpNamed (new h); s -> s)
      (shape sp.shape)
      sp.dim
      (axis sp.base)
  shape = \case
    SCons l a rest -> SCons l (axis a) (shape rest)
    sh -> sh
  axis = \case
    ANamed h -> ANamed (new h)
    a -> a

-- | 'retypeType' on a scheme, such as a signature (design §4.8).
retypeScheme :: Map Hash Hash -> Scheme -> Scheme
retypeScheme m (Forall vs t) = Forall vs (retypeType m t)

{- | References in current definitions that a name once pointed at but no
longer does, with nothing else naming them: the work `:upgrade` would do.
Each entry is (dependent, stale reference, the name that moved on).
-}
staleReferences :: Codebase -> [(Text, Reference, Text)]
staleReferences cb =
  [ (n, r, m)
  | (n, Reference h _) <- Map.toList cb.names
  , Just t <- [lookupTerm h cb]
  , (rh, ri, w) <- Set.toList (refsWritten t)
  , let r = Reference rh ri
  , null (namesOf r cb)
  , m <- historicalNamesOf r cb
  , writtenAs cb w m
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
    -- A chart's minted axis type follows its chart (design §3.9).
    Axes o | Just n <- Map.lookup o owners -> Axes n
    -- So do its frame, and a space its base axes (design §3.10).
    FrameLabel o moving | Just n <- Map.lookup o owners -> FrameLabel n moving
    SpaceLabel o | Just n <- Map.lookup o owners -> SpaceLabel n
    l -> l

  -- Types: re-stamped, and their users rewritten, until nothing changes.
  -- Declared types do not refer to each other in cycles, so this ends.
  -- A scalar chart's axes are unnamed, and follow the chart (design §3.9).
  named =
    Set.toList
      (Set.fromList (Map.elems cb0.typeNames ++ [axesHash o | (o, _) <- moves]))
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
      , -- A signature names re-hashed types by their new hashes (design §4.8).
        signatures = Map.map (retypeScheme typeMap) cb0.signatures
      }
  retype = retypeType
  constructor = \case
    UserCon h i -> UserCon (newType h) i

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
