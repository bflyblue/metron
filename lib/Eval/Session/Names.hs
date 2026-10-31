-- | Resolve command arguments and manipulate labels consistently across session operations.
module Eval.Session.Names (
  argPath,
  argPaths,
  namespaceArg,
  namespaceLine,
  labelsText,
  labelNoun,
  labelKinds,
  removeLabel,
  relabel,
) where

import Data.List ( sortOn )
import Data.Text ( Text )
import Eval.Codebase
    ( bindConName,
      bindFieldName,
      bindName,
      bindTypeName,
      isChartName,
      isUnitName,
      lookupConName,
      lookupFieldName,
      lookupName,
      lookupTypeName,
      markChart,
      markUnit,
      setSignature,
      signatureOf,
      unbindName,
      Codebase(uses, names, conNames, typeNames, fieldNames, history) )
import Eval.NameResolution ( disjointness, isLabel, isNamespace, qualifyWith, LabelKind(..), Qualified(NotFound, Found, Ambiguous) )
import Eval.Session.Types ( Session(scope, codebase) )
import Data.Map.Strict qualified as Map ( member )
import Eval.Syntax qualified as S
    ( qualify, Pos(Pos), Scope(namespace), Span(Span) )
import Data.Text qualified as T ( intercalate, stripPrefix, pack )

{- | A name given to a command: relative to the current namespace, through
the uses, or absolute with a leading dot (design §7.6).
-}
argPath :: S.Scope -> Codebase -> Text -> Text
argPath scope c n = case argPaths scope c n of
  [full] -> full
  _ -> n

{- | Every full path a name given to a command may mean: one, or, when the
uses offer it as several (a type in one namespace and a term in another,
@time.TT@ and @si.TT@, or two terms), each of them, types first and then by
path. A name that nothing offers is itself.
-}
argPaths :: S.Scope -> Codebase -> Text -> [Text]
argPaths scope c n
  | Just p <- T.stripPrefix "." n = [p]
  | otherwise = case qualifyWith c.uses known scope n of
      Found full -> [full]
      Ambiguous fulls -> sortOn (\p -> (not (isLabel TypeLabel c p), p)) fulls
      NotFound -> [n]
 where
  known x =
    isLabel TermLabel c x
      || isLabel TypeLabel c x
      || isLabel FieldLabel c x
      || Map.member x c.history
      || isNamespace c x

{- | A word naming a stored namespace: relative to the current one, else
from the root; absolute with a leading dot.
-}
namespaceArg :: Session -> Text -> Maybe Text
namespaceArg session w
  | Just p <- T.stripPrefix "." w = if isNamespace cb p then Just p else Nothing
  | not (null session.scope.namespace)
  , here <- S.qualify session.scope.namespace w
  , isNamespace cb here =
      Just here
  | isNamespace cb w = Just w
  | otherwise = Nothing
 where
  cb = session.codebase

-- | @namespace orbital@, or the root.
namespaceLine :: [Text] -> Text
namespaceLine = \case
  [] -> "namespace . (the root)"
  ns -> "namespace " <> T.intercalate "." ns

-- | @1 label@, @5 labels@.
labelsText :: Int -> Text
labelsText k = T.pack (show k) <> (if k == 1 then " label" else " labels")

-- | What a label names, for messages.
labelNoun :: Codebase -> Text -> Text
labelNoun cb n
  | Map.member n cb.names = "definition"
  | Map.member n cb.conNames = "constructor"
  | Map.member n cb.typeNames = "type"
  | Map.member n cb.fieldNames = "field"
  | otherwise = "name"

-- | The labels of each kind among some paths: a type and its constructor of one name are two.
labelKinds :: Codebase -> [Text] -> [(Text, LabelKind)]
labelKinds cb paths =
  [(p, k) | p <- paths, k <- [TermLabel, TypeLabel, FieldLabel], isLabel k cb p]

-- | Remove a label of every kind; history keeps it.
removeLabel :: Text -> Codebase -> Codebase
removeLabel n = unbindName n . unbindName ("." <> n)

{- | Relabel (design §7.2, §7.6): each new path gets the labels of every kind
its old path has, with their unit and chart flags, and unless aliasing the
old labels go. History keeps both. All or nothing: a new path that is
already a label of the same kind, two old paths given one new path, or a
new path that would be both a label and a namespace refuses the whole
change. Returns the codebase and the number of labels given.
-}
relabel :: Bool -> [(Text, Text)] -> Codebase -> Either Text (Codebase, Int)
relabel keepOld pairs cb = do
  let moves = [(o, n, k) | (o, n) <- pairs, (_, k) <- labelKinds cb [o]]
      base = if keepOld then cb else foldr (removeLabel . fst) cb pairs
      clashes =
        [ n
        | (i, (o, n, k)) <- zip [0 :: Int ..] moves
        , (o /= n && isLabel k base n)
            || any (\(_, n', k') -> n' == n && k' == k) (take i moves)
        ]
  case clashes of
    n : _ -> Left ("`" <> n <> "` is already a label; nothing was changed")
    [] -> Right ()
  case disjointness
    base
    [(n, labelNoun cb o, S.Span (S.Pos 1 1) (S.Pos 1 1)) | (o, n, _) <- moves] of
    Just (_, msg) -> Left (msg <> "; nothing was changed")
    Nothing -> Right ()
  pure (foldl copy base moves, length moves)
 where
  -- A signature moves with its name, and an alias, being the hash, is
  -- unsigned (design §4.8).
  copy acc (o, n, k) = case k of
    TermLabel
      | Just r <- lookupName o cb ->
          (if isUnitName o cb then markUnit n else id)
            . (if isChartName o cb then markChart n else id)
            . maybe id (setSignature n) (if keepOld then Nothing else signatureOf o cb)
            $ bindName n r acc
      | Just (h, i) <- lookupConName o cb -> bindConName n h i acc
    TypeLabel | Just h <- lookupTypeName o cb -> bindTypeName n h acc
    FieldLabel | Just (h, i, j) <- lookupFieldName o cb -> bindFieldName n h i j acc
    _ -> acc
