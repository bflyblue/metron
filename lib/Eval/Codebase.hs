{- | The codebase (design §7): terms by hash, names as labels pointing at
references, and the history of every name.
-}
module Eval.Codebase (
  Reference (..),
  Codebase (..),
  emptyCodebase,
  addTerm,
  bindName,
  unbindName,
  markUnit,
  isUnitRef,
  lookupName,
  lookupTerm,
  lookupTypes,
  lookupTyped,
  typeOf,
  namesOf,
  historicalNamesOf,
  historyOf,
  dependents,
  findByPrefix,
  showReference,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Hash (hashHasPrefix, showHash)
import Eval.TCore (TTerm)
import Eval.Type (Scheme)

{- | A reference to a definition: a hash, plus a member index when the hashed
term is a 'Cycle'.
-}
data Reference = Reference {hash :: Hash, index :: Maybe Int}
  deriving stock (Eq, Ord, Show)

data Codebase = Codebase
  { terms :: Map Hash (Term Z)
  -- ^ Core: the hashed content
  , derived :: Map Hash ([Scheme], TTerm Z)
  -- ^ types and Typed Core, recomputable (design §5.2, §5.3)
  , names :: Map Text Reference
  , history :: Map Text [Reference] -- newest first
  , units :: Set.Set Reference
  -- ^ definitions declared with @unit@ (design §3.2.12); label-level metadata like names
  }

emptyCodebase :: Codebase
emptyCodebase = Codebase Map.empty Map.empty Map.empty Map.empty Set.empty

markUnit :: Reference -> Codebase -> Codebase
markUnit r cb = cb{units = Set.insert r cb.units}

isUnitRef :: Reference -> Codebase -> Bool
isUnitRef r cb = Set.member r cb.units

{- | Store a term with its types and Typed Core under its hash. A no-op if
already present.
-}
addTerm :: Hash -> Term Z -> [Scheme] -> TTerm Z -> Codebase -> Codebase
addTerm h t schemes typed cb =
  cb
    { terms = Map.insertWith (\_new old -> old) h t cb.terms
    , derived = Map.insertWith (\_new old -> old) h (schemes, typed) cb.derived
    }

lookupTypes :: Hash -> Codebase -> Maybe [Scheme]
lookupTypes h cb = fst <$> Map.lookup h cb.derived

lookupTyped :: Hash -> Codebase -> Maybe (TTerm Z)
lookupTyped h cb = snd <$> Map.lookup h cb.derived

-- | The type of what a reference points at.
typeOf :: Reference -> Codebase -> Maybe Scheme
typeOf (Reference h idx) cb = do
  schemes <- lookupTypes h cb
  case drop (maybe 0 id idx) schemes of
    s : _ -> Just s
    [] -> Nothing

{- | Point a name at a reference, recording the previous binding in history.
Re-binding a name to what it already points at changes nothing.
-}
bindName :: Text -> Reference -> Codebase -> Codebase
bindName n r cb
  | lookupName n cb == Just r = cb
  | otherwise =
      cb
        { names = Map.insert n r cb.names
        , history = Map.insertWith (\new old -> new ++ old) n [r] cb.history
        }

-- | Remove a label. The term and the name's history stay.
unbindName :: Text -> Codebase -> Codebase
unbindName n cb = cb{names = Map.delete n cb.names}

lookupName :: Text -> Codebase -> Maybe Reference
lookupName n cb = Map.lookup n cb.names

lookupTerm :: Hash -> Codebase -> Maybe (Term Z)
lookupTerm h cb = Map.lookup h cb.terms

-- | Names that currently point at a reference, sorted.
namesOf :: Reference -> Codebase -> [Text]
namesOf r cb = sortOn id [n | (n, r') <- Map.toList cb.names, r' == r]

-- | Names that have ever pointed at a reference, sorted.
historicalNamesOf :: Reference -> Codebase -> [Text]
historicalNamesOf r cb = sortOn id [n | (n, rs) <- Map.toList cb.history, r `elem` rs]

historyOf :: Text -> Codebase -> [Reference]
historyOf n cb = Map.findWithDefault [] n cb.history

-- | Names whose current definition mentions the given hash.
dependents :: Hash -> Codebase -> [Text]
dependents h cb =
  sortOn
    id
    [ n
    | (n, Reference h' _) <- Map.toList cb.names
    , Just t <- [lookupTerm h' cb]
    , h `Set.member` refs t
    ]

-- | Hashes in the codebase whose base32hex form starts with a prefix.
findByPrefix :: Text -> Codebase -> [Hash]
findByPrefix p cb = filter (hashHasPrefix p) (Map.keys cb.terms)

-- | @#a3f9k@ for a plain term, @#a3f9k.1@ for member 1 of a cycle.
showReference :: Reference -> Text
showReference (Reference h idx) = showHash h <> maybe "" (\i -> "." <> T.pack (show i)) idx
