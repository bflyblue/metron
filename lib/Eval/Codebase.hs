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
  isUnitName,
  unitNameFor,
  markScale,
  isScaleName,
  clearFlags,
  addPreference,
  removePreference,
  scaleNameFor,
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
  , units :: Set.Set Text
  -- ^ names declared with @unit@ (design §3.2.12); label-level metadata like names
  , scales :: Set.Set Text
  -- ^ names declared with @scale@ (design §3.6)
  , preferences :: Set.Set Text
  -- ^ display preferences as written (@km/h@), label-level metadata (design §3.2.12)
  }

emptyCodebase :: Codebase
emptyCodebase =
  Codebase Map.empty Map.empty Map.empty Map.empty Set.empty Set.empty Set.empty

{- | Declare a name a display unit (design §3.2.12). Units are names, not
references: two names for one hash can be a unit and a plain quantity.
-}
markUnit :: Text -> Codebase -> Codebase
markUnit n cb = cb{units = Set.insert n cb.units}

isUnitName :: Text -> Codebase -> Bool
isUnitName n cb = Set.member n cb.units

markScale :: Text -> Codebase -> Codebase
markScale n cb = cb{scales = Set.insert n cb.scales}

isScaleName :: Text -> Codebase -> Bool
isScaleName n cb = Set.member n cb.scales

addPreference, removePreference :: Text -> Codebase -> Codebase
addPreference t cb = cb{preferences = Set.insert t cb.preferences}
removePreference t cb = cb{preferences = Set.delete t cb.preferences}

clearFlags :: Text -> Codebase -> Codebase
clearFlags n cb = cb{units = Set.delete n cb.units, scales = Set.delete n cb.scales}

{- | The unit name a reference is used under: the written name when it is a
unit that still points at this reference, else any current unit name of
the reference (so a renamed unit prints under its new name), else none.
-}
unitNameFor :: Reference -> Text -> Codebase -> Maybe Text
unitNameFor = nameUnder isUnitName

scaleNameFor :: Reference -> Text -> Codebase -> Maybe Text
scaleNameFor = nameUnder isScaleName

nameUnder ::
  (Text -> Codebase -> Bool) -> Reference -> Text -> Codebase -> Maybe Text
nameUnder flagged r written cb
  -- The written name still points here: it alone decides, so `let eggs = 12`
  -- is a quantity even if `unit dozen = 12` shares its hash.
  | Map.lookup written cb.names == Just r =
      if flagged written cb then Just written else Nothing
  -- The written name has moved or gone (a renamed unit): any current unit
  -- name of the reference stands in.
  | otherwise = case [n | n <- namesOf r cb, flagged n cb] of
      n : _ -> Just n
      [] -> Nothing

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

{- | Remove a label. The term and the name's history stay.
| Remove a label, and with it any unit or scale declaration it carried.
-}
unbindName :: Text -> Codebase -> Codebase
unbindName n cb =
  cb
    { names = Map.delete n cb.names
    , units = Set.delete n cb.units
    , scales = Set.delete n cb.scales
    }

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
