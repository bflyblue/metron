{- | The codebase (design §7): terms by hash, names as labels pointing at
references, and the history of every name.
-}
module Eval.Codebase (
  Reference (..),
  Codebase (..),
  emptyCodebase,
  addTerm,
  addTypeDef,
  lookupTypeDef,
  bindTypeName,
  bindConName,
  lookupTypeName,
  lookupConName,
  typeNameOf,
  conNameOf,
  bindFieldName,
  lookupFieldName,
  fieldNamesOf,
  bindName,
  unbindName,
  markUnit,
  isUnitName,
  unitNameFor,
  markChart,
  isChartName,
  clearFlags,
  addPreference,
  removePreference,
  addStoredUse,
  removeStoredUse,
  chartNameFor,
  lookupName,
  lookupTerm,
  lookupTypes,
  lookupTyped,
  typeOf,
  namesOf,
  historicalNamesOf,
  historyOf,
  dependents,
  writtenAs,
  findByPrefix,
  showReference,
  signatureOf,
  setSignature,
  dropSignature,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Syntax (Use (..))
import Eval.TCore (TTerm, signatureHolds)
import Eval.Type (Scheme, TypeDef (..), canonicalScheme)

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
  , charts :: Set.Set Text
  -- ^ names declared with @chart@ (design §3.6)
  , preferences :: Set.Set Text
  -- ^ display preferences as written (@km/h@), label-level metadata (design §3.2.12)
  , typeDefs :: Map Hash TypeDef
  -- ^ declared data types by the hash of their definition (design §2.3)
  , typeNames :: Map Text Hash
  -- ^ type names: labels on type definitions
  , conNames :: Map Text (Hash, Int)
  -- ^ constructor names: labels on a type's constructors
  , fieldNames :: Map Text (Hash, Int, Int)
  -- ^ record field names: labels on a constructor's positions (design §2.3)
  , uses :: [Use]
  {- ^ the codebase's stored default @use@s, oldest first (design §7.7): the
  library's six from seeding. A name resolves through them after the root.
  -}
  , signatures :: Map Text Scheme
  {- ^ signatures by definition name (design §4.8): label-level, like units,
  so two names of one hash may carry different ones; each is an instance of
  its name's scheme, canonical ('canonicalScheme')
  -}
  }

emptyCodebase :: Codebase
emptyCodebase =
  Codebase
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Set.empty
    Set.empty
    Set.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    []
    Map.empty

{- | The signature a definition name carries (design §4.8), if it carries
one and the name is still bound.
-}
signatureOf :: Text -> Codebase -> Maybe Scheme
signatureOf n cb = Map.lookup n cb.signatures

-- | Give a definition name a signature, which must hold of its scheme.
setSignature :: Text -> Scheme -> Codebase -> Codebase
setSignature n sig cb = cb{signatures = Map.insert n (canonicalScheme sig) cb.signatures}

dropSignature :: Text -> Codebase -> Codebase
dropSignature n cb = cb{signatures = Map.delete n cb.signatures}

{- | Add a stored default @use@ (design §7.7) after the others; one already
there moves to the end, as a repeated @use@ statement does.
-}
addStoredUse :: Use -> Codebase -> Codebase
addStoredUse u cb = cb{uses = filter (/= u) cb.uses ++ [u]}

removeStoredUse :: Use -> Codebase -> Codebase
removeStoredUse u cb = cb{uses = filter (/= u) cb.uses}

{- | Declare a name a display unit (design §3.2.12). Units are names, not
references: two names for one hash can be a unit and a plain quantity.
-}
markUnit :: Text -> Codebase -> Codebase
markUnit n cb = cb{units = Set.insert n cb.units}

isUnitName :: Text -> Codebase -> Bool
isUnitName n cb = Set.member n cb.units

markChart :: Text -> Codebase -> Codebase
markChart n cb = cb{charts = Set.insert n cb.charts}

isChartName :: Text -> Codebase -> Bool
isChartName n cb = Set.member n cb.charts

addPreference, removePreference :: Text -> Codebase -> Codebase
addPreference t cb = cb{preferences = Set.insert t cb.preferences}
removePreference t cb = cb{preferences = Set.delete t cb.preferences}

clearFlags :: Text -> Codebase -> Codebase
clearFlags n cb = cb{units = Set.delete n cb.units, charts = Set.delete n cb.charts}

{- | The unit name a reference is used under: the written name when it is a
unit that still points at this reference, else any current unit name of
the reference (so a renamed unit prints under its new name), else none.
-}
unitNameFor :: Reference -> Text -> Codebase -> Maybe Text
unitNameFor = nameUnder isUnitName

chartNameFor :: Reference -> Text -> Codebase -> Maybe Text
chartNameFor = nameUnder isChartName

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
  case drop (fromMaybe 0 idx) schemes of
    s : _ -> Just s
    [] -> Nothing

{- | Point a name at a reference, recording the previous binding in history.
Re-binding a name to what it already points at changes nothing. A
signature the name carries stays only if it holds of the new definition
(design §4.8); a group that rebinds a signed name checks that first and
refuses, so this drop is only for what rebinds without asking.
-}
bindName :: Text -> Reference -> Codebase -> Codebase
bindName n r cb
  | lookupName n cb == Just r = cb
  | otherwise =
      cb
        { names = Map.insert n r cb.names
        , history = Map.insertWith (++) n [r] cb.history
        , -- Constructors and definitions share the expression namespace.
          conNames = Map.delete n cb.conNames
        , signatures = Map.update stillHolds n cb.signatures
        }
 where
  stillHolds sig = case typeOf r cb of
    Just general | signatureHolds sig general -> Just sig
    _ -> Nothing

{- | Remove a label, whatever it names (a definition, a type or a
constructor), and with it any unit or chart declaration it carried. The
term and the name's history stay.
-}
unbindName :: Text -> Codebase -> Codebase
unbindName n cb
  -- A field label is named with its dot: @:unname .mass@.
  | Just f <- T.stripPrefix "." n = cb{fieldNames = Map.delete f cb.fieldNames}
  | otherwise =
      cb
        { names = Map.delete n cb.names
        , units = Set.delete n cb.units
        , charts = Set.delete n cb.charts
        , typeNames = Map.delete n cb.typeNames
        , conNames = Map.delete n cb.conNames
        , signatures = Map.delete n cb.signatures
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
dependents :: Text -> Hash -> Codebase -> [Text]
dependents name h cb =
  sortOn
    id
    [ n
    | (n, Reference h' _) <- Map.toList cb.names
    , Just t <- [lookupTerm h' cb]
    , any
        (\(rh, _, w) -> rh == h && (T.null w || w == name))
        (Set.toList (refsWritten t))
    ]

-- | Hashes in the codebase whose base32hex form starts with a prefix.
findByPrefix :: Text -> Codebase -> [Hash]
findByPrefix p cb = filter (hashHasPrefix p) (Map.keys cb.terms)

-- | @#a3f9k@ for a plain term, @#a3f9k.1@ for member 1 of a cycle.
showReference :: Reference -> Text
showReference (Reference h idx) = showHash h <> maybe "" (\i -> "." <> T.pack (show i)) idx

-- Data types ----------------------------------------------------------------------

-- | Store a type definition under its hash. A no-op if already present.
addTypeDef :: Hash -> TypeDef -> Codebase -> Codebase
addTypeDef h def cb = cb{typeDefs = Map.insertWith (\_new old -> old) h def cb.typeDefs}

lookupTypeDef :: Hash -> Codebase -> Maybe TypeDef
lookupTypeDef h cb = Map.lookup h cb.typeDefs

bindTypeName :: Text -> Hash -> Codebase -> Codebase
bindTypeName n h cb = cb{typeNames = Map.insert n h cb.typeNames}

{- | Bind a constructor name. A definition of that name is unnamed: constructors
and definitions share the expression namespace, and the newer label wins.
-}
bindConName :: Text -> Hash -> Int -> Codebase -> Codebase
bindConName n h i cb =
  cb
    { conNames = Map.insert n (h, i) cb.conNames
    , names = Map.delete n cb.names
    , units = Set.delete n cb.units
    , charts = Set.delete n cb.charts
    , signatures = Map.delete n cb.signatures
    }

lookupTypeName :: Text -> Codebase -> Maybe Hash
lookupTypeName n cb = Map.lookup n cb.typeNames

lookupConName :: Text -> Codebase -> Maybe (Hash, Int)
lookupConName n cb = Map.lookup n cb.conNames

{- | The current names of a type and of one of its constructors. Minted
axes are named as what minted them, a turned chart's frame or a space
(design §3.10, F4: a frame's or a space's name in an axis position means
its axes), when that is a type's name.
-}
typeNameOf :: Hash -> Codebase -> Maybe Text
typeNameOf h cb = case [n | (n, h') <- Map.toList cb.typeNames, h' == h] of
  n : _ -> Just n
  []
    | Just def <- Map.lookup h cb.typeDefs
    , Axes path <- def.label
    , Map.member path cb.typeNames ->
        Just path
    | otherwise -> Nothing

conNameOf :: Hash -> Int -> Codebase -> Maybe Text
conNameOf h i cb = case [n | (n, (h', i')) <- Map.toList cb.conNames, h' == h, i' == i] of
  n : _ -> Just n
  [] -> Nothing

-- | Name field @j@ of constructor @i@ of a type.
bindFieldName :: Text -> Hash -> Int -> Int -> Codebase -> Codebase
bindFieldName n h i j cb = cb{fieldNames = Map.insert n (h, i, j) cb.fieldNames}

lookupFieldName :: Text -> Codebase -> Maybe (Hash, Int, Int)
lookupFieldName n cb = Map.lookup n cb.fieldNames

-- | The field names of a constructor, by position; 'Nothing' where unnamed.
fieldNamesOf :: Hash -> Int -> Int -> Codebase -> [Maybe Text]
fieldNamesOf h i arity cb =
  [ case [n | (n, (h', i', j')) <- Map.toList cb.fieldNames, h' == h, i' == i, j' == j] of
      n : _ -> Just n
      [] -> Nothing
  | j <- [0 .. arity - 1]
  ]

{- | Whether a reference written under a name refers to a label (design §7.5):
the names agree; or the written name is the label's path seen from inside
its namespace; or the written name is no longer a label at all, in which
case the reference means whatever its hash is called now (the name was
renamed or moved, as the library was under @). A written name that still
exists means that name and no other: a user's @ and the library's
.metre@ share a term, and a reference written .metre@ is not a
dependent of @. An empty written name (a format-1 term) agrees with
every label.
-}
writtenAs :: Codebase -> Text -> Text -> Bool
writtenAs cb written label =
  T.null written
    || written == label
    || ("." <> written) `T.isSuffixOf` label
    || not (isLabel written)
 where
  isLabel n =
    Map.member n cb.names
      || Map.member n cb.typeNames
      || Map.member n cb.conNames
      || Map.member n cb.fieldNames
