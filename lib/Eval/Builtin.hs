{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{- | The types the language's own syntax builds (design §2.3, §4.1): @Bool@,
tuples and lists. They are not built into the type language or Core: each
is a @structural data@ declaration the compiler holds as a value and
refers to by its hash, which the declaration alone fixes, so it is known
without a codebase.

> structural data Bool = False | True
> structural data Pair a b = Pair a b
> structural data List a = Nil | Cons a (List a)

A tuple of @k@ components, @2 <= k <= 'maxTupleArity'@, is the structural
type of one constructor with @k@ fields, @(a, b, c)@ the one with three;
@Pair@ is the case @k = 2@. The standard library seeds @Bool@, @Pair@ and
@List@ under @std@ (design §7.7); a larger tuple's type is one the
compiler knows but no library names. The desugarer, inference, the
evaluator and the printers recognise these types and constructors by
hash, never by name: renaming them in the codebase changes nothing but
how a name prints.
-}
module Eval.Builtin (
  -- * The declarations
  boolDef,
  pairDef,
  listDef,
  tupleDef,
  maxTupleArity,
  builtinDefs,
  axesDef,
  axesHash,
  axesTag,
  isAxesDef,

  -- * Their hashes and types
  boolHash,
  pairHash,
  listHash,
  tupleHash,
  tupleArity,
  boolT,
  pairT,
  tupleT,
  listT,
  pattern BoolT,
  pattern TupleT,
  pattern ListT,

  -- * Their constructors
  falseC,
  trueC,
  pairC,
  tupleC,
  nilC,
  consC,
  boolC,
  pattern FalseC,
  pattern TrueC,
  pattern TupleC,
  pattern NilC,
  pattern ConsC,
  builtinCons,
  builtinConName,
  builtinTypeName,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core (ConRef (..), Hash, Label (..))
import Eval.Encode (hashTypeDef)
import Eval.Type.Base

-- The declarations ----------------------------------------------------------------

-- | @structural data Bool = False | True@: @False@ is constructor 0.
boolDef :: TypeDef
boolDef = TypeDef [] [[], []] structuralLabel

{- | @structural data TupleK a b … = TupleK a b …@, the type of a tuple of
@k@ components. Two or more: a tuple of one is its component.
-}
tupleDef :: Int -> TypeDef
tupleDef k =
  TypeDef
    [(v, KType) | v <- [0 .. k - 1]]
    [[TVar v | v <- [0 .. k - 1]]]
    structuralLabel

-- | @structural data Pair a b = Pair a b@, the tuple of two.
pairDef :: TypeDef
pairDef = tupleDef 2

-- | @structural data List a = Nil | Cons a (List a)@.
listDef :: TypeDef
listDef =
  TypeDef
    [(0, KType)]
    [[], [TVar 0, TData selfType [AType (TVar 0)]]]
    structuralLabel

{- | The most components a tuple may have. The bound is what lets a tuple's
type be recognised from its hash alone: the arities are a finite table.
-}
maxTupleArity :: Int
maxTupleArity = 32

{- | The axis type a chart declaration mints (design §3.9, decision 1): no
parameters, one constructor with no fields, stamped with the chart's full
path under a label kind no source @data@ has. Its hash is the chart's
axis set; its constructor is the chart primitive's first argument.
-}
axesDef :: Text -> TypeDef
axesDef path = TypeDef [] [[]] (Axes path)

axesHash :: Text -> Hash
axesHash = hashTypeDef . axesDef

-- | The constructor a chart primitive takes, the axes of the chart at a path.
axesTag :: Text -> ConRef
axesTag path = UserCon (axesHash path) 0

-- | Whether a declaration is a chart's minted axis type.
isAxesDef :: TypeDef -> Bool
isAxesDef def = case def.label of
  Axes _ -> True
  _ -> False

-- | The built-in declarations by hash: what every type lookup knows.
builtinDefs :: Hash -> Maybe TypeDef
builtinDefs h
  | h == boolHash = Just boolDef
  | h == listHash = Just listDef
  | Just k <- tupleArity h = Just (tupleDef k)
  | otherwise = Nothing

-- Hashes and types ----------------------------------------------------------------

boolHash :: Hash
boolHash = hashTypeDef boolDef

listHash :: Hash
listHash = hashTypeDef listDef

pairHash :: Hash
pairHash = tupleHash 2

tupleHashes :: Map Int Hash
tupleHashes = Map.fromList [(k, hashTypeDef (tupleDef k)) | k <- [2 .. maxTupleArity]]

tupleArities :: Map Hash Int
tupleArities = Map.fromList [(h, k) | (k, h) <- Map.toList tupleHashes]

-- | The hash of the tuple type of @k@ components.
tupleHash :: Int -> Hash
tupleHash k = Map.findWithDefault (hashTypeDef (tupleDef k)) k tupleHashes

-- | The number of components, if the hash is a tuple type's.
tupleArity :: Hash -> Maybe Int
tupleArity h = Map.lookup h tupleArities

boolT :: Type
boolT = TData boolHash []

pairT :: Type -> Type -> Type
pairT a b = tupleT [a, b]

-- | The tuple of the given component types (two or more).
tupleT :: [Type] -> Type
tupleT ts = TData (tupleHash (length ts)) (map AType ts)

listT :: Type -> Type
listT a = TData listHash [AType a]

-- | @Bool@.
pattern BoolT :: Type
pattern BoolT <- TData ((== boolHash) -> True) []
  where
    BoolT = boolT

-- | A tuple type, by its components.
pattern TupleT :: [Type] -> Type
pattern TupleT ts <- (asTupleT -> Just ts)
  where
    TupleT ts = tupleT ts

asTupleT :: Type -> Maybe [Type]
asTupleT = \case
  TData h as | Just k <- tupleArity h, length as == k -> traverse asType as
  _ -> Nothing
 where
  asType = \case
    AType t -> Just t
    _ -> Nothing

-- | @List a@, which prints as @{a}@.
pattern ListT :: Type -> Type
pattern ListT a <- TData ((== listHash) -> True) [AType a]
  where
    ListT a = listT a

-- Constructors --------------------------------------------------------------------

falseC, trueC, pairC, nilC, consC :: ConRef
falseC = UserCon boolHash 0
trueC = UserCon boolHash 1
pairC = tupleC 2
nilC = UserCon listHash 0
consC = UserCon listHash 1

-- | The constructor of the tuple of @k@ components.
tupleC :: Int -> ConRef
tupleC k = UserCon (tupleHash k) 0

-- | The constructor for a boolean.
boolC :: Bool -> ConRef
boolC b = if b then trueC else falseC

{- | A built-in type's constructors with their numbers of fields, in
canonical order; none for any other hash.
-}
builtinCons :: Hash -> [(ConRef, Int)]
builtinCons h =
  [ (UserCon h i, length fields)
  | Just def <- [builtinDefs h]
  , (i, fields) <- zip [0 ..] def.constructors
  ]

pattern FalseC :: ConRef
pattern FalseC <- UserCon ((== boolHash) -> True) 0
  where
    FalseC = falseC

pattern TrueC :: ConRef
pattern TrueC <- UserCon ((== boolHash) -> True) 1
  where
    TrueC = trueC

-- | A tuple's constructor, by its number of components.
pattern TupleC :: Int -> ConRef
pattern TupleC k <- UserCon (tupleArity -> Just k) 0
  where
    TupleC k = tupleC k

pattern NilC :: ConRef
pattern NilC <- UserCon ((== listHash) -> True) 0
  where
    NilC = nilC

pattern ConsC :: ConRef
pattern ConsC <- UserCon ((== listHash) -> True) 1
  where
    ConsC = consC

{- | The name a built-in constructor prints under without a codebase, as
the declarations above spell it; @Tuple3@ and on for the larger tuples.
-}
builtinConName :: ConRef -> Maybe Text
builtinConName = \case
  FalseC -> Just "False"
  TrueC -> Just "True"
  TupleC k -> Just (tupleName k)
  NilC -> Just "Nil"
  ConsC -> Just "Cons"
  _ -> Nothing

-- | The name a built-in type's declaration is written under.
builtinTypeName :: Hash -> Maybe Text
builtinTypeName h
  | h == boolHash = Just "Bool"
  | h == listHash = Just "List"
  | Just k <- tupleArity h = Just (tupleName k)
  | otherwise = Nothing

tupleName :: Int -> Text
tupleName = \case
  2 -> "Pair"
  k -> "Tuple" <> T.pack (show k)
