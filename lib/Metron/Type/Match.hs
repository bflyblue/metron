-- | One-way matching of types against quantified schemes, also used to validate signatures.
module Metron.Type.Match (
  signatureHolds,
  isInstanceOf,
) where

import Control.Monad ( foldM )
import Metron.Dimension
    ( dimAtoms, dimDiv, dimFromAtoms, dimRoot, DimAtom(DVar) )
import Metron.Type
    ( applyType,
      substOnce,
      varArg,
      Arg(ADim, AType, ARole, AFrame, ASpace, AShape, AAxis, ALen),
      Axis(AVar),
      Frame(Frame),
      FrameSlot(FrVar),
      Len(LRank, LLit, LVar),
      Role(RVar),
      Scheme(..),
      Shape(SNil, SVar, SCons),
      Space(Space),
      SpaceSlot(SpVar),
      Type(TTensor, TVar, TFun, TQty, TPoint, TChart, TOver, TData) )
import Data.Map.Strict qualified as Map
    ( empty, lookup, member, fromList, insert )

{- | Whether a signature holds of a definition's scheme (design §4.8): the
signature's type, its own variables held fixed as if they were constants,
is an instance of the scheme. So @Num m -> Num m@ holds of @a -> a@,
and @a -> a@ does not hold of @Num -> Num@: a signature narrows a
definition's type and never widens it.
-}
signatureHolds :: Scheme -> Scheme -> Bool
signatureHolds (Forall _ t) general = t `isInstanceOf` general

{- | Whether a type is an instance of a scheme: one-way matching of the
scheme's quantified variables, each at its kind. Arguments come before
results in a scheme, so by the time a composite dimension such as
@d1 d2@ is met, its variables are bound and it is checked by equality;
the one composite that binds is a single variable to a power (@sqrt@),
solved by taking the root.

A rank in the pattern (@timap@'s @Vec (rank s)@) can come before the shape
that fixes it, so it is skipped while matching, and the whole pattern,
substituted and normalised, is compared with the type at the end.
-}
isInstanceOf :: Type -> Scheme -> Bool
isInstanceOf ty (Forall vs0 pat0) = case matchType pat ty Map.empty of
  Just m -> substOnce m pat == ty
  Nothing -> False
 where
  -- The scheme's variable ids are small fixed numbers that can coincide
  -- with the inferred type's ids; rename them to negative ids, which no
  -- inferred type contains, so pattern and actual variables never mix.
  renamed = Map.fromList [(v, varArg k (negate (v + 1))) | (v, k) <- vs0]
  vs = [(negate (v + 1), k) | (v, k) <- vs0]
  pat = applyType renamed pat0
  quantified v = v `elem` map fst vs
  matchType p t m = case (p, t) of
    (TVar v, _) | quantified v -> bindArg v (AType t) m
    (TFun a b, TFun c d) -> matchType a c m >>= matchType b d
    (TQty r sa da, TQty r' sb db) ->
      matchRole r r' m >>= matchShape sa sb >>= matchDim da db
    (TPoint f, TPoint g) -> matchFrame f g m
    (TChart f, TChart g) -> matchFrame f g m
    -- A synonym is checked by the comparison at the end, reduced.
    (TOver _ _, _) -> Just m
    (TData h as, TData h' bs)
      | h == h' && length as == length bs ->
          foldM (\acc (a, b) -> matchArg a b acc) m (zip as bs)
    _ -> if p == t then Just m else Nothing
  matchArg p a m = case (p, a) of
    (AType x, AType y) -> matchType x y m
    (ALen x, ALen y) -> matchLen x y m
    (AShape x, AShape y) -> matchShape x y m
    (ADim x, ADim y) -> matchDim x y m
    (AAxis x, AAxis y) -> matchAxis x y m
    (AFrame x, AFrame y) -> matchFrameSlot x y m
    (ASpace x, ASpace y) -> matchSpaceSlot x y m
    (ARole x, ARole y) -> matchRole x y m
    _ -> Nothing
  matchRole p a m = case p of
    RVar v | quantified v -> bindArg v (ARole a) m
    _ -> if p == a then Just m else Nothing
  matchFrame (Frame s a sp) (Frame s' a' sp') m =
    matchFrameSlot s s' m >>= matchAxis a a' >>= matchSpace sp sp'
  matchSpace (Space s sh d b) (Space s' sh' d' b') m =
    matchSpaceSlot s s' m >>= matchShape sh sh' >>= matchDim d d' >>= matchAxis b b'
  matchFrameSlot p a m = case p of
    FrVar v | quantified v -> bindArg v (AFrame a) m
    _ -> if p == a then Just m else Nothing
  matchSpaceSlot p a m = case p of
    SpVar v | quantified v -> bindArg v (ASpace a) m
    _ -> if p == a then Just m else Nothing
  matchShape p sh m = case (p, sh) of
    (SVar v, _) | quantified v -> bindArg v (AShape sh) m
    (SCons l a rest, SCons l' a' rest') ->
      matchLen l l' m >>= matchAxis a a' >>= matchShape rest rest'
    _ -> if p == sh then Just m else Nothing
  -- A quantified axis variable stands for any slot; anything else matches itself.
  matchAxis p a m = case p of
    AVar v | quantified v -> bindArg v (AAxis a) m
    _ -> if p == a then Just m else Nothing
  matchLen p l m = case p of
    LVar v off | quantified v -> case l of
      LLit j | j >= off -> bindArg v (ALen (LLit (j - off))) m
      LVar u j | j >= off -> bindArg v (ALen (LVar u (j - off))) m
      LRank u j | j >= off -> bindArg v (ALen (LRank u (j - off))) m
      _ -> Nothing
    LRank v _ | quantified v -> Just m
    _ -> if p == l then Just m else Nothing
  -- Bound pattern variables are replaced once (their replacements come
  -- from another namespace and must not be chased); the remaining
  -- pattern variables are the scheme's unbound ones.
  matchDim p actual m =
    let unbound = [(v, k) | (DVar v, k) <- dimAtoms p, quantified v, not (Map.member v m)]
        boundPart =
          dimFromAtoms
            [ (a, k)
            | (a, k) <- dimAtoms p
            , case a of DVar v -> not (quantified v) || Map.member v m; _ -> True
            ]
        known = case substOnce m (TTensor SNil boundPart) of
          TTensor _ d -> d
          _ -> boundPart
     in case unbound of
          [] -> if known == actual then Just m else Nothing
          [(v, k)] ->
            -- p = known · v^k, so v^k = actual / known.
            dimRoot k (dimDiv actual known) >>= \root -> bindArg v (ADim root) m
          _ -> Nothing
  bindArg v arg m = case Map.lookup v m of
    Nothing -> Just (Map.insert v arg m)
    Just existing -> if existing == arg then Just m else Nothing
