{- | The check before running (design §8.2): an input that uses, directly or
through any definition it reaches, a built-in the current backend does not
have is refused before it runs, with the path that reaches it.

What a definition needs is its own backend-specific built-ins, found by
the walk that finds its references ('directUses'), and what its
dependencies need: @needs(h) = direct(h) ∪ ⋃ needs(d)@. A recursive group
is one hash, a cycle, so its members share one union. A hash names an
immutable term, so @needs(h)@ is memoised by hash and never invalidated;
the memo holds built-in names, not backends, so a new backend or a
built-in added to one changes nothing in it. An input's own Core is
walked, and the memo answers for the hashes it refers to, so the library
is walked once a session. Only when the check fails is the graph searched
for the path the message names.

The check is sound, since every function value, closure and record is
built from Core in the closure, and conservative, as a type check is:
@if false then sd x else 0@ is refused under double.
-}
module Metron.Needs (
  Needs,
  noNeeds,
  needsOf,
  reachedBy,
  checkBackend,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (empty, insert, lookup)
import Data.Maybe (isJust)
import Data.Set (Set)
import Data.Set qualified as Set (empty, member, toList)
import Data.Text (Text)
import Data.Text qualified as T (intercalate)
import Metron.Core (Hash, Nat (Z), Term, directUses)
import Metron.Scalar (Backend, ownerOf, refusal, refusalClause, refusalOf)

-- | What each definition needs, by hash: the backend-specific built-ins it reaches.
newtype Needs = Needs (Map Hash (Set Text))

noNeeds :: Needs
noNeeds = Needs Map.empty

-- | A term's references and its own backend-specific built-ins.
direct :: Term n -> (Set (Hash, Maybe Int), Set Text)
direct = directUses (\name -> name == "sample" || isJust (ownerOf name))

{- | What a definition needs, and the memo with it, and with what its
dependencies need, recorded. A hash with no term here is not recorded:
the evaluation reports it.
-}
needsOf :: Map Hash (Term Z) -> Hash -> Needs -> (Set Text, Needs)
needsOf terms h memo@(Needs m) = case Map.lookup h m of
  Just s -> (s, memo)
  Nothing -> case Map.lookup h terms of
    Nothing -> (Set.empty, memo)
    Just t ->
      let (rs, own) = direct t
          (s, Needs m') = foldl' step (own, memo) [d | (d, _) <- Set.toList rs, d /= h]
       in (s, Needs (Map.insert h s m'))
 where
  step (acc, memo') d = let (s, memo'') = needsOf terms d memo' in (acc <> s, memo'')

{- | The backend-specific built-ins an input reaches, itself or through the
definitions it refers to; the memo comes back extended.
-}
reachedBy :: Map Hash (Term Z) -> Needs -> Term Z -> (Set Text, Needs)
reachedBy terms memo t =
  let (rs, own) = direct t
   in foldl'
        (\(acc, mm) (d, _) -> let (s, mm') = needsOf terms d mm in (acc <> s, mm'))
        (own, memo)
        (Set.toList rs)

{- | Whether an input may run under a backend at a number of samples (the
double backend has some built-ins only with copies), its Core given; the
memo comes back extended either way. The names a reference prints with
come from the caller.
-}
checkBackend ::
  Backend ->
  Int ->
  ((Hash, Maybe Int) -> Text) ->
  Map Hash (Term Z) ->
  Needs ->
  Term Z ->
  (Either Text (), Needs)
checkBackend b samples nameOf terms memo t =
  let (rs, own) = direct t
      (total, memo') = reachedBy terms memo t
      refused = [(n, why) | n <- Set.toList total, Just why <- [refusalOf b samples n]]
   in case refused of
        [] -> (Right (), memo')
        (n, why) : _
          | n `Set.member` own -> (Left (refusal b n why), memo')
          | otherwise -> (Left (explain n why (pathTo memo' n (Set.toList rs))), memo')
 where
  explain n why = \case
    first : rest ->
      "`"
        <> nameOf first
        <> "` uses `"
        <> n
        <> "`"
        <> ( if null rest
               then ""
               else
                 " (through " <> T.intercalate ", " ["`" <> nameOf r <> "`" | r <- rest] <> ")"
           )
        <> ", "
        <> refusalClause b why
    [] -> refusal b n why
  -- The first reference that needs the name, then down through the
  -- definitions that need it to one that uses it itself.
  pathTo (Needs m) n = \case
    [] -> []
    r@(h, _) : more
      | needs h -> r : down h
      | otherwise -> pathTo (Needs m) n more
   where
    needs h = maybe False (n `Set.member`) (Map.lookup h m)
    down h = case Map.lookup h terms of
      Nothing -> []
      Just t' ->
        let (rs, own) = direct t'
         in if n `Set.member` own
              then []
              else case [r | r@(d, _) <- Set.toList rs, d /= h, needs d] of
                r@(d, _) : _ -> r : down d
                [] -> []
