{-# LANGUAGE PatternSynonyms #-}

{- | The table at a branch point (design §8.2, "Branches under copies"),
written for the user: the branch point found by its site in the Core it
came from, its scrutinee and alternatives printed as source, and a row
for each alternative counting the copies whose own scrutinee selects it.
-}
module Metron.Branch (
  tableLines,
) where

import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as T
import Metron.Builtin (pattern FalseC, pattern TrueC)
import Metron.Codebase (Codebase, lookupTerm)
import Metron.Core (
  Alt (..),
  Hash,
  Hint (..),
  Nat (Z),
  Term (..),
  Vec (..),
  vecAppend,
  vecIndex,
  vecMap,
  vecToList,
 )
import Metron.Dimension (Spelling)
import Metron.Pretty (RefNamer, renderTermIn)
import Metron.Remark (Cause (..), Site (..), Table (..))
import Metron.TCore (patternText)

-- | A term somewhere inside a definition, with the names of the variables in scope.
data Inside = forall n. Inside (Vec n Text) (Term n)

{- | A branch point as source: the words its table is headed by (@if x >
0.9@, @case xs of@) and its alternatives in the order of their
constructors, each with its label and the place its row is shown in.
-}
data Branch = Branch {heading :: Text, alternatives :: [(Int, Text)]}

{- | The lines a table prints as, after the value: a @warning:@ where the
copies followed the nominal branch, rounding alone setting them apart,
and a @note:@ where they split, each down its own alternative. The
input's own Core stands for its hash; the names are written as
@namer@ and @named@ write them. 'Nothing' for a site that is not a
branch point of the Core found, which does not happen.
-}
tableLines ::
  Spelling ->
  RefNamer ->
  (Text -> Text) ->
  Codebase ->
  (Hash, Term Z) ->
  Int ->
  Table ->
  [Text]
tableLines spelling namer named cb (inputHash, input) samples t =
  case branchAt spelling namer named =<< termAt cb (inputHash, input) t.site of
    Nothing -> []
    Just b -> header b : map (row b) (rowsOf b)
 where
  header b =
    (if t.split then "note: " else "warning: ")
      <> "the branch at `"
      <> b.heading
      <> "` goes "
      <> (if ways > 2 then "several ways" else "both ways")
      <> " across "
      <> (if t.evaluations > 1 then tshow t.evaluations <> " evaluations × " else "")
      <> tshow samples
      <> " samples ("
      <> ( case t.cause of
             Rounding -> "lost in rounding"
             Draws -> "by the declared uncertainty"
         )
      <> ( if left > 0
             then
               "; " <> tshow left <> " had left the evaluated path at an earlier branch point"
             else ""
         )
      <> "):"
  -- The alternatives some copy selects or the nominal branch takes.
  ways = IntMap.size (IntMap.union (IntMap.filter (> 0) t.rows) t.taken)
  left = t.evaluations * samples - t.counted + t.departed
  rowsOf b = b.alternatives
  width b = maximum (0 : map (T.length . snd) b.alternatives)
  countWidth = T.length (tshow (maximum (0 : IntMap.elems t.rows)))
  row b (k, label) =
    "  "
      <> T.justifyLeft (width b) ' ' label
      <> "   "
      <> T.justifyRight countWidth ' ' (tshow (IntMap.findWithDefault 0 k t.rows))
      <> taken k
  taken k = case IntMap.lookup k t.taken of
    Nothing -> ""
    Just j
      | IntMap.size t.taken == 1 -> "   ← taken (the nominal branch)"
      | otherwise ->
          "   ← taken in "
            <> tshow j
            <> " of "
            <> tshow t.evaluations
            <> " evaluations (the nominal branch)"

{- | The term at a site: in the input when the site is the input's, else in
the definition it names, down its path.
-}
termAt :: Codebase -> (Hash, Term Z) -> Site -> Maybe Inside
termAt cb (inputHash, input) site = do
  top <-
    if site.definition == inputHash
      then Just input
      else lookupTerm site.definition cb
  descend (Inside VNil top) (reverse site.path)
 where
  descend at = \case
    [] -> Just at
    i : rest -> child at i >>= (`descend` rest)

{- | A child of a term by the index the evaluator gives it ("Metron.Eval"):
a case's scrutinee is 0 and its alternatives from 1; a let's bound value
0 and its body 1; a lambda's body 0; a cycle's members by number.
-}
child :: Inside -> Int -> Maybe Inside
child (Inside ctx t) i = case t of
  Lam (Hint h) b | i == 0 -> Just (Inside (VCons (fresh h ctx) ctx) b)
  App f a -> nth [Inside ctx f, Inside ctx a]
  Let (Hint h) e b
    | i == 0 -> Just (Inside ctx e)
    | i == 1 -> Just (Inside (VCons (fresh h ctx) ctx) b)
  PrimApp _ args -> nth (map (Inside ctx) args)
  Con _ args -> nth (map (Inside ctx) args)
  Case sc alts
    | i == 0 -> Just (Inside ctx sc)
    | otherwise -> case drop (i - 1) alts of
        Alt _ hs b : _ -> Just (Inside (vecAppend (names hs) ctx) b)
        [] -> Nothing
  Pow b _ | i == 0 -> Just (Inside ctx b)
  Uncertain _ _ x e -> nth [Inside ctx x, Inside ctx e]
  Pack ts -> nth (map (Inside ctx) ts)
  Proj b _ | i == 0 -> Just (Inside ctx b)
  Cycle hs bodies -> Inside (vecAppend (names hs) ctx) <$> vecIndex i bodies
  _ -> Nothing
 where
  nth xs = case drop i xs of
    x : _ -> Just x
    [] -> Nothing
  names :: Vec k Hint -> Vec k Text
  names = vecMap (\(Hint h) -> fresh h ctx)

-- | A binder's name as printed: its hint, primed where it would shadow.
fresh :: Text -> Vec n Text -> Text
fresh h ctx
  | T.null h || "§" `T.isPrefixOf` h || h == "_" = fresh "x" ctx
  | h `elem` vecToList ctx = fresh (h <> "'") ctx
  | otherwise = h

-- | The branch point a term is, if it is a case.
branchAt :: Spelling -> RefNamer -> (Text -> Text) -> Inside -> Maybe Branch
branchAt spelling namer named (Inside ctx t) = case t of
  -- A case on Bool reads back as the if it came from.
  Case sc [Alt FalseC VNil _, Alt TrueC VNil _] ->
    Just
      Branch{heading = "if " <> render sc, alternatives = [(1, "then"), (0, "else")]}
  Case sc alts ->
    Just
      Branch
        { heading = "case " <> render sc <> " of"
        , alternatives =
            [ (k, named (patternText c (vecToList (vecMap (\(Hint h) -> fresh h ctx) hs))))
            | (k, Alt c hs _) <- zip [0 ..] alts
            ]
        }
  _ -> Nothing
 where
  render = named . renderTermIn spelling namer ctx

tshow :: (Show a) => a -> Text
tshow = T.pack . show
