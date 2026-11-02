{- | Which arguments a call certainly evaluates (design §8), so
that the evaluator can evaluate them before the call instead of passing a
thunk.

Evaluation is call by need, and a thunk keeps alive the environment it was
made in. A loop that passes an accumulator on, @go n acc = … go (n - 1)
(acc + 1)@, or that never stops, @f n = f (n + 1)@, would build one thunk
per step, each holding the one before. A function is /strict/ in a
parameter when evaluating its body certainly evaluates that parameter:
evaluating the argument first changes nothing but when the work is done.
An error is a value here, not an exception, so evaluating an argument
early cannot raise an error the program would not have raised; the one
difference is an argument that never finishes, where the program would
have failed with another error first, and the evaluator then stops at a
limit instead. The evaluator also evaluates the components of a number or
of a small tensor passed so (Metron.Eval.evaluated), which the analysis
does not prove are read: one that is never read is computed anyway, or,
if it never finishes, stops at a limit.

The analysis is the classic one over Typed Core: a case evaluates its
scrutinee and what every alternative evaluates; a strict primitive its
operands; a call to a function of known signature, saturated, the
arguments it is strict in. A cycle's members are solved together from the
assumption that they are strict in everything, which is sound (a call
that loops forever evaluates whatever it likes) and finds @f n = f (n +
1)@ strict in @n@. A function value passed as an argument has no known
signature, so @foldl f z@ stays lazy in @z@, as it must.
-}
module Metron.Strictness (
  Signature,
  Signatures,
  strictMarker,
  strictify,
  signatures,
  signatureAt,
) where

import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Text (Text)
import Metron.Core (Hash, Nat (Z), finToInt, vecLength, vecMap, vecToList)
import Metron.TCore (TAlt (..), TTerm (..))
import Metron.Type (numT)

{- | For each parameter of a function of several arguments, in order,
whether a saturated call evaluates it.
-}
type Signature = [Bool]

-- | The signatures known for the variables in scope, by de Bruijn index.
type Known = [Maybe Signature]

-- | The signature of what a reference names: a definition, or a member of a cycle.
type External = Hash -> Maybe Int -> Maybe Signature

-- | A definition's signature, and its members' when it is a cycle.
data Signatures = Signatures {whole :: Maybe Signature, members :: [Maybe Signature]}

{- | The name of the marker around an argument evaluated before its call.
It is no primitive's name and no identifier can spell it, so no source
term carries it; only the evaluator sees marked terms.
-}
strictMarker :: Text
strictMarker = "(evaluated first)"

-- | The signatures of a definition, given those of what it references.
signatures :: External -> TTerm Z -> Signatures
signatures ext = \case
  TCycle _ _ bodies -> Signatures Nothing (cycleSignatures ext [] (vecToList bodies))
  t -> Signatures (signatureOf ext [] t) []

-- | The signature a reference to a definition finds.
signatureAt :: Signatures -> Maybe Int -> Maybe Signature
signatureAt s = \case
  Nothing -> s.whole
  Just i -> case drop i s.members of
    m : _ -> m
    [] -> Nothing

-- | A term with the arguments its calls certainly evaluate marked.
strictify :: External -> TTerm Z -> TTerm Z
strictify ext = mark ext []

-- The members of a cycle, solved together from all-strict down.
cycleSignatures :: External -> Known -> [TTerm m] -> [Maybe Signature]
cycleSignatures ext env bodies = solve (map (fmap (map (const True)) . signatureOf ext unknown) bodies)
 where
  unknown = map (const Nothing) bodies ++ env
  solve sigs =
    let sigs' = map (signatureOf ext (sigs ++ env)) bodies
     in if sigs' == sigs then sigs else solve sigs'

-- | The signature of a function term: a chain of lambdas, under any type abstractions.
signatureOf :: External -> Known -> TTerm m -> Maybe Signature
signatureOf ext env = \case
  TTyLam _ _ b -> signatureOf ext env b
  TLam _ _ b -> Just (chain 1 (Nothing : env) b)
  _ -> Nothing
 where
  chain :: Int -> Known -> TTerm k -> Signature
  chain k env' = \case
    TLam _ _ b -> chain (k + 1) (Nothing : env') b
    body ->
      let d = demanded ext env' body
       in [IntSet.member (k - 1 - i) d | i <- [0 .. k - 1]]

-- | The variables evaluating a term to a value certainly evaluates.
demanded :: External -> Known -> TTerm m -> IntSet
demanded ext env = \case
  TVr i -> IntSet.singleton (finToInt i)
  t@TApp{} -> call t
  t@TTyApp{} -> call t
  TPrimApp p _ args
    | p == strictMarker || p `elem` strictPrimitives ->
        foldMap (demanded ext env) args
    | p `elem` ["and", "or"] -> foldMap (demanded ext env) (take 1 args)
    | otherwise -> IntSet.empty
  TLet _ _ e b ->
    let db = demanded ext (signatureOf ext env e : env) b
        rest = below 1 db
     in if IntSet.member 0 db then rest <> demanded ext env e else rest
  TCase s _ alts ->
    demanded ext env s
      <> meet
        [ below k (demanded ext (replicate k Nothing ++ env) b)
        | TAlt _ bs b <- alts
        , let k = vecLength bs
        ]
  TPow t _ -> demanded ext env t
  TProj t _ -> demanded ext env t
  TSample _ a -> demanded ext env a
  _ -> IntSet.empty
 where
  call t =
    let (h, args) = spine t []
        fromHead = case h of
          TLam{} -> IntSet.empty
          _ -> demanded ext env h
     in fromHead
          <> foldMap
            (demanded ext env . snd)
            (filter fst (zip (strictArgs ext env h args) args))
  meet = \case
    [] -> IntSet.empty
    s : ss -> foldr IntSet.intersection s ss

-- | Mark the strict arguments of every saturated call of known signature.
mark :: External -> Known -> TTerm m -> TTerm m
mark ext env = \case
  t@TApp{} -> markCall t
  t@TTyApp{} -> markCall t
  TLam h ty b -> TLam h ty (mark ext (Nothing : env) b)
  TLet h sc e b -> TLet h sc (mark ext env e) (mark ext (signatureOf ext env e : env) b)
  TCase s ty alts ->
    TCase
      (mark ext env s)
      ty
      [ TAlt c bs (mark ext (replicate (vecLength bs) Nothing ++ env) b)
      | TAlt c bs b <- alts
      ]
  TPrimApp p ty args -> TPrimApp p ty (map (mark ext env) args)
  TCon c ty args -> TCon c ty (map (mark ext env) args)
  TPow t n -> TPow (mark ext env t) n
  TSample l a -> TSample l (mark ext env a)
  TPack ax ty ts -> TPack ax ty (map (mark ext env) ts)
  TProj t i -> TProj (mark ext env t) i
  TTyLam v k b -> TTyLam v k (mark ext env b)
  TCycle vars hb bodies ->
    let sigs = cycleSignatures ext env (vecToList bodies)
     in TCycle vars hb (vecMap (mark ext (sigs ++ env)) bodies)
  t -> t
 where
  markCall t =
    let (h, args) = spine t []
     in rebuild (reverse (strictArgs ext env h args)) t
  -- The spine again, its arguments marked, flags from the last argument back.
  rebuild :: [Bool] -> TTerm m -> TTerm m
  rebuild flags = \case
    TApp f a -> case flags of
      fl : rest -> TApp (rebuild rest f) (wrap fl (mark ext env a))
      [] -> TApp (rebuild [] f) (mark ext env a)
    TTyApp f x -> TTyApp (rebuild flags f) x
    h -> mark ext env h
  wrap strict a
    | strict && not (cheap a) = TPrimApp strictMarker numT [a]
    | otherwise = a
  -- Already a value, or no work to save.
  cheap = \case
    TLit{} -> True
    TLam{} -> True
    TPrimApp p _ _ -> p == strictMarker
    _ -> False

-- | Which of a call's arguments it evaluates: none unless saturated.
strictArgs :: External -> Known -> TTerm m -> [TTerm m] -> [Bool]
strictArgs ext env h args = case headSignature of
  Just sig | length args >= length sig -> take (length args) (sig ++ repeat False)
  _ -> map (const False) args
 where
  headSignature = case h of
    TVr i -> case drop (finToInt i) env of
      known : _ -> known
      [] -> Nothing
    TRef r mi _ -> ext r mi
    _ -> signatureOf ext env h

-- | A call's head and its arguments, type applications passed over.
spine :: TTerm m -> [TTerm m] -> (TTerm m, [TTerm m])
spine t acc = case t of
  TApp f a -> spine f (a : acc)
  TTyApp f _ -> spine f acc
  _ -> (t, acc)

-- | Indices under k more binders, seen from outside them.
below :: Int -> IntSet -> IntSet
below k s = IntSet.fromDistinctAscList [j - k | j <- IntSet.toAscList s, j >= k]

{- | The primitives that evaluate every operand. Any other is assumed to
evaluate none, which is always sound.
-}
strictPrimitives :: [Text]
strictPrimitives =
  [ "add"
  , "sub"
  , "neg"
  , "abs"
  , "emul"
  , "ediv"
  , "div"
  , "outer"
  , "dot"
  , "eq"
  , "ne"
  , "lt"
  , "le"
  , "gt"
  , "ge"
  , "not"
  , "floor"
  , "ceil"
  , "round"
  , "sqrt"
  , "exp"
  , "log"
  , "sin"
  , "cos"
  , "tan"
  , "asin"
  , "acos"
  , "atan"
  , "sinh"
  , "asinh"
  , "cosh"
  , "tanh"
  , "atan2"
  , "norm"
  , "mid"
  , "bound"
  , "sd"
  , "seq"
  , "errorOf"
  , "digitsOf"
  , "nextUp"
  , "ulps"
  , "fma"
  , "isNaN"
  , "isInfinite"
  ]
