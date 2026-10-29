-- | User-facing rendering (design §3.2.10, §7.2): values as decimals, and
-- Core terms back to surface syntax for @:view@.
module Eval.Pretty
  ( renderRational
  , renderValue
  , renderNested
  , renderTerm
  , RefNamer
  ) where

import Data.Char (intToDigit)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Eval.Core
import Eval.Dimension (renderUnits)
import Eval.Eval

-- Values ------------------------------------------------------------------------

-- | @renderRational scale r@.
renderRational :: Int -> Rational -> Text
renderRational scale r
  | r < 0 = "-" <> renderRational scale (negate r)
  | otherwise =
      let (whole, frac) = properFraction r :: (Integer, Rational)
          (digits, exact) = fractionDigits scale frac
       in T.pack (show whole)
            <> (if null digits then "" else "." <> T.pack digits)
            <> (if exact then "" else "…")

-- | Up to @n@ decimal digits of a fraction in @[0, 1)@, and whether they are
-- the whole expansion.
fractionDigits :: Int -> Rational -> (String, Bool)
fractionDigits n frac
  | frac == 0 = ("", True)
  | n == 0 = ("", False)
  | otherwise =
      let scaled = frac * 10
          d = floor scaled :: Integer
          rest = scaled - fromInteger d
          (more, exact) = fractionDigits (n - 1) rest
       in (intToDigit (fromInteger d) : more, exact)

-- | Print a value. A tensor with a display unit whose dimension matches
-- prints its magnitudes in that unit (design §3.2.12); otherwise in SI base
-- units. Unit names go through the namer so that a renamed unit prints under
-- its current name.
renderValue :: RefNamer -> Int -> Value -> Either EvalError Text
renderValue namer scale = \case
  VTensor dims d hint buf -> do
    rs <- sequence (V.toList buf)
    let (scaled, units) = case hint of
          Just h
            | h.dim == d, h.factor /= 0 -> (map (/ h.factor) rs, renderHint h)
          _ -> (rs, renderUnits d)
    pure (renderNested (renderRational scale) dims scaled <> (if T.null units then "" else " " <> units))
  VBool True -> Right "true"
  VBool False -> Right "false"
  VClosure _ -> Right "<function>"
  where
    -- Positive exponents first, otherwise in the order the units appeared.
    renderHint h =
      T.unwords
        [ atomName a <> (if k == 1 then "" else "^" <> T.pack (show k))
        | (a, k) <- filter ((> 0) . snd) h.atoms ++ filter ((< 0) . snd) h.atoms
        ]
    atomName = \case
      UnitRef h i -> namer h i
      UnitBase u -> u

-- | Print a flat row-major buffer as nested brackets according to its shape.
renderNested :: (a -> Text) -> [Int] -> [a] -> Text
renderNested showElem dims xs = case dims of
  [] -> case xs of
    x : _ -> showElem x
    [] -> "[]"
  [_] -> brackets (map showElem xs)
  d : rest ->
    let stride = product rest
     in brackets [renderNested showElem rest (take stride (drop (i * stride) xs)) | i <- [0 .. d - 1]]
  where
    brackets ts = "[" <> T.intercalate ", " ts <> "]"

-- Terms --------------------------------------------------------------------------

-- | How to print a reference: the codebase decides between a current name,
-- a stale @name#hash@, and a bare @#hash@ (design §7.2).
type RefNamer = Hash -> Maybe Int -> Text

-- | Print a term as surface syntax, given names for the variables in scope
-- (innermost first). Binder hints become names; de Bruijn indices make
-- shadowing faithful even when hints repeat.
renderTerm :: RefNamer -> Vec n Text -> Term n -> Text
renderTerm namer = go 0
  where
    go :: Int -> Vec m Text -> Term m -> Text
    go prec ctx t = case t of
      Var i -> lookupVar i ctx
      Ref h idx -> namer h idx
      Lit (LTensor [] [r])
        | r < 0 -> paren (prec > 8) (renderRational 20 r)
        | otherwise -> renderRational 20 r
      Lit (LTensor dims rs) -> renderNested (renderRational 20) dims rs
      Lit (LBool True) -> "true"
      Lit (LBool False) -> "false"
      Lam (Hint h) b ->
        let h' = freshen h ctx
         in paren (prec > 0) ("\\" <> h' <> " -> " <> go 0 (VCons h' ctx) b)
      App f a -> paren (prec > 10) (go 10 ctx f <> " " <> go 11 ctx a)
      Let (Hint h) e b ->
        let h' = freshen h ctx
         in paren (prec > 0) ("let " <> h' <> " = " <> go 0 ctx e <> " in " <> go 0 (VCons h' ctx) b)
      If c th el ->
        paren (prec > 0) ("if " <> go 0 ctx c <> " then " <> go 0 ctx th <> " else " <> go 0 ctx el)
      Pow b n -> paren (prec > 9) (go 10 ctx b <> "^" <> T.pack (show n))
      Noise Bound n -> "noise " <> T.pack (show n)
      Noise Stat n -> "gauss " <> T.pack (show n)
      Uncertain k x e ->
        paren (prec > 5) (go 6 ctx x <> (if k == Bound then " ± " else " ±σ ") <> go 6 ctx e)
      Pack ts -> "[" <> T.intercalate ", " (map (go 0 ctx) ts) <> "]"
      Proj b i -> go 11 ctx b <> "." <> T.pack (show i)
      Cycle hints bodies ->
        -- Only reached when a whole cycle is printed; members are normally
        -- viewed one at a time through 'renderTerm' on a body.
        let ctx' = vecAppend (vecMap (\(Hint h) -> h) hints) ctx
         in T.intercalate "; " [h <> " = " <> go 0 ctx' b | (Hint h, b) <- zip (vecToList hints) (vecToList bodies)]
      PrimApp p args -> prim prec ctx p args

    prim :: Int -> Vec m Text -> Text -> [Term m] -> Text
    prim prec ctx p args = case (binary p, args) of
      (Just (sym, lvl, assoc), [a, b]) ->
        let (lp, rp) = case assoc of
              L -> (lvl, lvl + 1)
              R -> (lvl + 1, lvl)
              N -> (lvl + 1, lvl + 1)
         in paren (prec > lvl) (go lp ctx a <> " " <> sym <> " " <> go rp ctx b)
      _ -> case (p, args) of
        -- `-3` reads back as the constant minus three (core.md §6), so the
        -- primitive applied to a constant keeps its name.
        ("neg", [a@(Lit _)]) -> paren (prec > 10) ("neg " <> go 11 ctx a)
        ("neg", [a]) -> paren (prec > 8) ("-" <> go 9 ctx a)
        (_, []) -> p
        _ -> paren (prec > 10) (T.unwords (p : map (go 11 ctx) args))

    paren b s = if b then "(" <> s <> ")" else s

    -- A hint that is already in scope would capture an outer variable the
    -- body may still refer to, so the printed binder gets a prime (or a
    -- name if the hint is blank, or one the desugarer made up for a section
    -- or a composition, `§s0`, which is not an identifier). De Bruijn
    -- indices make the term itself unambiguous; this keeps the printed text
    -- so.
    freshen :: Text -> Vec m Text -> Text
    freshen h ctx
      | T.null h || "§" `T.isPrefixOf` h = freshen "x" ctx
      | h `elem` vecToList ctx = freshen (h <> "'") ctx
      | otherwise = h

    lookupVar :: Fin m -> Vec m Text -> Text
    lookupVar i ctx = case (i, ctx) of
      (FZ, VCons x _) -> x
      (FS j, VCons _ xs) -> lookupVar j xs

data Assoc = L | R | N

-- | Operator symbol, precedence level (as in design §2.5) and associativity
-- for the binary primitives.
binary :: Text -> Maybe (Text, Int, Assoc)
binary = \case
  "outer" -> Just ("*", 7, L)
  "dot" -> Just ("·", 7, L)
  "wedge" -> Just ("∧", 7, L)
  "emul" -> Just ("⊙", 7, L)
  "ediv" -> Just ("⊘", 7, L)
  "div" -> Just ("/", 7, L)
  "add" -> Just ("+", 6, L)
  "sub" -> Just ("-", 6, L)
  "eq" -> Just ("==", 4, N)
  "ne" -> Just ("/=", 4, N)
  "lt" -> Just ("<", 4, N)
  "le" -> Just ("<=", 4, N)
  "gt" -> Just (">", 4, N)
  "ge" -> Just (">=", 4, N)
  "and" -> Just ("&&", 3, R)
  "or" -> Just ("||", 2, R)
  "to" -> Just ("to", 1, N)
  _ -> Nothing
