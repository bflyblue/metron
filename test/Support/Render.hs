-- | Deliberately simple rendering for semantic evaluator tests; not a user-facing printer.
module Support.Render (render) where

import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Metron.Affine
import Metron.Builtin
import Metron.Eval
import Metron.Type (conText)

{- | A plain rendering for tests. Forces every element. Exact magnitudes
print as @n/d@ in base units, affine ones as an approximate @mid±r@, and
dimensions are omitted; decimal output with units is "Metron.Pretty"'s job.
-}
render :: Value -> Either EvalError Text
render = \case
  VTensor dims _ _ buf -> do
    rs <- sequence (V.toList buf)
    pure (nested dims rs)
  VPoint dims _ _ buf -> ("point " <>) . nested dims <$> sequence (V.toList buf)
  VChart _ -> Right "<chart>"
  VBool True -> Right "true"
  VBool False -> Right "false"
  VData c fields -> do
    parts <- mapM (>>= render) fields
    pure
      ( case c of
          TupleC _ -> "(" <> T.intercalate ", " parts <> ")"
          _ -> T.unwords (conText c : parts)
      )
  VClosure _ -> Right "<function>"
  VTyAbs{} -> Right "<polymorphic value>"
  VUnit v -> ("unit " <>) <$> render v
  -- The affine backend has no copies, so never a mixture.
  VMixture _ -> Right "<mixture>"
 where
  magnitude = \case
    Exact r -> frac r
    m ->
      let c = collapse m
       in tshow (fromRational c.mid :: Double)
            <> "±"
            <> tshow (fromRational (c.bound + sigmaOf 6 c) :: Double)
  frac r
    | denominator r == 1 = tshow (numerator r)
    | otherwise = tshow (numerator r) <> "/" <> tshow (denominator r)
  nested dims rs = case dims of
    [] -> maybe "[]" magnitude (headMay rs)
    [_] -> brackets (map magnitude rs)
    d : rest ->
      let stride = product rest
       in brackets [nested rest (take stride (drop (i * stride) rs)) | i <- [0 .. d - 1]]
  brackets xs = "[" <> T.intercalate ", " xs <> "]"
  headMay = \case
    x : _ -> Just x
    [] -> Nothing

tshow :: (Show a) => a -> Text
tshow = T.pack . show
