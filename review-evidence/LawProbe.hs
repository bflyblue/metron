{-# LANGUAGE OverloadedStrings #-}

import Metron.Affine
import Metron.Core (NudgeKind (Stat))

main :: IO ()
main = do
  let x = uncertain Stat (Tagged "x" 0) (Exact 0) (Exact 1)
      y = uncertain Stat (Tagged "y" 0) (Exact 0) (Exact 1)
      z = mulM 24 x y
      sk k = case scaleM 24 k z of
        Affine _ _ _ s -> s
        _ -> mempty
      a = sk 1000
      b = sk 1
      c = sk 1
  print ((a <> b) <> c)
  print (a <> (b <> c))
  print (((a <> b) <> c) == (a <> (b <> c)))
