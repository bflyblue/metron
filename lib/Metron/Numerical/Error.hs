-- | Arithmetic failures shared by the scalar implementations.
module Metron.Numerical.Error (ArithError (..)) where

import Data.Text (Text)

data ArithError
  = DivideByZero
  | -- | a function applied outside its domain
    Domain Text
  deriving stock (Eq, Show)
