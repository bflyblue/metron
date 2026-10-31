-- | Run elaboration and independent Core lint, preserving both results and their distinct errors.
module Metron.Check (
  CheckedCore (..),
  CheckError (..),
  checkCore,
) where

import Data.Bifunctor ( first )
import Data.Text ( Text )
import Metron.Core ( Nat(Z), Term )
import Metron.Infer
    ( TypeLookup, elaborateClosedWith, Annotations, TypeError )
import Metron.TCore ( lintClosed, TTerm )
import Metron.Type ( Scheme )

data CheckedCore = CheckedCore
  { inferred :: [Scheme]
  , typed :: TTerm Z
  , linted :: [Scheme]
  }

data CheckError = InferenceError TypeError | CoreLintError Text

checkCore :: Annotations -> TypeLookup -> Term Z -> Either CheckError CheckedCore
checkCore annotations look term = do
  (inferred, typed) <- first InferenceError (elaborateClosedWith annotations look term)
  linted <- first CoreLintError (lintClosed look typed)
  pure CheckedCore{inferred, typed, linted}
