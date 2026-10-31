-- | Run elaboration and independent Core lint, preserving both results and their distinct errors.
module Eval.Check (
  CheckedCore (..),
  CheckError (..),
  checkCore,
) where

import Data.Bifunctor ( first )
import Data.Text ( Text )
import Eval.Core ( Nat(Z), Term )
import Eval.Infer
    ( TypeLookup, elaborateClosedWith, Annotations, TypeError )
import Eval.TCore ( lintClosed, TTerm )
import Eval.Type ( Scheme )

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
