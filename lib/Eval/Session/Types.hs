-- | Session state shared by command orchestration, evaluation, export, and editing.
module Eval.Session.Types (
  Session (..),
  LastExpr (..),
  emptySession,
) where

import Data.Map.Strict ( Map )
import Data.Text ( Text )
import Eval.Codebase ( emptyCodebase, Codebase )
import Eval.Core ( Nat(Z), Term )
import Eval.UnitHint ( Preferences )
import Eval.Eval ( defaultConfig, Config )
import Eval.TCore ( TTerm )
import Eval.Type ( Scheme )
import Data.Map.Strict qualified as Map ( empty )
import Eval.Syntax qualified as S ( rootScope, Decl, Scope )

data Session = Session
  { codebase :: Codebase
  , scratch :: [S.Decl]
  -- ^ pending definitions, oldest first
  , sources :: Map Text Text
  -- ^ the input text each pending definition came from, for error excerpts
  , staging :: Codebase
  -- ^ codebase with the scratch entered on top; what expressions see
  , config :: Config
  -- ^ evaluation settings, changed with @:set@
  , preferred :: Preferences
  -- ^ the codebase's preference texts, evaluated to hints keyed by dimension (design §3.2.12)
  , lastExpr :: Maybe LastExpr
  {- ^ the last expression statement that evaluated, which expressions and
  inspection commands see as @it@ (design §7.3); never stored
  -}
  , scope :: S.Scope
  {- ^ the current namespace, set with @:namespace@, and the @use@s in
  effect (design §7.6); never stored
  -}
  }

{- | An expression as it was checked: its Core, types and Typed Core, and the
codebase it was checked against, whose terms it may reference after the
scratch that defined them has changed.
-}
data LastExpr = LastExpr
  { term :: Term Z
  , schemes :: [Scheme]
  , typed :: TTerm Z
  , base :: !Codebase
  }

emptySession :: Session
emptySession =
  Session
    emptyCodebase
    []
    Map.empty
    emptyCodebase
    defaultConfig
    Map.empty
    Nothing
    S.rootScope
