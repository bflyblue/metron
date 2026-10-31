-- | Evaluate stored unit preferences after codebase changes.
module Metron.Session.Preferences (
  preferenceHint,
  refreshPreferences,
) where

import Data.Text ( Text )
import Metron.Codebase ( Codebase(preferences) )
import Metron.Compile ( evalValue )
import Metron.Dimension ( Dim )
import Metron.UnitHint ( UnitHint(dim) )
import Metron.Eval ( Config, Value(VTensor, VUnit) )
import Metron.Parser ( parseExpr )
import Metron.Session.Types ( Session(staging, preferred, config) )
import Data.Map.Strict qualified as Map ( fromList )
import Metron.Syntax qualified as S
    ( rootScope, Expr(span, Expr), Node(UnitSyntax) )
import Data.Set qualified as Set ( toList )

{- | Evaluate a preference text (@km/h@) to the unit it names and the exact
dimension it applies to. It must be a scalar with a display unit.
-}
preferenceHint :: Config -> Codebase -> Text -> Either Text (Dim, UnitHint)
preferenceHint cfg cb text = do
  e <- parseExpr text
  (_, v) <- evalValue cfg S.rootScope cb text (S.Expr e.span (S.UnitSyntax e))
  -- A preference is a unit (design §3.10, U7), not an amount of one.
  case v of
    VUnit (VTensor [] d (Just h) _) | h.dim == d -> Right (d, h)
    VUnit _ ->
      Left ("`" <> text <> "` has no unit to prefer; write one, as in :prefer km/h")
    VTensor{} ->
      Left
        ( "a preference is a unit, not an amount: write it as one, as in :prefer km/h, not `"
            <> text
            <> "`"
        )
    _ -> Left ("a preference must be a unit expression, not `" <> text <> "`")

{- | Recompute the evaluated preferences from the codebase's texts, as after a
load or a change. A text that no longer evaluates (its unit was unnamed) is
dropped from the evaluated set but kept in the codebase.
-}
refreshPreferences :: Session -> Either Text Session
refreshPreferences session =
  let hints =
        [ (d, h)
        | t <- Set.toList session.staging.preferences
        , Right (d, h) <- [preferenceHint session.config session.staging t]
        ]
   in Right session{preferred = Map.fromList hints}
