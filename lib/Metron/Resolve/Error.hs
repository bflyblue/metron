-- | Binding and declaration diagnostics shared by resolution and type-syntax checking.
module Metron.Resolve.Error (
  ResolveError (..),
  renderResolveError,
) where

import Data.Maybe ( fromMaybe )
import Data.Text ( Text )
import Metron.Desugar ( renderDesugarError, DesugarError )
import Metron.Syntax qualified as S
    ( renderSpanError, Name(span, text), Pos(col, line), Span(from) )
import Data.Text qualified as T ( pack )

data ResolveError
  = DuplicateDefinition S.Name
  | Desugar DesugarError
  | {- | A type error in the named definition, at a span when provenance
    could place it.
    -}
    TypeErrorIn S.Name (Maybe S.Span) Text
  | -- | Elaboration produced ill-typed Typed Core: an internal error.
    LintFailure S.Name Text
  | -- | A @ declaration that cannot be entered, at the offending span.
    DataError S.Span Text
  | {- | A signature that cannot be entered or does not hold (design §4.8),
    at a span in the input of the declaration with the given key ('S.declKey').
    -}
    SignatureError Text S.Span Text
  deriving stock (Eq, Show)

-- | Render without source text; "Metron.Driver" renders with the excerpt.
renderResolveError :: ResolveError -> Text
renderResolveError = \case
  DuplicateDefinition n ->
    T.pack (show n.span.from.line)
      <> ":"
      <> T.pack (show n.span.from.col)
      <> ": `"
      <> n.text
      <> "` is defined twice in the same group"
  Desugar e -> renderDesugarError e
  TypeErrorIn n sp msg ->
    S.renderSpanError
      Nothing
      (fromMaybe n.span sp)
      ("in `" <> n.text <> "`: " <> msg)
  LintFailure n msg ->
    "internal error: elaboration of `"
      <> n.text
      <> "` produced ill-typed core: "
      <> msg
  DataError sp msg -> S.renderSpanError Nothing sp msg
  SignatureError _ sp msg -> S.renderSpanError Nothing sp msg
