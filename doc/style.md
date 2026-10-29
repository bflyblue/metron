# Style Guide

Project conventions and rationale. This file is intended for both human
contributors and AI assistants (Claude Code, etc.).

## GHC Extensions

The `common` stanza in the cabal file enables these extensions globally:

- **GHC2024** — the default language, which already includes many modern
  extensions (e.g. `LambdaCase`, `GADTs`, `DataKinds`).
- **DuplicateRecordFields** — allows the same field name across different
  record types. Essential when modelling domains with many similarly-shaped
  records.
- **NoFieldSelectors** — suppresses generation of top-level selector functions
  for record fields, avoiding name clashes in scope.
- **OverloadedRecordDot** — enables `value.field` dot syntax for record
  access, replacing verbose selectors or lens boilerplate.
- **OverloadedStrings** — string literals desugar via `IsString`, avoiding
  explicit `pack` / `fromString` calls for `Text`, `ByteString`, etc.

Together, `DuplicateRecordFields` + `NoFieldSelectors` + `OverloadedRecordDot`
form a cohesive modern records story: define records freely without worrying
about field name collisions, and access fields with dot syntax.

## Cabal Formatting

- Leading-comma style for `build-depends` and `exposed-modules` lists.
- Aligned field values in stanzas.
- Library source lives in `lib/`, executable source in `src/`.

## Preferences

- The language design lives in [doc/design.md](design.md). Code follows it; when
  code and the design disagree, update one or the other deliberately.
- Core is kept deliberately small; [doc/core.md](core.md) says why and how it
  may change. A new Core constructor goes through that document's §7 before
  any code.

_(Add further project-specific preferences here as they develop.)_
