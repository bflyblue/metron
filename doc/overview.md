# Metron overview

This is the entry point to the project for a new reader, human or agent. It says what Metron is for, the principles it keeps, how a line of input becomes a printed value, where each part lives in the code, what is built, and what the words mean. The rules themselves are in [design.md](design.md). This document points at them and does not repeat them.

## Contents

1. Purpose and goals
2. Principles
3. A first session
4. The pipeline
5. Module map
6. Feature map
7. Glossary
8. Other documents

## 1. Purpose and goals

Metron is a small, pure calculator language that understands units and tracks error. Two uses drive every priority (design §1.1):

- **Daily calculation.** A command-line calculator to type `metron '5 km/h to m/s'` into every day. It must give exact answers where it can, handle units without ceremony, and start at once.
- **iapetus.** The owner's orbital-mechanics project needs a library of functions that carry units, work on vectors and matrices, and track how approximation error and input uncertainty build up through user code. The library needs stable versions of its definitions over years.

Metron is a proof of concept, written in Haskell. The language and the store format can change, and a store of an older format is refused, not migrated.

## 2. Principles

- **Honest error bounds.** An approximate number is an affine form: a midpoint plus named error terms, each a guaranteed bound or a standard uncertainty. Printing never shows a digit that is not correct, a σ never prints as a bound, and a comparison that the error does not decide is an error, not a guess (design §3.2).
- **Units as a type-level dimension.** A dimension is part of the static type, so `1 m + 1 s` is a type error before anything runs. Units are syntax that scale amounts and choose how values print. Points (a temperature, an instant, a position) are a separate type from amounts (design §3.10, §4.1).
- **A content-addressed codebase.** A definition's identity is the SHA-256 hash of its desugared, untyped Core. Names are labels that point at hashes, so versioning is relabelling, as in Unison (design §6, §7).
- **Explicit conversions.** Nothing converts silently. `to` chooses a display unit, re-expresses a point on another chart, or turns an amount onto a chart's axes. Points on two frames never mix until one is converted (design §3.10, F10).
- **Pure and lazy.** Expressions have no effects and bindings are immutable, with Haskell-like call-by-need semantics (design §8).

## 3. A first session

These lines run under `metron --no-codebase` and print what is shown. Start the REPL with `nix run . -- --no-codebase`.

```
> 5 km/h to m/s
1.3888888888888888888… m s^-1
> 1/3 * 3
1
> 1 m + 1 s
error at 1:7
  1 m + 1 s
        ^^^
  expected Num m, got Num s: dimensions differ by m/s
> let x = 5 ± 0.1 in x - x
0
> (5 ± 0.1) * (5 ± 0.1)
25 ± 1
> 2 ±σ 0.1
2.0 ±σ 0.1
> sin (90 deg)
1.0000000000000000000…
> 20 degC to degF
68 degF
```

The `…` means that the printed digits are all correct and more follow. `x - x` is exactly `0` because both operands carry the same named error term. `±σ` is a standard uncertainty and always prints with its `σ`.

Under the double backend (`metron --no-codebase --backend double`), the same language runs in IEEE doubles with an error estimate, and with `:set samples N` it runs N copies for a Monte Carlo sample:

```
> 0.1 + 0.2
0.30000000000000004 ± 5.0e-17 (bound)
> :set samples 1000
> let x = 1 ±σ 0.1
> if x > 0.9 then 1 else 2
1 (Monte Carlo: mean 1.144, sd 0.3513, 1000 samples)
note: the branch at `if x > 0.9` goes both ways across 1000 samples (by the declared uncertainty):
  then   856   ← taken (the nominal branch)
  else   144
```

## 4. The pipeline

A line of input goes through these stages. Each stage reads only the output of the one before it (design §1.4).

1. **Lexer** (`Metron.Lexer`). The text is NFC-normalised, confusable characters are folded, and unicode spellings become the same tokens as their ASCII forms. A layout pass turns newlines and indentation into statement separators and blocks (design §2.1, §2.8).
2. **Parser** (`Metron.Parser`). Megaparsec builds the surface AST of `Metron.Syntax`, with a source span on every node (design §2.5 to §2.7).
3. **Name resolution and desugaring** (`Metron.NameResolution`, `Metron.Desugar`). Names resolve through local binders, the current namespace, the `use`d namespaces, the root and the stored uses. All sugar goes: operators become saturated primitive applications, the quantity rule becomes `scale` or `pointOn`, records become `case`. The result is Core plus a provenance table that maps each node to its source span (design §2.9, §4.7, §7.6).
4. **Binding groups and hashing** (`Metron.Resolve`, `Metron.Hash`). The statements of one input form a binding group. It is split into strongly connected components, each component is hashed (a recursive one as a `Cycle`), and nothing is entered unless the whole group checks (design §6).
5. **Type inference** (`Metron.Infer`). Hindley-Milner with kinded variables: types, lengths, shapes, dimensions (Kennedy's unification), axis slots, frames and spaces. Shape concatenation, ranks and equality are pending constraints. Inference also elaborates (design §4).
6. **Typed Core** (`Metron.TCore`). Core with every binder typed and every polymorphic use applied explicitly, in the manner of System F (design §5.3).
7. **Lint** (`Metron.TCore.lintClosed`, run by `Metron.Check`). An independent type checker re-checks every elaborated term before it is stored or run. A lint failure is an internal error (doc/core.md §6).
8. **Evaluation** (`Metron.Eval`). An environment-passing, call-by-need interpreter over Typed Core, generic over its scalar domain (`Metron.Scalar`). Two backends plug in: `affine` (`Metron.Affine`, exact rationals and affine error forms, the default) and `double` (`Metron.Double`, IEEE doubles with a running error bound, or N copies under stochastic rounding and Monte Carlo draws). Resource limits bound every evaluation (design §8).
9. **Printing** (`Metron.Pretty`). Values print with only correct digits and their display units. Core prints back as source for `:view` and `:edit` (design §3.2.10, §3.2.12).

Beside the pipeline sits **the codebase** (`Metron.Codebase`): terms by hash, names as labels, their history, and the declared types. **The store** (`Metron.Store`) keeps it on disk as one file per term and an append-only log of label events. A new store is seeded with the standard library (`Metron.Prelude`) (design §7).

## 5. Module map

Every module under `lib/Metron`, with its job and the design section that governs it. The executable's entry point is `src/Main.hs` (command-line flags, design §7.4). Another branch is reorganising some modules and test files. After it merges, check this table against `ls lib/Metron`.

| Module | Responsibility | Design |
|---|---|---|
| `Metron.Lexer` | Tokens, unicode mapping, NFC and confusables, the layout pass | §2.1, §2.8 |
| `Metron.Unicode` | Unicode entry by name in the REPL (`\mu` TAB) | §2.8, §7.3 |
| `Metron.Syntax` | The surface AST with source spans, paths and scopes | §2 |
| `Metron.Parser` | Megaparsec parser for programs, expressions and types | §2.5 to §2.7 |
| `Metron.Desugar` | Surface AST to Core, the quantity rule, provenance, ascription markers | §2.9, §4.7, §4.8 |
| `Metron.NameResolution` | Names through scopes and namespaces, shortest spellings for printing | §7.6 |
| `Metron.Core` | Core: the well-scoped untyped term language, `alphaEq`, references | §5.1, doc/core.md |
| `Metron.TCore` | Typed Core and its independent `lint` | §5.3, doc/core.md |
| `Metron.Primitive` | Primitive arities and base units | §4.3, §5.1 |
| `Metron.Primitive.Types` | Primitive type schemes, computed for literal arguments | §4.2, §4.3 |
| `Metron.Builtin` | `Bool`, tuples, lists and the minted axis, space and frame types, by hash | §2.3, §3.9, §3.10 |
| `Metron.Type`, `Metron.Type.Base` | Kinds, types, shapes, frames, spaces, schemes, substitution, rendering | §4.1 |
| `Metron.Type.Syntax` | Written types: signatures, `data` and `space` declarations, queries | §2.3, §4.8 |
| `Metron.Type.Match` | One-way matching: is a signature an instance of a scheme | §4.8 |
| `Metron.Dimension` | Dimensions as a free abelian group, Kennedy's unifier, dimension printing | §4.1, §4.4 |
| `Metron.Infer` | Inference and elaboration to Typed Core in one pass, readings of `to` and quantities | §4.2, §4.5 |
| `Metron.Check` | Runs elaboration, then lint, and keeps both results | §5.3 |
| `Metron.Resolve`, `Metron.Resolve.Error` | Binding groups: dependency analysis, cycles, inference, entry into the codebase | §6.2, §6.3, §7.1 |
| `Metron.Encode` | Byte-level encoding pieces and the encoding of declared types | §6.1 |
| `Metron.Hash` | Canonical encoding of terms, SHA-256, the storage encoding | §5.2, §6 |
| `Metron.Codebase` | Terms, names, history, types, constructors, fields, flags, signatures | §7.1, §7.2 |
| `Metron.Update` | Propagation of new versions to dependents, re-stamping on rename | §7.2, §7.5 |
| `Metron.Store` | The store on disk: format, seeding, loading, sync, merge | §7.4 |
| `Metron.Prelude` | The standard library as source, by namespace | §7.7 |
| `Metron.Source` | Stored definitions back to source: `:view`, `:edit`, `:export` | §7.3, §7.4 |
| `Metron.Edit` | The `:edit` round trip: plan and reconcile, all or nothing | §7.3 |
| `Metron.Session.Types`, `Metron.Session.Names`, `Metron.Session.Preferences` | Session state, command arguments and label moves, unit preferences | §7.3, §7.6, §3.2.12 |
| `Metron.Command` | Command names and help text, shared by help and completion | §7.3 |
| `Metron.Driver` | Feeds input through the pipeline; the commands; scratch, `:add`, `:update` | §7.3, §7.5 |
| `Metron.Repl` | The REPL's pure parts: completion, colour, continuation lines | §7.3 |
| `Metron.Compile` | Checks and evaluates one expression with diagnostics, batches | §4.7, §8 |
| `Metron.Eval` | The evaluator: values, closures, charts, mixtures, splits | §8, §3.8 |
| `Metron.Strictness` | Which arguments a call certainly evaluates | §8 |
| `Metron.Limits` | Resource limits, the step and depth budget, paths | §8.1 |
| `Metron.Scalar` | The scalar class a backend implements, settings, backend-only built-ins | §8.2 |
| `Metron.Affine` | The affine backend: exact rationals and affine forms, the non-linear mark | §3.2 |
| `Metron.Numerical.Approx` | Elementary functions in fixed point with rigorous error bounds | §3.2.8 |
| `Metron.Numerical.Linear` | Determinant, inverse, matrix exponential, Cholesky over magnitudes | §3.3, §3.4 |
| `Metron.Double` | The double backend: IEEE values, running bound, copies, Monte Carlo draws | §8.2 |
| `Metron.Batch` | The double backend's copies in parallel batches (`:set cores`) | §8.2 |
| `Metron.Remark` | Records of the copies at each branch point | §8.2 |
| `Metron.Branch` | The branch table as text | §8.2 |
| `Metron.Needs` | The check before running: built-ins a backend lacks | §8.2 |
| `Metron.UnitHint` | Display-unit algebra and cancellation | §3.2.12 |
| `Metron.Pretty` | Printing values, budgets and Core as source | §3.2.10, §7.2 |

The test suite is in `test/`. Its groups follow the design's sections, and each design subsection names the groups that test it under **Tested by:**.

## 6. Feature map

Status: **built** (in the code and tested), **designed** (decided in design.md, not built), **open** (not decided).

| Feature | Status | Design |
|---|---|---|
| Exact rational arithmetic, exact while small | built | §3.2, §3.2.8 |
| Static dimensions, Kennedy unification, angle as a dimension | built | §3.2.11, §4.1, §4.4 |
| Units as syntax, the implicit one, the quantity rule | built | §2.6, §3.10 Part U |
| Display units, `to`, `:prefer` | built | §3.2.12 |
| Affine error forms: bound and statistical nudges, `±`, `±σ`, `noise`, `gauss`, `#label` | built | §3.2 to §3.2.5 |
| The non-linear mark, re-judged at each operation | built | §3.2 |
| `:budget`, `:exact`, `:covariance` | built | §3.2.6, §3.2.10, §3.5 |
| Working precision, fixed-point series, linear results held | built | §3.2.8 |
| Comparison at a stated sigma, `mid`, `bound`, `sd` | built | §3.2.9 |
| Tensors of any rank, the products, `contract`, `permute`, `slice`, `timap` | built | §3.3, §4.2 |
| Rotations from bivectors, `expm`, the `linalg` constructors | built | §3.3 |
| Covariance, `cholesky`, `crossCovariance`, joint covariance in blocks (`Cov2`) | built | §3.5, §3.7.2 |
| Points, charts, spaces and frames, turned and moving charts | built | §3.6, §3.8, §3.10 Part F |
| Axis sets as types | built | §3.9 |
| Data types, records, `case`; `Bool`, tuples and lists as structural data | built | §2.3 |
| Signatures, ascriptions, required `forall` | built | §4.8 |
| Content hashing, cycles | built | §5.2, §6 |
| Scratch, `:add`, `:update`, propagation, history | built | §7.1 to §7.5 |
| The store on disk, `--merge`, `:export` | built | §7.4 |
| Namespaces and `use` | built | §7.6 |
| The standard library by namespace; `astro` constants, Kepler and manoeuvres | built | §7.7 |
| `:edit`, the editor round trip | built | §7.3 |
| REPL aids: completion, unicode entry, colour, continuation lines, the echo | built | §7.3 |
| Resource limits | built | §8.1 |
| Backends `affine` and `double`; samples, Monte Carlo, branch tables, mixtures, parallel batches | built | §8.2 |
| The check before running (`needs`) | built | §8.2 |
| Mixed-dimension matrices in the type system (Hart's route) | designed, waits for its escalation signal | §3.7.1 |
| Named positions, `axes x y z` | designed | §3.9 |
| The second `astro` build: time, frames, geodesy, then Lambert | designed | §7.7, §10 |
| A `brick` front end, `metron --tui` | designed | §10 |
| Dictionary passing for unresolved constraints | designed | §4.2, §5.3 |
| Matrix work over the generic scalar type, the affine fused dot product | open | §10 |
| `:trace`, `samplesOf`, Monte Carlo quantiles | open | §8.2, §10 |
| Precision refinement for undecidable comparisons, lazy precision | open | §3.2.9, §11 |
| Curvilinear charts, a frame per item of data | open | §11 |

§10 of the design lists all pending work, and §11 lists the questions the owner has not decided.

## 7. Glossary

Terms in alphabetical order. The design section in parentheses has the rules.

- **Affine form.** An approximate number `mid + c₁·e₁ + … + cₖ·eₖ (± slack)`: an exact rational midpoint, rational coefficients on named unknowns (nudges), and an anonymous leftover radius. Linear operations combine coefficients exactly, so `x - x` is `0` (§3.2).
- **Amount.** A quantity of a vector space: `Num δ`, `Vec n δ`, `Tensor s δ`. Amounts add, scale and multiply. Contrast with point (§3.6).
- **Axis set, axes.** The type-level name of the axes a vector is measured along, beside each length in a shape: anonymous (`Vec 3`), named (`Vec lvlh`), or a variable. Mixing axes of two frames is a type error (§3.9).
- **Backend.** The scalar arithmetic the evaluator runs with, and the built-ins that belong to it: `affine` (the default) or `double`. A stored definition names no backend (§8.2).
- **Binding group.** The statements of one input (a line, a file, a multi-line entry). They can refer to each other in any order. Nothing from a group is stored unless all of it checks (§2.2, §6.3).
- **Bound nudge.** A nudge whose unknown lies in `[-1, 1]`, guaranteed. Made by rounding, series truncation, linearisation remainders and `±` (§3.2).
- **Branch table.** Under `samples N`, the table printed at an `if` or `case` whose copies choose different alternatives: one row per alternative with its count of copies, the nominal branch marked (§8.2).
- **CESTAC.** Stochastic arithmetic: N copies of a computation, each rounding every operation up or down at random. Their spread estimates the digits that survive rounding. The method behind CADNA, used by the double backend with `samples N` (§8.2).
- **Chart.** A value that puts coordinates on a space: a step unit, an origin and an orientation (a list of generators). `20 degC` is the point 20 steps up `degC` from its origin. A chart with parameters is a moving chart (§3.6, §3.8).
- **Compaction.** Folding the smallest bound coefficients of a form with more than 64 nudges into slack (§3.2.7).
- **Copies.** Under the double backend with `samples N`, the N versions of each number computed in lockstep, each with its own rounding and its own draws (§8.2).
- **Core, Typed Core.** Core is the small untyped language that desugaring produces and that is hashed. Typed Core is Core after inference, explicitly typed, linted and run (§5, doc/core.md).
- **Cores (`:set cores K`).** How many parallel batches the copies run in. Results are identical for every K (§8.2).
- **`Diff`.** `Diff c` is the type of the amount between two points on frame `c`: the space's dimension along the frame's axes. `Diff degC` is `Num K`, `Diff lvlh` is `Vec lvlh m` (§3.10, F4).
- **Dimension.** The static part of a quantity's type, a product of powers of the base dimensions (length, mass, time, current, temperature, amount of substance, luminous intensity, and plane angle) and variables (§3.2.11, §4.1).
- **Display unit.** The unit a value prints in, carried beside the value and never part of its type or hash (§3.2.12).
- **Exact while small.** An exact result stays an exact rational while its numerator and denominator are short (224 digits at the default precision). A longer one is rounded to working precision, the rounding a fresh bound nudge (§3.2.8).
- **Frame.** The type-level identity of a chart: which origin and which axes, with no numbers. `Point degC` is typed by the frame `degC`. A chart with only a new step shares its parent's frame (§3.10, F3).
- **Generator, bivector.** An antisymmetric matrix: the oriented plane of a rotation, with the angle as its size. `expm` turns it into the rotation matrix, and negation inverts it exactly (§3.3, §3.8).
- **Label.** A name in the codebase that points at a reference: a definition, a type, a constructor or a field. Also `#label` after `±`, which names a shared unknown (§3.2.4, §7.1).
- **Limits.** Per-session bounds on an evaluation: `memory`, `steps`, `depth`, `digits`, `components`, `outcomes` and `time`. A limit reached is an ordinary error that names its setting, and a limit never changes a value or a hash (§8.1).
- **Lint.** The independent type checker over Typed Core, in the role of GHC's Core Lint (§5.3).
- **Mixture.** Under Monte Carlo, a value whose copies reached different constructors: a set of options, each a group of copies with its own value. It prints as a table of outcomes (§8.2).
- **Monte Carlo draws.** Under the double backend with `samples N`, each copy draws every declared standard uncertainty from a normal distribution, keyed by the nudge's identity, the copy and the seed. The copies then form a sample of the result (§8.2).
- **`needs`.** The set of backend-only built-ins a definition uses, directly or through its dependencies. It is memoised by hash, and an input whose needs the current backend lacks is refused before it runs (§8.2).
- **Nominal branch, nominal value.** Under the double backend, the alternative and the value that the plain IEEE computation takes, as a ported Haskell formula would (§8.2).
- **Non-linear mark.** A warning on a value whose second-order statistical term is more than `:set nonlinear` percent (default 1) of its first-order σ. A mean and a σ do not describe such a value, so comparisons, `mid`, `sd` and the covariances refuse it (§3.2).
- **Nudge.** A named unknown in an affine form, with a kind (bound or statistical) and a content-addressed identity, so the same unknown cancels wherever it meets itself (§3.2, §3.2.4).
- **Owner stamp.** The full path of the definition that a `±`, `noise` or `gauss` is written in, kept in the term so that two identical measurements in two definitions are independent. Renaming such a definition re-hashes it (§3.2.4, §7.2).
- **Point.** A position in an affine space: a temperature, an instant, a place. Two points subtract to an amount (`.-`), and an amount added to a point gives a point (`.+`). Points never add (§3.6).
- **Propagation.** Rewriting the dependents of a re-bound name to the new version, re-checking each, on `:update` or `:upgrade` (§7.5).
- **Quantity rule.** A literal followed by unit syntax is an amount (`3 m`), and a literal followed by a chart is a point (`20 degC`) (§2.6, §3.10 U4).
- **Role.** Internal to the type checker: whether a quantity type is an amount or a unit. Roles cannot be written in a type, and there is no role polymorphism in the language (§3.10 U9).
- **Scratch.** Pending definitions: checked, hashed and usable, but not stored until `:add` or `:update` (§7.5).
- **Slack.** The anonymous worst-case radius of an affine form. It never cancels and never shrinks (§3.2.7).
- **Space.** A declared set of points that convert among each other, with the type of its amounts: `space ITS90 = Num K`, `space GCRS = Vec 3 m`. Points of two spaces never meet (§3.10, F2).
- **Statistical nudge.** A nudge with mean 0 and standard deviation 1 and no hard limit, made by `±σ` and `gauss`. Statistical nudges propagate to first order, and a σ never becomes a bound (§3.2).
- **Steps per path.** The `steps` limit counts along each copy's path through the branch points, so that an input is accepted or refused alike for every `cores` setting (§8.1).
- **Stored use.** A `use` kept in the codebase (six by default: `std`, `linalg`, `si`, `time`, `angle`, `temperature`), resolved after the root (§7.6, §7.7).
- **Unit.** Syntax that names a scale: a declared unit name, or a product, quotient or power of them. A unit after a literal scales it, and after `to` it chooses how a value prints. A unit is never a value (§3.10, Part U).
- **Working precision.** `p`, the `precision` setting plus four guard digits: the significant digits to which midpoints and series are computed (§3.2.8).

## 8. Other documents

- [design.md](design.md): the specification. Each subsection states its rules and ends with where they are implemented and which test groups check them. Marks: **Decided.** for an owner decision, **Open.** for an unsettled item.
- [core.md](core.md): why Core is small, its invariants, and how it may change.
- [style.md](style.md): Haskell conventions.
- [AGENTS.md](../AGENTS.md): how to build, test and run safely, and the owner's rules for changes.
- [README.md](../README.md) and [TUTORIAL.md](../TUTORIAL.md): the user's introduction.
- [CHANGELOG.md](../CHANGELOG.md): what changed, including hash-affecting changes.
