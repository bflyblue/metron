# Metron overview

Metron is a small, pure calculator language for physical quantities.
It checks units, tensor shapes, coordinate spaces and frames before evaluation.
Its content-addressed store identifies definitions by their code and dependencies.

The project is a proof of concept. Language and store formats can change.
Stores are recreated rather than migrated.

## 1. Purpose

Use Metron for unit conversions, reusable engineering calculations and orbital mechanics.
Explicit input distributions describe measurement uncertainty.
Monte Carlo sampling propagates those inputs through complete calculations.
Optional stochastic rounding on doubles provides separate numerical sensitivity diagnostics.
Neither method provides guaranteed error bounds.

## 2. Principles

- Dimensions and shapes belong in types.
- Points and displacements follow different mathematical operations.
- Conversions between coordinate frames are explicit.
- Stored definitions retain their dependencies by content hash.
- Input uncertainty and floating-point sensitivity remain separate.
- Unsupported operations fail explicitly.

## 3. A first session

```text
5 km/h to m/s
:set arithmetic rational
1/3 * 3
20 degC to degF
let distance = sample (normal (12 km) (0.1 km))
let speed = distance / (30 min)
speed to km/h
sd speed
:set arithmetic double
:set roundingAnalysis stochastic
(1e16 + 1) - 1e16
```

Double arithmetic is the default. Rational arithmetic keeps rational operations exact.
Irrational constants and elementary functions still need approximations.
The speed report separates its mean, sample deviation and outcome interval.
The final expression has ordinary result zero and can show rounding sensitivity.
See [the tutorial](../TUTORIAL.md) for complete examples.

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

| Responsibility | Modules |
|---|---|
| Syntax and parsing | `Syntax`, `Lexer`, `Parser`, `Fixity`, `Unicode` |
| Names and desugaring | `NameResolution`, `Desugar`, `Resolve` |
| Core and independent checking | `Core`, `TCore`, `Check` |
| Type inference and dimensions | `Infer`, `Type`, `Dimension` |
| Hashing and storage | `Hash`, `Encode`, `Codebase`, `Store`, `Update` |
| Evaluation and resources | `Eval`, `Compile`, `Limits`, `Strictness` |
| Scalar arithmetic | `Scalar`, `Rational`, `Double` |
| Approximation and sampling | `Numerical.Approx`, `Numerical.Rational`, `Numerical.Sampling` |
| Random identity and reports | `Numerical.Identity`, `Numerical.SamplePlan`, `Numerical.Statistics` |
| Batches and branches | `Batch`, `Branch`, `Remark` |
| Display | `Pretty`, `UnitHint`, `Source` |
| Session and command line | `Driver`, `Command`, `Repl`, `Session.Preferences`, `src/Main.hs` |
| Standard library | `Prelude`, `Builtin`, `Primitive` |

All library modules have the `Metron.` prefix.

## 6. Features and limits

Metron supports rational and double arithmetic, scalar normal and uniform distributions,
sample statistics, tensors, chart transformations, functions, declared data types and lazy lists.
The standard library includes SI units, linear algebra and orbital calculations.

Input-only double sampling can run in parallel batches.
Grouped rounding runs use one bounded grid initially.
Rational sampling runs serially. Results do not depend on the core count.

Distribution parameters must be deterministic.
The language does not yet support hierarchical distributions or stochastic rounding of sample reductions.
Conditional numeric rounding summaries for mixed constructors are unavailable.
Rational domain errors fail explicitly. Nonfinite double outcomes remain visible.

## 7. Glossary

| Term | Meaning |
|---|---|
| Arithmetic | The scalar representation and its numerical operations |
| Distribution | A description of possible input values and their probabilities |
| Input realization | One indexed draw from every reached sample source |
| Ordinary result | The result before stochastic rounding perturbations |
| Rounding repetition | A diagnostic run with fixed inputs and its own rounding stream |
| Sample identity | A lexical or explicit label that preserves shared input draws |
| Chart | Coordinates with an origin, scale and optional orientation |
| Point | A position on a chart, distinct from a displacement |
| Content hash | The identity of a term and its dependencies |
| Core | The small, scope-safe language produced by desugaring |

## 8. Further reading

[design.md](design.md) specifies the language and runtime.
[core.md](core.md) explains representation boundaries.
[style.md](style.md) defines Haskell conventions.
[montecarlo-removal-plan.md](montecarlo-removal-plan.md) records the refactor and validation.
[CHANGELOG.md](../CHANGELOG.md) lists changes that move hashes.
