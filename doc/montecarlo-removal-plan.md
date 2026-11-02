# Plan: remove affine propagation and separate the two sampling methods

Status: implemented in the review worktree; final validation recorded below.
The target contract is [Monte Carlo inputs and separate rounding analysis](montecarlo-first.md).
Start from the tested snapshot `pre-montecarlo-refactor-2026-11-02` (`d2cfea5`), which contains the review fixes.
Local `main` at `5160cd1` does not contain those fixes.

## Implementation result

Steps 1–8 are complete. Rational and double evaluators share stable input
identities and use separate rounding identities. Distributions, controls,
grouped execution, branch accounting, summaries and format 13 are connected
through the language, runtime, CLI and store. Affine arithmetic, hard bounds,
their syntax and their public controls have been removed.

The final execution decision is a bounded grouped grid, rather than chunked
grouped execution. Input-only double runs retain parallel batching. The grid
has an overflow-checked size cap and a conservative combined step budget.
Chunking is a future performance improvement, not an accuracy feature.
Rational transcendental results are approximations; stochastic transcendental
perturbations are diagnostics. Rounding analysis of cross-input reductions
and conditional numeric summaries for mixed constructors are explicitly
unsupported. These limits are specified in the canonical design.

Validation includes the full suite with 2,000 cases per QuickCheck property,
worker-count equivalence, bounded-memory regressions and separate-axis
reporting. Final counts and measured whole-command costs appear below.

The numbered sections below retain the implementation sequence and its
acceptance criteria. The canonical current behavior is in design §§3.2 and 8.2.

## 1. Resolve the implementation gates

The architecture is decided, but some details need concrete specifications before their dependent steps begin.
Write the selected rules into the target contract and add examples.
Do not delete shared code until its replacements pass their tests.

| Gate | Decision to complete | Required evidence |
|---|---|---|
| Rational arithmetic | Precision, transcendental coverage and rational random-variate generation | Exact rational arithmetic tests, approximation tests, no silent double fallback |
| Distribution identity | First-class distribution representation and stable identity for `sample`, including function calls | Sharing, independent declarations, recursion, export/reload and worker-count tests |
| Rounding identity | Stable operation occurrences across branches and repeated invocations | No operand-only accidental coin sharing, reproducible execution at K=1/2/4 |
| Reporting | Quantile interpolation, diagnostic accessors, nonfinite/mixture handling | Small hand-computable examples and malformed-outcome cases |
| Resource defaults | N, R, arithmetic defaults and total work/storage limits | Combined N×R accounting, integer-overflow refusal and bounded-memory tests |
| Transcendentals | Supported stochastic perturbation model and explicit exclusions | Per-function boundary tests and an honest capability table |

Do not couple this work to the indexed-amount proposal.
Keep the existing tensor and chart types during the sampling refactor.
A later exterior implementation can use the resulting scalar interfaces.

## 2. Extract shared numerical infrastructure

`Double` imports `ArithError`, `Origin`, identifiers and `Magnitude` from `Affine`.
`Scalar` also uses `Magnitude` for unit hints and aliases the affine runtime in several places.
Removing the module first will therefore break more than uncertainty propagation.

Move backend-neutral arithmetic errors and stable source identities into focused modules.
Replace unit-hint dependencies with a representation that supports exact unit factors without affine values.
Inventory `Numerical.Approx` and `Numerical.Linear` for reusable arithmetic versus affine-specific propagation.
Retain exact residual tests, subnormal fixes, scaled statistics and division-free determinant logic from the snapshot.

This is a mechanical extraction step with current behaviour unchanged.
Run the full existing suite and HLint before introducing new semantics.
Use it as a small commit with a clear boundary.

## 3. Implement arithmetic independently of uncertainty

Introduce explicit `RationalArithmetic` and `DoubleArithmetic` selections.
Keep scalar arithmetic, literal conversion, numerical kernels and display separate from sampling configuration.
Build a rational scalar implementation instead of renaming `Magnitude` and retaining its affine fields.

Keep ordinary double calculations in their existing operation order and nearest-rounding mode.
Represent unsupported rational operations as explicit capability errors.
Preserve unit dimensions, charts, tensor operations, IEEE utility functions and resource limits.

Tests compare double nominal outputs with GHC and rational operations with exact reference values.
Test negative powers, zero division, NaN, infinity, underflow, matrix operations and empty tensors.
Document approximation precision rather than claiming exact transcendental results.

## 4. Introduce distributions and stable sampled inputs

Add dimension-checked normal and uniform distribution constructors.
Start with scalar deterministic parameters, plus shared-input constructions for correlation.
Keep distribution descriptions separate from realized input values.

Remove bound and Gaussian shorthand from the target grammar and standard library.
Audit `Parser`, `Fixity`, `Desugar`, primitive names, inference, typed lint, pretty-printing and round trips.
Rewrite each standard-library uncertainty declaration using its intended distribution.
Do not mechanically turn a hard interval into a normal or uniform distribution.

Core currently has `Noise` and `Uncertain`, carrying labels for input identity.
A plain unlabelled `PrimApp "sample"` does not automatically preserve that identity.
Apply the Core extension test in `core.md` before choosing the representation.
Prefer one labelled sampling form if existing primitive arguments cannot express stable identity without leaking implementation tokens into user code.

If that form is required, replace the two old uncertainty forms rather than retaining all three.
Update Core and Typed Core traversals, equality, codecs, needs analysis, strictness, compilation and checking together.
Distributions can use existing data/type mechanisms where possible.
No general effect system or type-class dispatch is required merely to describe a distribution.

Test `x-x`, shared input through closures, separate declarations, labels/owner stamps, stored functions and input parameters in different units.
Test that distribution parameters containing sampled inputs fail in the initial domain.
Test deterministic degenerate distributions without spurious statistical spread.

## 5. Separate the two execution axes

Replace `Estimate = ErrorBound | Copies Spread` as the organising representation.
Replace the `RoundingOnly | Drawn` distinction with explicit ordinary input results and grouped rounding repetitions.
Define logical coordinates `(i,j)` and retain global coordinates across worker partitions.

Compute each ordinary Y_i independently of rounding analysis.
Compute Z_ij with that same input realization and its own rounding stream.
Without sampled inputs, compute one baseline and R rounding repetitions.
With analysis off, allocate no rounding repetitions.

Refactor `Batch`, `Branch`, `Eval`, scatter/gather operations and memoisation for these coordinates.
Keep shared sampled values stable under lazy forcing and branching.
Distinguish input-driven branch changes from rounding-driven changes within one input.
Rounding repetitions now follow their own branches instead of being forced down the nominal branch.

Start with correctness on small grids. The adopted first implementation uses
a capped grid; defer chunked grouped execution as documented above.
Charge the total evaluation against steps, memory and time limits, including the diagnostic work.

Tests require identical baselines when R, analysis mode or worker count changes.
Increasing R must preserve the existing indexed rounding runs.
Test two input draws with three rounding repetitions using a hand-built grid before randomized tests.
Test divergent recursion, skipped sample sites, constructors, tensors and failures.

## 6. Implement separate summaries and controls

Add the agreed settings to the driver, CLI, preference persistence, help and completion.
Remove the old backend and rounding settings when the new interface takes over.
An invalid configuration must fail clearly, including rational arithmetic with stochastic rounding.

Compute input summaries from Y_i alone.
Compute within-input rounding spread and RMS displacement from Z_ij and Y_i.
Never flatten the grid to estimate an input standard deviation or mean confidence interval.
Use scaled accumulation and deterministic reduction order where reproducibility requires it.

Remove ambiguous `errorOf` and `digitsOf` APIs.
Provide explicit accessors only after their return types and exceptional-outcome behaviour are specified.
Update the cross-copy aggregation set in `Batch.acrossCopies` so reductions do not run independently in each partition.
Keep unit scaling consistent in both printed and programmatic statistics.

Golden tests distinguish outcome quantiles, sample deviation and numerical diagnostics.
All-agreeing repetitions print “no variation observed”.
Include the cancellation example `(1e16+1)-1e16` and an exact binary operation with no rounding spread.
Report unsupported analysis, excluded distribution generation and nonfinite run counts explicitly.

## 7. Remove affine and hard-bound paths completely

Delete `Metron.Affine`, its scalar instance and its backend selection once replacements pass.
Delete running `ErrorBound` propagation and its outward bound bookkeeping.
Keep exact arithmetic used to determine stochastic neighbours, even when it resembles code formerly used by bounds.
Internal approximation intervals can remain if they serve rational numerical kernels rather than a user-visible bound mode.

Remove `bound`, affine budgets, compaction, nonlinear statistical markers, sigma-based comparison policies and affine-only commands.
Inventory `mean`, `sd`, covariance and correlation functions individually.
Retain a useful statistic only under an explicit sample-based definition, including its reduction axis.
Do not silently retain an affine formula under a new name.

Replace source tests of removed behaviour with tests of the new contract.
Retain regression coverage for unrelated decoder, algebra, matrix, units and precision repairs.
Keep old review evidence only as historical evidence tied to the preservation tag, not as active test instructions.
No compatibility aliases, deprecated operators or hidden fallback backend remain.

## 8. Update storage, library and documentation

Bump the store format for changed Core forms and type/term encoding.
Update encoder and decoder validation together, including corrupt-object handling from the review.
Recreate stores from explicitly rewritten exports, with no migration or reinterpretation of old uncertainty syntax.
List changed library and dependent hashes in the changelog.

Rewrite design §§3.2 and 8.2 and all other affected sections to describe only the implemented target.
Update `core.md`, the overview, README, tutorial, settings help and language examples in the same release.
Move the new design into the canonical sections instead of retaining contradictory descriptions after implementation.
Keep the indexed-amount proposal open and update only its backend assumptions.

Use documentation examples as executable tests where possible.
Make sure that constructor descriptions, units, outputs and configuration defaults agree across all entry points.
Do not describe illustrative output as measured test evidence.

## 9. Final validation and acceptance

Each functional stage must build and pass its relevant tests before its commit.
Run the full suite with increased QuickCheck counts after integration.
Run formatting, HLint with the project extensions, `git diff --check`, Cabal checks and the pinned Nix package build.
Cap every interpreter and Cabal test run according to AGENTS.md.

Acceptance requires:

- Rational and double arithmetic work without importing affine uncertainty machinery.
- Monte Carlo input statistics are unchanged when rounding analysis toggles.
- Rounding diagnostics reuse fixed input realizations and never claim hard bounds.
- Random identities and reports agree across K=1, 2 and 4.
- Combined sampling obeys resource limits and has measured memory behaviour.
- Removed syntax, settings, APIs and store formats are refused without legacy reinterpretation.
- The standard library and orbital/chart examples pass with explicitly reviewed input models.
- Independent arithmetic and statistical tests cover the new domains and failure paths.

Benchmark the cost of N input evaluations separately from N×R diagnostic work.
Measure peak residency with forced results and fixed seeds.
Passing numerical tests alone is not evidence that the nested evaluator uses bounded memory.
Publish measured costs and remaining approximation limits with the implementation.

## Validation record (2026-11-02)

All 711 tests pass with 2,000 cases per QuickCheck property and no compiler
warnings. The pinned Nix package build and the local-system flake check pass.
The suite includes
ordinary-result invariance, stable indexed repetitions, K = 1/2/4 equivalence,
separate branch counts, nonfinite predicates, input sharing, matrix kernels,
store validation and constant-memory recursion. HLint uses the extensions
required by AGENTS.md; formatting and `git diff --check` are also checked.

Whole-command measurements below use the built executable, seed 1, one core,
and `let x = sample (normal 10 0.1) in x*x/3`. Printing forces the result and
all statistics. Each command runs under a 4 GB memory cap. Times include
startup and printing; maximum residency is GHC's sampled live heap, not RSS.
These are individual measurements, not a throughput or scaling guarantee.

| Inputs | Rounding repetitions per input | Elapsed seconds | Maximum live heap, bytes |
|---:|---:|---:|---:|
| 1,000 | off | 0.128 | 4,453,192 |
| 10,000 | off | 0.920 | 7,011,352 |
| 1,000 | 8 | 0.213 | 4,453,360 |
| 10,000 | 8 | 3.781 | 13,392,520 |

The 10,000-input ordinary mean and standard deviation are identical with
rounding off and on. Eight repetitions add a typical rounding spread of
about 7.15e-15 and RMS displacement of about 9.60e-15 for this expression.
These values describe this experiment, not a certified error limit.

`cabal check` identifies the existing missing dependency upper bounds. The
redundant explicit `-O` option has been removed, leaving Cabal to select its
normal optimization level. Dependency version policy is unchanged.
