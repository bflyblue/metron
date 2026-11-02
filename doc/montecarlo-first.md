# Monte Carlo inputs and separate rounding analysis

**Decided.** This is the adopted sampling architecture, implemented in the review worktree.
Recorded 2026-11-02.
The preservation tag is `pre-montecarlo-refactor-2026-11-02` at `d2cfea5`.
The canonical runtime specification is now in design §§3.2 and 8.2.
The staged work is in [the removal plan](montecarlo-removal-plan.md).

## Scope

Remove affine uncertainty propagation and hard running numerical bounds.
Keep Monte Carlo input sampling and CESTAC-style stochastic rounding analysis as separate facilities.
Support `rational` and `double` arithmetic.
Only double arithmetic supports stochastic rounding analysis initially.

There is no certified enclosure mode in this design.
A sampled outcome interval is not a hard bound.
A stochastic rounding diagnostic is not a proof of numerical accuracy.
The implementation must preserve these distinctions in output and APIs.

## User controls

**Decided.** Use these independent settings:

| Setting | Values | Meaning |
|---|---|---|
| `arithmetic` | `rational`, `double` | Arithmetic for numerical coefficients |
| `propagation` | `montecarlo` | Input uncertainty propagation, the sole initial choice |
| `samples` | Positive integer N | Number of input draws when sampled inputs occur |
| `roundingAnalysis` | `off`, `stochastic` | Whether to run extra double computations with random rounding |
| `roundingSamples` | Integer R, at least 2 | Rounding repetitions for each fixed input draw |
| `seed` | Reproducible seed | Root of separate input and rounding random streams |
| `cores` | Worker count | Execution partition, with no effect on random identities |

```metron
:set arithmetic double
:set propagation montecarlo
:set samples 10000
:set roundingAnalysis stochastic
:set roundingSamples 8

let distance = sample (normal (100 m) (0.5 m))
let duration = sample (normal (10 s) (0.1 s))
distance / duration
```

`roundingAnalysis off` disables only the diagnostic repetitions.
It never disables IEEE rounding in ordinary double calculations.
It does not change the input draws or their ordinary results.
There is no `roundingErrors` switch because this design retains no hard numerical bounds.

If an expression has no sampled inputs, evaluate one ordinary result.
If rounding analysis is enabled, run R diagnostic repetitions for that result.
Do not run N identical input evaluations in this case.
The `samples` setting no longer selects a numerical analysis method.

Reject `arithmetic rational` with `roundingAnalysis stochastic` before evaluation.
Never silently turn off a requested analysis when arithmetic changes.
One input sample can be evaluated, but it cannot provide an estimated sample standard deviation.
Report unavailable statistics explicitly rather than replacing them with zero.

**Decided.** Defaults are double arithmetic, rounding analysis off, N=10000 and R=8.
N is at most 100000 and R at most 1000. The combined grid is capped at one million runs and the component limit.
Counts remain independent of definitions and their hashes.
Limits must apply to the combined work, not merely to each setting separately.

## Explicit input distributions

**Decided.** Declare a distribution for each sampled input.
A distribution describes possible input values and their probabilities.
A sample declaration introduces a stable uncertain input identity.
It is not a fresh random draw every time a variable is referenced.

```metron
let length = sample (normal (10 m) (0.02 m))
let delay = sample (uniform (0 s) (2 s))
length - length
```

The last expression is zero in each ordinary input evaluation.
Both uses refer to the same draw.
Independent source declarations receive independent random identities by default.
Changing worker count or lazy evaluation order must not change those identities.

Normal and uniform are the first required distribution constructors.
Their scalar parameters must share physical dimensions.
Normal takes a mean and a nonnegative standard deviation.
Uniform takes ordered lower and upper endpoints.
A zero standard deviation or equal endpoints produces a deterministic input.
Negative deviations, reversed endpoints and nonfinite double parameters are errors.

Constructors describe distributions and do not sample them.
They can be passed to functions without introducing additional uncertain inputs.
Named axes, units and points remain subject to the existing type rules.
For uncertain points, sample a displacement and use the explicit point-plus-displacement operation.
Do not make an offset unit into an additive scalar distribution by accident.

Initial scalar signatures, with syntax subject to the type design:

```text
normal  : Num d -> Num d -> Distribution d
uniform : Num d -> Num d -> Distribution d
sample  : Distribution d -> Num d
```

Distribution parameters are deterministic in the first stage.
Reject sampled parameters until hierarchical distribution semantics are specified.
Correlated quantities can already be built from shared sampled inputs, for example `x = a*z + b` and `y = c*z + d`.
A joint-distribution constructor is a later extension, not an assumption that tensor components are independent.

**Decided.** Represent distributions with the existing structural data type
mechanism. `Distribution d` has `Normal` and `Uniform` constructors, each with
two scalar fields of dimension `d`. The lowercase constructors have the same
types. Validate their parameter values when sampling, including values made
with the uppercase constructors.

**Decided.** Sampling needs one labelled Core form, `Sample label distribution`.
An ordinary primitive application cannot see its definition-site identity.
Passing an implementation identity through a user-visible argument would
expose an evaluator concern in the language. The new form replaces the two
old uncertainty forms. Inference,
typed lint, traversal, hashing, decoding and owner restamping cover it.

**Decided.** Generate input variates in rational arithmetic before converting
them to the selected coefficient arithmetic. Uniform draws use the midpoints
of 2^64 equal probability cells. Normal draws use Box–Muller with the rational
elementary functions at working precision plus eight guard digits. This is a
finite numerical approximation to a distribution, not a hard support or
accuracy guarantee for a mathematical normal distribution. Seed domains for
inputs and rounding are distinct. Input generation cannot read the rounding
repetition index.

Display-unit factors hold the represented rational coefficient, with no
uncertainty form. A factor calculated with an approximate function remains an
approximation; storing it as a rational does not make the physical constant
exact.

**Decided.** Remove `±`, `+-`, `±σ`, `+-s`, `noise` and `gauss` as uncertainty constructors.
Use explicit distributions instead.
A hard interval does not specify probabilities, so never convert old `±` expressions to uniform sampling automatically.
Remove old forms rather than retain aliases or compatibility hints.
Rewrite the standard library deliberately, and recreate stores from reviewed exports.

## Two separate sample axes

Let X_i be the input realization for input index i.
Compute Y_i using ordinary arithmetic on X_i.
For doubles, this baseline always uses round-to-nearest.
Its input draws and results are independent of whether rounding analysis is enabled.

For each i, compute Z_ij for rounding repetition j on that same input realization.
Only rounding choices vary across j.
The result has two logical indices `(input, rounding)`, not one flattened set of interchangeable samples.
Streaming implementations can avoid storing the entire grid, but must preserve these meanings.

Key input randomness by the input declaration identity, global input index and input stream seed.
It must not include the rounding index.
Key rounding randomness by a separate seed domain, operation occurrence, input index and rounding index.
Shared evaluated expressions reuse their numerical results, rather than acquiring new rounding coins when read again.

Literal conversion and supported arithmetic operations participate in rounding analysis.
For a declared sampled input, all repetitions reuse one generated value before its conversion to double.
They can analyse conversion of that value without generating new physical draws.
Distribution-parameter evaluation and random-variate generation are outside the initial rounding diagnostic scope.
State that exclusion in the report, especially when distribution parameters involve substantial calculations.

The existing operand-hash coin scheme needs a specific review.
Equal operands at unrelated operations must not accidentally force the same rounding coin.
Operation identity must be stable across batches, lazy forcing, recursion and stored-function calls.
Identical seeds and sample indices must reproduce results at K=1, 2 and 4.

## Branches and exceptional outcomes

Ordinary input runs follow the branches selected by their own input values.
Rounding repetitions follow their own rounded comparisons and branches too.
This extends the old rounding-only behaviour, which kept the nominal branch and issued a warning.
The new report separates input-driven branch frequencies from rounding-driven disagreements within each input group.

Operation identities cannot depend on one mutable global random counter.
A repetition can skip a branch without shifting randomness for unrelated work.
A sample declaration has a stable per-input realization even if reached only by a diagnostic branch.
Operation identities combine lexical sites, application paths and internal component indices.
A sample source retains its lexical identity across calls. Distinct sample sites introduce independent latent inputs.

Record NaN, infinity, domain failures and different result constructors separately.
Do not silently discard failed runs or average incompatible outcomes.
For valid numeric subsets, label every statistic with its conditioning and counts.
If a conditional statistic is not implemented, report it as unavailable.

## Reports

**Decided.** Input statistics use only the ordinary results Y_i.
Report the empirical mean, sample standard deviation and central quantile interval with the input count.
Do not treat the N×R rounding repetitions as additional independent input observations.
A quantile interval describes simulated outcomes, not confidence in the estimated mean.

The initial central 95% interval uses empirical 2.5% and 97.5% quantiles.
Quantiles use linear interpolation at (N−1)p, also called type 7.
Do not add a Student confidence interval or a claim of significant digits by default.
Input distributions with heavy tails or few samples can give unstable summary statistics.

For each finite scalar output, let s_i be the sample standard deviation of its R rounding repetitions.
Define the typical rounding spread as `sqrt(mean_i(s_i^2))`.
Also report the RMS displacement from the ordinary results, `sqrt(mean_ij((Z_ij-Y_i)^2))`.
The displacement matters when repetitions agree with one another but differ from the baseline.
Both values are diagnostics, not error bounds.

Use scaled or compensated summary algorithms to avoid overflow and underflow.
Compute tensor summaries componentwise, with units and shapes intact.
Any maximum is a maximum observed in these runs, not a worst-case mathematical guarantee.
If all repetitions agree, report “no variation observed”, not “exact”.

Illustrative layout only, not a captured program result:

```text
Mean speed:                 10.001 m/s
Input uncertainty:
  standard deviation:        0.112 m/s
  central 95% interval:       [9.785, 10.224] m/s
  input samples:             10000

Floating-point sensitivity:
  typical rounding spread:   ... m/s
  RMS baseline displacement: ... m/s
  rounding repetitions:      8 per input sample
  statistical diagnostic, not a guaranteed bound
  excludes distribution generation and parameter evaluation
```

For an expression without sampled inputs, print its ordinary result instead of an input-distribution report.
For `(1e16 + 1) - 1e16`, that result is 0 under ordinary double arithmetic.
The stochastic repetitions can expose alternative values such as 2.
Do not present their mean as a certified correction to the ordinary result.

Existing `errorOf` and `digitsOf` mix incompatible meanings across configurations.
Remove these APIs rather than silently reuse them for the new statistics.
Replace them with explicit input-statistic and rounding-diagnostic accessors when their names and return types are specified.
Keep useful IEEE utilities such as `ulps`, `nextUp`, `fma`, `isNaN` and `isInfinite` on doubles.

## Arithmetic and scope of the diagnostic

Rational arithmetic is exact for represented rational operands under rational operations.
Gaussian draws, irrational constants and transcendental functions generally need approximation.
Their numerical accuracy is not certified by input sampling.
Do not silently route rational arithmetic through double operations.

**Decided.** Rational operations remain exact on represented operands.
Elementary functions use the configured precision with guard digits.
Uniform inputs use rational midpoint cells. Normal inputs use rational Box–Muller calculations.
Retain reusable approximation kernels while removing affine propagation.
Internal intervals used to calculate an approximation can remain implementation tools.
They must not leak into a claim that final values carry hard bounds.

The double rounding diagnostic follows CESTAC-style random directed rounding.
Keep the nominal IEEE result and the repetitions separate.
Preserve exactness and underflow fixes from the tagged snapshot when selecting enclosing neighbours.
Equal-probability directed rounding is not assumed to make the result unbiased.

Transcendental perturbations need an explicit per-function policy.
The current one-ulp random perturbation is a heuristic, not a proof of a library function's error.
If retained initially, identify that scope in the diagnostic description.
Unsupported operations must refuse requested analysis rather than silently stop perturbing halfway through an expression.

This design makes no unconditional confidence claim for CESTAC estimates.
Coin dependence, nonlinear calculations and divergent branches require validation beyond observing a sample spread.
Increasing R improves sampling of the chosen perturbation model, not the ordinary result itself.

## Implementation and validation status

The implementation covers the scalar interface, both arithmetic implementations,
grouped execution, branch reporting, controls, labelled Core sampling and format 13 storage.
The [removal plan](montecarlo-removal-plan.md) records validation.

Grouped rounding executes as one bounded grid initially. Input-only doubles retain parallel batches.
Rational sampling executes serially. The core count does not change results.
Rounding analysis of sample reductions and conditional numeric rounding summaries for mixed constructors are unsupported and explicit.
Rational domain failures stop evaluation rather than silently dropping failed runs.
These limits are part of the initial scope.

## Sources

[CESTAC and stochastic arithmetic](https://perso.lip6.fr/Stef.Graillat/papers/nsv.pdf) motivate repeated randomly rounded calculations.
The implementation is inspired by this method, not a claim of CADNA conformance.
Its estimator and branching policies need their own evidence.

[JCGM 101:2008](https://www.bipm.org/en/publications/guides) describes propagation of input distributions through Monte Carlo evaluation.
This is distinct from perturbing floating-point operations.
Neither reference licenses combining both sources into one unlabeled variance.
