# Monte Carlo first: arithmetic and uncertainty

Status: agreed direction for a future implementation, recorded 2026-11-02.
The current implementation still has the affine and double backends.
This document does not claim that the settings below already work.
The owner is considering removal of affine support, which remains intact in this snapshot.

## Settings

**Decided.** Separate numerical arithmetic from uncertainty propagation.
The initial arithmetic choices will be `rational` and `double`.
The initial propagation choice will be `montecarlo` only.
Use `samples` to control the number of statistical samples.

```text
:set arithmetic rational
:set propagation montecarlo
:set samples 10000
```

```text
:set arithmetic double
:set propagation montecarlo
:set samples 10000
```

Use the spelling `arithmetic` for the setting.
A fixed seed must reproduce the statistical draws independently of worker count.
Keep sample identity stable when a calculation follows different branches.
Shared uncertain inputs must reuse their draws across all dependent expressions.

## Sampling and numerical error

**Decided.** Statistical sampling and floating-point rounding errors are separate concerns.
Do not make them competing values of `propagation`.
Monte Carlo samples input distributions and produces output statistics.
It does not establish a numerical enclosure or a guaranteed interval containing all outcomes.

The ordinary double arithmetic path uses round-to-nearest operations.
Randomising rounding is a numerical diagnostic, not a draw from an input distribution.
If it returns later, it needs a separate control and separate reported results.
Combining both sources in one sample spread hides what that spread measures.

**Open.** Specify numerical-error reporting before claiming any verified accuracy for the new arithmetic modes.
An initial implementation can explicitly report that rounding and approximation errors are not enclosed.
Do not print a sample standard deviation or a confidence interval as a numerical error bound.
A confidence interval for an estimated mean is also different from an interval describing individual outcomes.

## Input meaning

**Decided.** Preserve the distinction between hard bounds and distributions.
A hard interval supplied with `±` does not determine a sampling distribution.
Do not silently treat it as uniform or Gaussian.
Until an explicit distribution or supported bounded-input policy exists, reject statistical evaluation that needs such a choice.

Declared statistical uncertainty uses its documented distribution and correlation rules.
The current Gaussian interpretation of `±σ` can supply those draws.
Changing arithmetic must not change a declaration's statistical meaning.
The numerical representation of draws can differ between arithmetic modes without promising identical result bits across them.

## Rational arithmetic

Rational addition, subtraction, multiplication and defined division can be exact for the represented operands.
That does not make sampled Gaussian values or transcendental functions exact.
Finite random draws approximate a continuous distribution, and functions such as `sin` generally require approximation.
Those limits remain separate from finite-sample statistical uncertainty.

**Open.** Define the precision policy for draws and transcendental functions under rational arithmetic.
Specify which functions are supported before removing shared approximation machinery from the affine implementation.
Exact rational intermediates can also grow substantially, so existing resource limits must remain active.
No fallback to double can occur silently under a rational arithmetic setting.

## Scope of the snapshot

The annotated tag `pre-montecarlo-refactor-2026-11-02` preserves the numerical review repairs before any affine removal.
The snapshot also includes the open indexed-amount proposal.
Neither that algebra proposal nor this configuration direction is implemented by creating the tag.
The next implementation plan must define output statistics, failure behaviour, arithmetic precision and the treatment of existing uncertainty syntax.
