# Sample evaluation performance repair

Measured on 2026-11-02 with GHC 9.12.3, Cabal 3.16.1.0 and the project's
normal `-O1` build. The baseline executable was built from `2f6f191`.
The scheduler remains `async`'s `forConcurrently`; no scheduler, dependency,
random identity, arithmetic order or store encoding changed.

## Causes and changes

Before the change, optimized `Double.operation` called `$wcopiesOf` inside
the per-realization loop. Its `NoSamples` branch allocated and filled an
N-element unboxed vector to retrieve one constant operand. This was not
eliminated by optimization: both Core and final STG retained that call.
Combining N draws with a constant therefore allocated quadratic storage
over the run, although most of it was short-lived.

`copyAt` now reads the stored scalar for a constant, or indexes the existing
vector for a sampled operand. Optimized Core branches directly on
`NoSamples` and `Copies` in that loop. The matrix evaluation path uses the
same accessor. Whole-vector consumers retain `copiesOf` where broadcasting
is actually required.

`sampleNote` also repeatedly used `drop i` on a list of samples, starting
at the head for every group. It now indexes group coordinates directly.
Ordinary statistics read baseline indices only; diagnostic statistics read
each baseline together with its own repetitions. Constant tensor components
use the same coordinates without constructing broadcast vectors.

## Forced whole-command measurements

Every command used `--no-codebase`, seed 1, double arithmetic, a 4 GB memory
cap and `+RTS -N4 -s`. The expression was:

```text
let f n x = if n == 0 then x else f (n-1) (sin (x * rad)+1)
f 80 (sample (uniform 0 1))
```

Input-only runs used 10,000 draws. The rounding run used 1,000 input draws
and eight diagnostic repetitions per input. Results were fully printed.
Elapsed time comes from RTS statistics and includes startup and reporting.
These are individual observations, not a general speedup guarantee.

| Configuration | Before elapsed | After elapsed | Before allocated bytes | After allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| One worker, input only | 3.183 s | 0.160 s | 129,484,752,224 | 1,403,944,976 |
| Four workers, input only | 1.206 s | 0.118 s | 33,489,883,944 | 1,409,068,232 |
| Four requested workers, grouped rounding | 0.538 s | 0.480 s | 3,360,017,408 | 3,358,201,600 |

Grouped rounding remains serial. Its constants already carry diagnostic
copies, so the constant-broadcast fix does not materially reduce its
allocation. Remaining linear allocation and serial reporting are separate
optimization opportunities.

A second workload used 200 iterations and returned `f ... > 0`, avoiding
numeric summary rendering. One worker dropped from 323,031,129,360 to
2,839,123,000 allocated bytes and from 6.503 to 0.241 seconds. Four workers
dropped from 83,043,205,992 to 2,851,168,584 bytes and from 1.785 to
0.145 seconds. All five before/after outputs matched byte for byte.

At 100,000 draws, the fixed 80-iteration workload with four workers took
0.493 seconds. Sampling process CPU time through `/proc/PID/stat` every
quarter-second observed 256–268% CPU, where 100% means one logical core.
The small fixed workloads finish too quickly for that sampling interval to
characterize their peak utilization accurately.

## Regression evidence

The allocation test runs separate processes for 2,048 and 8,192 input draws
of `let x = sample (uniform 0 1) in (x+1)*2`, using one batch and `-N2`.
It parses `+RTS -t --machine-readable` output and compares allocated bytes,
which avoids timing thresholds and other tests' allocations.
Subtracting totals removes their common startup cost.

The old executable grows by 1,048,380,536 bytes; the fixed executable grows
by 38,699,928 bytes. The test allows 128 MiB of growth, so the baseline fails
and the fixed version passes with headroom.

A hand-computable grouped report also checks baseline quantiles, constant
components, diagnostic displacement and sample count. Existing tests cover
K = 1/2/4 reproducibility, stochastic identities, subnormals, matrix scaling,
branching, limits and separate statistical axes.

Final validation: all 713 tests passed with 2,000 cases per QuickCheck
property and no compiler warnings. HLint reported no hints. Fourmolu,
`git diff --check` and the pinned Nix package build passed.
