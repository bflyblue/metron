# Review follow-up

**Current status:** all fourteen numbered findings are addressed. The
second-batch section below records the remaining fixes and final checks.

The review worktree was fast-forwarded from `d907a43` to finished local
`main`, `5160cd1`, before implementation. The original worktree was left
untouched. Changes across all 50 files were compared with the review's
affected code and contracts.

## Effect of the other agent's work

None of R1–R14 was resolved or invalidated by these commits. The main
numerical implementations are unchanged. The edits to `Hash` remove
unused role decoding but leave the malformed-rational path unchanged.
The new compaction test covers linear slack handling, not the nonlinear
correlation failure. Default backend settings now have one definition;
this does not repair the statistical estimator or propagation formulas.

Counterexamples were rerun on the rebuilt `5160cd1` executable before
implementation. Outputs are in `review-evidence/recheck-main.txt` and
`review-evidence/recheck-main-extra.txt`, including the isolated-store
crash. The first new regression run reproduced four failing tests; the
remaining tests passed. The purely mathematical/specification findings
were rechecked against the changed documentation and unchanged code.

## First implementation batch

| Finding | Change |
|---|---|
| R1: falsely shared anonymous remainder | A bound remainder involving any operand's anonymous slack stays anonymous. Its total radius rounds upward to the working length limit. Deterministic sharing for fully identified operands remains intact. Regression tests cover cancellation, exponentials, and independent product corners. |
| R5: decoder crash | Zero denominators and invalid sign bytes are rejected before constructing rationals. Machine-sized fields are range checked; byte lengths and collection counts are checked against remaining input; tensor products use `Integer`. Tests cover invalid encodings, arbitrary small byte strings, round trips, and valid definitions loading beside a corrupt object. |
| R9: unlawful `SecondOrder` combination | Recorded sizes combine by exact addition. Creation and scaling retain their existing upward rounding. Associativity and identity are checked through publicly constructed affine values. |

These repairs change evaluated bounds and rejection of malformed input.
They do not change valid encodings, Core hashes, library hashes, or store
format 12. The design and changelog describe the changes. The existing
precision test caught excessive slack growth in the initial R1 repair;
rounding the combined anonymous radius upward fixes that without
weakening the enclosure.

The decoder changes are not a proof of resilience to arbitrarily large
hostile files. Deep recursive encodings and very large integer arithmetic
still need a separately designed input/work budget; small-byte fuzz
properties cannot establish that guarantee.

## Validation

- Full suite: **1,025 tests passed**, with `--quickcheck-tests 2000`
  (43.45 seconds reported by Tasty).
- The existing high-precision matrix-exponential regression passes.
- HLint: **no hints**. Fourmolu and `git diff --check` pass.
- Flake evaluation: passed for the host system; Darwin was not built.
- The Nix package build, including its test suite, passed. Its source
  snapshot contains the final Haskell changes; only this follow-up record
  and design-document placement were edited afterward.
- Original probes now report `(0 ± 2, 0 ± 2)` instead of an exact second
  zero, `exp x - exp y` encloses the independent range, malformed-store
  startup reports the bad object and exits successfully, and both
  parenthesisations of `SecondOrder` combination agree.

## Remaining work after the first batch (historical)

R2, R3, R4, R6, R7, R8, R10, R11, R12, R13 and R14 remained open. Priorities were
uncertain widths (R2), range-safe double bounds (R3), and determinant
sample preservation (R4). The sample estimator, statistical assumptions,
PSD covariance support, and exterior representation require explicit
design decisions as described in the original review. No package
dependency has been changed in this first batch.

Changes are in `/tmp/metron-review`, branch `review/mathematical-audit`.
They have not been committed, merged, or pushed.

## Remaining findings: implementation completed

The second batch addresses R2–R4, R6–R8 and R10–R14. This section
supersedes the first batch's remaining-work list above.

| Finding | Change and evidence |
|---|---|
| R2: uncertain widths | Non-exact widths pass through affine multiplication by a fresh bound or Gaussian nudge. Statistical and mixed second-order corrections survive; a statistical width does not become a hard bound. Exact widths retain their identity rules. |
| R3: double bounds | Finite basic-arithmetic propagation uses exact rational intermediates and outward conversion. FMA includes an absolute underflow allowance; atan2 uses a range-safe lower radius. The 13,068-case extreme-value grid now finds no finite containment violations. |
| R4: determinants and pivot decisions | Division-free Berkowitz evaluation preserves all copies and bounds; the 1×1 case returns its input, including NaN. A separate permutation formula checks random integer matrices. Inversion also chooses a pivot independently for each copy. |
| R6: stochastic underflow | When an FMA residual vanishes, exact comparisons establish the rounding direction for multiplication, division and square root. Subnormal products retain both enclosing neighbours in stochastic copies. |
| R7: sample summaries | Mean and standard deviation scale finite samples before compensated summation. Regressions cover 1e200 and 1e-200 scales. |
| R8: estimator meaning | The Student interval is shown around the sample mean separately from the nominal result. The nominal accuracy diagnostic includes displacement to that mean; the mean interval includes rounding of its centre. Statistical assumptions are explicit. |
| R10: exterior domain and rotations | `star` checks alternation, including all copies, and rejects unprovable inputs. Bound multiplication uses a commutative remainder identity. `cross` contracts a constructed wedge directly, preserving shared axes and units without asking statistical enclosures to prove an identity they have discarded. Rotation documentation now distinguishes skew logarithms from the invalid exponential-of-sum law. |
| R11: Cholesky domain | Both backends consistently require positive-definite input and reject zero or nonpositive enclosed pivots, including the last pivot and sampled copies. Positive-semidefinite factorisation is explicitly a future extension. |
| R12: stable inverse hyperbolic sine | A dimensionless `asinh` primitive replaces the unstable library formula. Double uses the native operation; affine evaluation uses an odd, sign-stable composition. Extreme negative double inputs remain finite. |
| R13: inverse specification | The design now describes the implemented scalar affine Gauss–Jordan algorithm. A compound Neumann remainder is explicitly future work. Independent triangular inverse corner tests check enclosure containment. |
| R14: statistical assumptions | Independent declared errors are explicitly standard Gaussian; shared labels identify the same variable. First-order moment propagation is distinguished from Gaussian quadratic formulas and local nonlinear diagnostics. Adopted astronomical constants are modelling assumptions. |

All fourteen numbered findings now have a repair or a corrected, explicit
contract. General exterior grades, PSD covariance factorisation, universal
libm guarantees and rigorous nonlinear statistical variance certificates
have not been implemented or claimed. In particular, the double libm ULP
allowances remain platform-dependent assumptions; passing the basic
arithmetic grid does not establish those allowances. Decoder input/work
budgets remain a separate hardening task as described above.

### Compatibility and implementation costs

The `asinh` primitive and revised `linalg.cross` change standard-library
and dependent hashes. Recreate stores from exports; there is no migration.
The wire format remains 12. The changelog lists both changes. `vzipWith`
now preserves an input's preferred display unit when its dimension matches
the result, which keeps the cross product's compound unit.

Double bound propagation now pays for exact rational intermediates, and
the division-free determinant has O(n⁴) arithmetic cost. These choices
prioritise the numerical contract. No performance improvement is claimed.
No package dependency was added.

### Second-batch validation

- Full Cabal suite: **1,038 tests passed** (35.37 seconds), with
  `--quickcheck-tests 2000`; individual test options can override that count.
- The new numerical review group includes the exact-rational grid,
  independent determinant oracle, inverse corners, stochastic underflow,
  sample scaling and domain regressions. Existing orbital, unit, precision,
  storage and K=1/2/4 batching tests also pass.
- HLint: **no hints** with the project's extensions.
- Fourmolu applied to touched Haskell sources; `git diff --check` passes.
- Nix flake evaluation passes for x86_64-linux; Darwin was not built.
- Nix package build passes, including **1,038 tests** (17.81 seconds at
  the package's default property count). Its source snapshot includes all
  functional changes; only formatting and documentation changed afterward.
- `cabal check` still reports pre-existing missing dependency upper bounds
  and rejects the executable's explicit `-O` flag for Hackage portability.
  These packaging issues are outside the numbered numerical findings.

Logs for this batch use the `remaining-` prefix in `review-evidence/`.
The original review/probe files describe their historical baseline; current
regressions live in the test suite. In particular, old diagnostic sources
may use the earlier `uncertain` API, which now takes a precision argument.

Changes remain uncommitted in `/tmp/metron-review` on
`review/mathematical-audit`. The original worktree is clean on `main` at
`5160cd1`; nothing has been merged or pushed.

## Preservation snapshot, 2026-11-02

At the owner's request, this work is committed on the review branch and
preserved by the annotated tag `pre-montecarlo-refactor-2026-11-02`.
This supersedes the uncommitted status above. The snapshot includes the
open indexed-amount proposal and the agreed future arithmetic/propagation
settings in `doc/montecarlo-first.md`. It removes no affine implementation
and is not merged or pushed by this action. All functional source changes
are the ones covered by the final validation above.
