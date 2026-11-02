# Metron review

This is the original review snapshot. The follow-up against finished `main`
and implementation progress are recorded in [FIXES.md](FIXES.md).

Review date: 2026-11-02. Baseline: `d907a4306b484de4a045fb1b0af0da8c95e9f3a3` on local `main`.
Review branch: `review/mathematical-audit`; worktree: `/tmp/metron-review`.

Final branch check: local `main` still points to this baseline. The original working tree is clean. Review artifacts are uncommitted in the separate review worktree; nothing was merged or pushed.

## Assessment

Metron has a promising foundation: dimensions and nominal frames prevent many category errors; inference is followed by an independent checker; content identity is separate from names; and the newer evaluator has meaningful resource and retention tests. The shared Core traversal and fixity table are useful improvements. Exterior algebra is a sensible next direction, but it should follow repairs to uncertainty semantics and numerical guarantees.

The passing suite is not yet sufficient evidence for the numerical promises. This review reproduced failures in both backends, including falsely exact results. The highest priorities are anonymous-error correlation, uncertainty widths, double error propagation, determinant samples, and malformed-store handling. There are also mathematical specification errors and an unlawful Haskell `Semigroup` instance.

No implementation, dependency, design, or existing test file was changed. Diagnostic sources and outputs are in [review-evidence](review-evidence/). Commands below assume the freshly built executable and the resource wrapper described there; they must not be run against the user's database.

Severity: **P1** means an incorrect guarantee, silently lost information, or a normal recovery path that crashes. **P2** means a substantive correctness/contract issue, misleading mathematical model, or important extension obstacle. Confidence is high for the reproduced findings; architectural recommendations are identified separately.

## Validation and limits

| Check | Result |
|---|---|
| Pinned toolchain | GHC 9.12.3; cabal-install 3.16.1.0; normal Cabal `-O1` build |
| `cabal -v0 build all` | Passed; no compiler warnings emitted |
| Baseline suite | All 1,008 tests passed, 15.63 s reported by Tasty |
| Suite with `--quickcheck-tests 2000` | All 1,008 tests passed, 35.77 s; local test options can override global counts |
| HLint, project extensions | No hints |
| Targeted numerical probes | Reproduced findings below |
| Exact rational extreme-value grid | 157 running-bound violations among a grid of 13,068 basic arithmetic cases; see R3 |
| Batch comparison | Representative sampled branch output identical at K = 1, 2, 4; determinant defect also identical at all three |
| Retention/stack probes | Million-step accumulator and list traversal completed at about 4.5 MB maximum residency with `-K1M` |
| Core/STG | Actual `-O1` build inspected; specialised affine and double evaluators and primitive dispatchers present |
| Package compatibility | `fp-ieee`, `integer-roots`, and `statistics` compiled/ran in a separate pinned GHC 9.12.3 environment |

Interpreter and test experiments used a systemd scope with `MemoryMax=4G`, `MemorySwapMax=0`, and per-command timeouts. Nix access needed the normal sandbox escalation. No global tools were installed. Temporary stores were used only for corruption experiments.

This is broad subsystem coverage with selective deep source inspection, not a claim that every line or mathematical bound has been verified. The generated tests principally exercise small terms and moderate magnitudes. The double-bound generator in `test/Backend.hs:462` uses small decimal mantissas, exponents 0–4, and modest exponentials. Its oracle permits overlap with the affine enclosure, rather than independently certifying containment of the true answer. Increasing its case count cannot discover exponent regions it never generates. Exact rational checks found failures immediately outside that region.

Full crash/power-loss fault injection, concurrent writers, all orbital constants against their original publications, every platform's libm, and a complete independent proof of the fixed-point transcendental enclosures remain outside the demonstrated evidence. No new defect is inferred merely from those gaps.

## Findings

### R1 — P1: anonymous slack becomes a falsely shared nonlinear remainder

**Locations:** `lib/Metron/Affine.hs:618`, `:879`, `:929`, `:943`; design §§3.2.4 and 3.2.7.

```metron
let x = 0 +- (0 +- 1)
let y = 0 +- (0 +- 1)
(x-y, x*x-y*y)
```

Observed: `(0 ± 2, 0)`. The first result correctly treats anonymous slack as independent. The second incorrectly reports exact zero. The allowed assignment `x=1, y=0` gives a difference of squares of 1.

With the same declarations, `exp x - exp y` returns `0 ± 2`, although `x=1, y=-1` gives approximately 2.3504. The failure therefore also affects smooth-function propagation, not only squares. Both outputs are recorded in `slack.txt`.

The two values have the same *enclosure representation*, but not the same unknown. Multiplication at midpoint zero moves their slack-dependent quadratic error into a named remainder. `builtinId` hashes the operand representations, including only the numerical slack radius. Both products therefore get the same remainder identity, which subtraction cancels. Representation equality is not dependence identity once anonymous uncertainty is present.

**Remedy:** never derive cancellable dependence from equal anonymous radii. Keep contributions involving anonymous slack anonymous, or introduce provenance that actually identifies the underlying uncertainty. Preserve deterministic sharing for operands whose full dependencies are represented. Do not fix this by making every operation globally fresh: that would unnecessarily destroy valid correlation.

**Regression:** the example above; independent compacted forms with equal radii; zero/nonzero midpoints; multiplication, reciprocal, and composed functions. Check enclosure containment against independent assignments, including corners. Existing linear slack tests do not cover this nonlinear transition. This changes evaluated bounds, not Core hashes, unless the representation change also affects stored syntax.

### R2 — P1: uncertainty in an uncertainty width is dropped or assigned the wrong kind

**Locations:** `lib/Metron/Affine.hs:1642`, `lib/Metron/Scalar.hs:448`; design §3.2.5.

```metron
0 +- (0 +-s 1)       -- observed: 0
0 +-s (0 +-s 1)      -- observed: 0
0 +-s (1 +-s 1)      -- observed: 0 ±σ 1
0 +-s (1 +- 1)       -- observed: 0 ±σ 1 (bound 1)
```

`uncertain` keeps the width's midpoint and bound radius, and copies its pre-existing second-order markers. It does not account for the width's first-order statistical coefficients. Thus a random width can disappear entirely. For a statistical outer operation, uncertainty in its coefficient is also not an additive hard error of the same radius: multiplying a bounded coefficient error by an unbounded statistical variable is not bounded.

The documented expansion to multiplication by `noise`/`gauss` does not agree with this implementation for uncertain widths. The statements that a sigma never becomes a bound and that an uncertain coefficient is tracked as such must apply here too.

**Remedy:** first define admissible widths explicitly. A safe initial repair is to reject statistical uncertainty in the width until supported, and to route permitted non-exact widths through the same mixed-error rules as multiplication. Preserve exact-width identity and shared-label behaviour. Do not silently take only the midpoint.

**Regression:** both kinds of outer operator crossed with exact, bounded, statistical, and nonlinear-marked widths; zero midpoint; tensor broadcasting; labelled/shared errors. Check equivalent supported desugarings. Changing the implementation alone need not change Core hashes; changing desugaring does.

### R3 — P1: the double running bound can be zero or too small

**Locations:** `lib/Metron/Double.hs:278`, `:350`, `:415`, `:575`, `:633`; design §8.2.2.

Under `--backend double`:

| Expression | Observed | Mathematical issue |
|---|---|---|
| `((1e100 + 1) - 1e100) / 1e200` | `0`, no error | Exact formula is `1e-200` |
| `atan2 ((1e200 + 1) - 1e200) 1e200` | `0 ± 3.0e-323 rad (bound)` | Exact angle is about `1e-200 rad` |
| `fma (2^-537) (2^-538) 0` | `0`, no error | Exact result is positive `2^-1075`, rounded to zero |
| `nextUp 0 / nextUp (nextUp (nextUp 0))` | `0.3333333333333333`, no error | Exact quotient is 1/3 |

These have distinct causes and need separate regressions:

1. The quotient bound forms a denominator `|b|*(|b|-eb)` that can overflow, reducing a positive propagated error to zero.
2. `atan2` forms `sqrt(x*x+y*y)` without scaling; overflow makes the lower-radius estimate infinite and suppresses propagated error.
3. `fma` uses `u*abs(result)` without an absolute underflow allowance. The generic `raw == 0` shortcut then treats the result as exact.
4. The quotient exactness guard checks whether the *result* is normal. Its FMA residual can underflow with tiny operands even when the quotient is normal. A zero residual is then not proof of exactness.

`ExtremeProbe.hs` independently compares scalar `+`, `*`, and `/` against exact `Rational` arithmetic over 66 operands spanning exponents −1074 through 1023. It finds **157 violations**. This is not a statistical failure rate: it is a deliberately adversarial deterministic grid, with nonfinite results/bounds excluded from the violation test.

**Remedy:** use scaled, range-safe formulas and outward arithmetic; retain an absolute allowance for gradual underflow. Restrict error-free-transform exactness claims to their actual preconditions, with scaled or exact fallback near exceptional ranges. Post-hoc relative widening cannot repair an error already rounded to zero. Audit all sibling formulas, including libm bounds and norms.

**Regression:** each counterexample, normal/subnormal boundaries, extreme exponent pairs, overflow in intermediates with finite results, and exact rational containment. Keep IEEE nominal values as specified; repair the accompanying bounds. No Core hash change is necessary.

### R4 — P1: determinant discards error, samples, and NaN on a nominally zero/NaN pivot

**Locations:** `lib/Metron/Double.hs:1054`, `:1082`; design §8.2 and the determinant signature.

```metron
-- double, samples 0
det [[(1e20 + 1) - 1e20]]   -- observed: exact 0; exact formula is 1
det [[0/0]]                 -- observed: 0; the 1x1 determinant is NaN

-- double, samples 100, cores 1, 2 or 4
det [[0 +-s 1]]             -- observed: exact 0, sample information gone
```

`pivotOf` looks only at `.value`. When the best pivot is zero or NaN, `determinantD` returns `exactDbl 0`, losing everything the entries carry. Even the 1×1 identity `det [[x]] = x` fails.

**Remedy:** preserve the scalar for a 1×1 determinant, propagate nonfinite values deliberately, and handle singular nominal paths without discarding bounds or copies. For sampled matrices, pivot/zero decisions must be valid for each copy, not just the nominal matrix. Fixing only the 1×1 case is insufficient; audit inverse and Cholesky for sample-dependent pivot/domain paths as well.

**Regression:** these cases, 2×2 matrices with zero nominal pivots and nonzero sample pivots, sample-wise reference determinants, singular samples, NaN placement permutations, and K=1/2/4 equality. No Core hash change is necessary.

### R5 — P1: a malformed stored rational crashes the loader instead of being skipped

**Locations:** `lib/Metron/Hash.hs:325`, `lib/Metron/Store.hs:589`; design §7.4.

The six bytes `[3,0,0,1,1,0]` encode a rank-zero literal with numerator 1 and denominator 0. `decodeStored` builds it with `(%)`, which raises `Ratio has zero denominator` when forced. It does not return a decoding error.

The direct decoder probe catches that exception. A separate freshly seeded temporary store containing those bytes under a valid-looking hash filename causes normal CLI startup to exit with an uncaught arithmetic exception, rather than print a corruption note and load the rest. See `decoder.txt` and `store.txt`.

**Remedy:** validate denominators before construction. Audit other decoder boundaries at the same time: unchecked `Integer`→`Int` conversions, `i+n` overflow, negative/oversized dimensions after conversion, length products, tags, constructor indices, and recursion/size limits. Hash verification occurs after decoding and cannot protect this boundary. Use structured failures, not a broad catch that hides programmer errors.

**Regression:** malformed denominator, truncated varints, oversized lengths, invalid tags/indices, and arbitrary-byte decoding. Assert no synchronous exceptions, bounded work, and continued loading of valid unrelated terms. `binary` can simplify parser plumbing but does not replace semantic validation.

### R6 — P2: stochastic rounding treats an underflowed residual as exact

**Locations:** `lib/Metron/Double.hs:275`, `:278`, `:283`, `:390`; design §8.2.3.

With double, 100 samples, and one core, `1e-200 * 1e-200` prints `0`; `errorOf` returns `0`. The result is strictly positive and lies between zero and the least positive subnormal. The specified equal-probability directed rounding should produce both neighbours over copies, not classify every result as exact.

`productSide` uses an FMA residual that itself underflows. Unlike the running-bound path, the copy path has no safeguard before taking `EQ` as exact. Similar residual issues affect division and square root.

**Remedy:** determine direction using a scaled/exact fallback in the unsafe region. Keep this separate from R3's bound fix: supplying a nonzero bound does not repair sample generation. Regression tests should inspect copies against exact rational neighbour selection and compare all core counts.

### R7 — P2: sample statistics overflow and underflow at ordinary finite scales

**Locations:** `lib/Metron/Double.hs:771`, `:779`, `:857`, `:1000`.

With double, samples 100, rounding nearest, cores 1:

```metron
sd (0 +-s 1e200)   -- observed: Infinity
sd (0 +-s 1e-200)  -- observed: 0
```

The generated samples and their standard deviations are representable. Squaring unscaled deviations overflows or underflows before the square root. `estimateOf` repeats the same pattern, and `meanOf` can overflow its shifted sum for large ranges. These statistics feed printing and later computation as exact doubles.

**Remedy:** use scaled sum-of-squares and an overflow-aware mean, with compensated accumulation where appropriate. Share one implementation between displayed statistics, `sd`, and stochastic estimates. Preserve deterministic global copy order across batches.

**Package caution:** pinned `statistics` compiled successfully and supplies compensated sums, but its `stdDev` also squares unscaled differences. The isolated package probe returned `NaN` for `[-1e200,1e200]` and `0` for the small-scale pair. It is useful with an appropriate scaling wrapper, not a drop-in cure.

### R8 — P2, design: the stochastic confidence statistic is attached to the wrong result

**Locations:** `lib/Metron/Double.hs:857`, `:885`; design §§8.2.3 and 8.2.8.

At 10,000 samples, `1/10` prints `0.1 ± 1.9e-19 (estimate, 10000 samples)`. Its nominal IEEE value is unchanged by the sample count and differs from exact 1/10 by approximately `5.5511e-18`. `1 + 1e-16` prints `1 ± 3.1e-18`, although the nominal error is `1e-16`.

The statistic `t*s/sqrt(N)` is a standard-error interval for a sample mean under its assumptions. It is not an error interval for a separately retained round-to-nearest execution. Increasing N drives the statistic down without improving that nominal execution. This is not the already documented small-N accident of all copies agreeing.

The [CESTAC presentation by Jézéquel](https://calcul.math.cnrs.fr/attachments/spip/IMG/pdf/2013_Jezequel_PRCN.pdf) associates the calculation with the mean of the stochastic executions. [Sohier et al.](https://arxiv.org/abs/1807.09655) examine the statistical interpretation of stochastic accuracy measures.

**Remedy:** retain the nominal result for porting/debugging, but report the sample mean and its uncertainty separately. Do not attach the mean's confidence width to the nominal value or describe it as that value's digits. If estimating nominal accuracy, account for displacement and state the model; merely changing the Student-t table does not fix the conceptual mismatch. Equal-probability rounding and operand-keyed repeated coins also warrant validation of the estimator's assumptions. This requires a deliberate design amendment and output tests.

### R9 — P2: `SecondOrder` has a non-associative `Semigroup` instance

**Location:** `lib/Metron/Affine.hs:200–208`.

Combination rounds each sum upward to three significant digits. Parenthesisation therefore matters. `LawProbe.hs` constructs three values through public affine operations and obtains:

```text
(a <> b) <> c: SecondOrder ... Just (1030 % 1)
a <> (b <> c): SecondOrder ... Just (1020 % 1)
equal: False
```

Both can be conservative estimates, but the Haskell `Semigroup` law is still violated. A traversal, parallel reduction, or routine reassociation may change a nonlinear warning or whether an accessor is accepted.

**Remedy:** either combine exact sizes associatively and round at an explicit boundary, or remove the instance and use an explicitly ordered rounded-combination function. Exact summation needs a size/performance check; do not restore unbounded rational growth accidentally. Add associativity/identity properties to every custom algebraic instance, not just this example.

### R10 — P2, mathematics: exterior operations need a stronger domain and corrected rotation claims

**Locations:** `lib/Metron/Eval.hs:1906–1938`, `lib/Metron/Primitive/Types.hs:160`; design §§3.3 and 3.8, especially `doc/design.md:2686`.

`star` accepts every 3×3 matrix and simply reads three entries:

```metron
star [[0,1,0],[0,0,0],[0,0,0]]  -- [0,0,1]
```

That input is not alternating. If the intended extension to arbitrary matrices were antisymmetric projection, its coefficient would be 1/2 under the existing wedge convention. A Hodge star on bivectors should instead require a bivector or an explicit projection. The present signature does neither.

The document also says a composed rotation is not the exponential of any single bivector, and describes every antisymmetric generator as one plane and one angle. In 3D every proper rotation has a skew-symmetric logarithm, though it is not unique. In higher dimensions a general bivector can contain several independent planes. What fails generally is `exp(A+B) = exp(A) exp(B)` for noncommuting generators. Keeping a list is a useful implementation/uncertainty choice, not evidence of nonexistence of a logarithm. See the [rotation/exponential treatment](https://atc.home.ece.ust.hk/files/mls94-complete.pdf).

There is also an enclosure-tightness limitation, not an unsound bound: `wedge a a` for a bounded uncertain vector does not simplify to exact zero; a chart built from it acquires spurious rotational uncertainty. `algebra.txt` and `more-algebra.txt` show this. Ordinary independent-entry matrices cannot encode all exterior identities reliably.

**Remedy:** correct the mathematical rationale now. Before adding grades, define a grade-indexed alternating representation or a smart-constructor boundary; make matrix embedding/projection explicit. Keep vector exterior products metric-free; Hodge duals and bivector-to-skew-operator conversion require additional structure. Test alternation, graded commutativity, associativity, orientation reversal, and basis transformation under the stated numeric semantics. This is groundwork, not a request to implement full Clifford algebra during the fixes.

### R11 — P2: Cholesky's positive-definiteness contract depends on pivot position

**Locations:** `lib/Metron/Numerical/Linear.hs:240–295`; design §3.5.

```metron
cholesky [[1,0],[0,0]]        -- accepted: [1,0;0,0]
cholesky [[0,0],[0,1]]        -- division by zero
[0,0] +-s [[1,0],[0,0]]      -- [0 ±σ 1, 0]
[0,0] +-s [[0,0],[0,1]]      -- division by zero
```

The implementation comments promise rejection when a pivot reaches zero. `sqrtM 0` instead succeeds; failure only occurs if a later division uses it. Thus the documented strictly positive-definite contract is not enforced consistently. Moreover, valid covariance matrices are positive **semidefinite**, including exact coordinates and linearly dependent measurements, so this is a practical limitation for covariance input.

**Remedy:** enforce the current SPD contract consistently with a clear domain error. Separately adopt a deliberate PSD covariance-factorisation policy if wanted—zero pivots require checking the corresponding residual row/column, or a suitable pivoted factorisation. Do not simply replace division by zero with zero. Test coordinate permutations, zero covariance, rank-one covariance, and genuinely indefinite inputs.

### R12 — P2: the library's `asinh` formula catastrophically cancels

**Location:** `lib/Metron/Prelude.hs:575`; used by hyperbolic anomaly conversion and starters.

```metron
-- double
astro.kepler.asinh (-1e20)  -- -Infinity (log 0)
```

The true result is finite, approximately −46.74485. `log(x + sqrt(x*x+1))` cancels for large negative x and overflows `x*x` for sufficiently large finite inputs. Affine enclosure arithmetic can turn the same cancellation into a domain refusal rather than a useful value.

**Remedy:** use an odd, range-safe implementation, with small-argument and large-magnitude branches, or a backend primitive with matching error propagation. Preserve angle dimensions in its callers. Test positive/negative pairs, near zero, large finite values, and hyperbolic conversion round trips. A library-body change moves its hash and dependent hashes and belongs in the changelog.

### R13 — P2, specification: inverse documentation describes an algorithm that is not implemented

**Locations:** `doc/design.md:2195`, `:6533`; `lib/Metron/Numerical/Linear.hs:91`.

The design says inverse applies a compound derivative and a Neumann-series remainder based on a matrix norm. The implementation performs Gauss–Jordan elimination with scalar affine operations and per-entry settling. There is no corresponding matrix-norm test or Neumann remainder in that path.

This does not by itself make scalar enclosure elimination unsound. It does mean its dependency loss, refusal conditions, and bounds are not the described compound algorithm. The document should describe the implemented guarantee and mark the compound method as future work unless it is actually built. Add independent small-matrix corner checks; residual overlap alone is not proof that an inverse enclosure contains all inverses.

### R14 — P2, mathematics: second-order statistical claims assume more than the declared model

**Locations:** `doc/design.md:904–1008`; `lib/Metron/Affine.hs:639` and nonlinear marking helpers.

The declared statistical nudge has mean zero and variance one, with independence between distinct nudges. The product formula then invokes Isserlis and calls its second-order standard deviation exact. Isserlis requires a Gaussian joint model; the first two moments alone do not imply it.

A counterexample needs no numerical experiment: let Z be +10 and −10 with probability 0.005 each, and 0 otherwise. Then E[Z]=0, Var(Z)=1, but sd(Z²)=sqrt(99), not sqrt(2). It satisfies the stated nudge assumptions. Also, checking derivatives only within one sigma does not bound an arbitrary nonlinear function over an unbounded distribution's full support.

**Remedy:** state which inputs are modelled as Gaussian, distinguish first-order GUM propagation from Gaussian second-order diagnostics, and avoid presenting a local nonlinear warning heuristic as a global uncertainty certificate. If arbitrary finite-variance inputs remain allowed, fourth-moment/distribution assumptions or an unknown remainder are needed. A missing published uncertainty must likewise not be advertised as physical certainty: the astronomy library's zero placeholders and exact adopted numerical constants need explicit modelling context.

## Exterior algebra roadmap

The existing point/delta separation is worth preserving. Affine points are not vectors in an exterior algebra; choosing an origin maps points to displacement vectors, and changing that choice must remain explicit. A unit rescaling need not mint a new frame; the implemented nominal spaces/axes make that distinction well.

Recommended design sequence, before implementation:

1. Define `Λ^k V` independently of a metric. Distinguish a general grade-k element from a decomposable blade. In dimension n, grade k has `choose(n,k)` independent coefficients; avoid storing n^k unconstrained tensor entries as the authoritative form.
2. Use canonical ordered index tuples or blade bitsets, with exact permutation signs and explicit embedding into tensors. Keep zeros and antisymmetry structural, including when coefficients have uncertainty. Treat equality/normalisation policies separately from algebraic membership.
3. Specify which dimensions coefficients carry. Addition needs compatible physical dimensions; wedge multiplies them. A mixed-grade multivector may need homogeneous coefficient dimensions or explicitly dimensioned grade components. Do not silently add a length to an area because both are multivector components.
4. Add orientation and a metric as separate data/constraints for Hodge star, inner products, and identification of V with its dual. The current chart rotations use Euclidean orthonormal bases. General basis changes require distinguishing covariant and contravariant transformations; `R` on every axis is not the universal rule for mixed tensors.
5. Only then add a Clifford product satisfying the chosen metric/signature relation, grade projections, reversal, and rotor action. State the sign and half-angle conventions; do not identify the matrix exponential of a skew operator with the rotor exponential without the representation map.

Reference: [Conrad's Hodge-star notes](https://virtualmath1.stanford.edu/~conrad/diffgeomPage/handouts/star.pdf) make the metric and orientation explicit. The current limited `star` is a Euclidean 3D convenience, not a general implementation of that construction.

Tests should begin with exact rational coefficients and then distinguish enclosure containment from exact symbolic laws. Include 4D non-decomposable bivectors, not only 3D cross-product examples. No new Core constructor is justified merely by the word “multivector”; first assess library/data representations and primitive types against the existing Core change criteria.

## Haskell and reuse assessment

### Keep the useful abstractions

- The binder-aware `traverseChildren` expressed through `Applicative`, with `Identity`/`Const` specialisations, is a good fit. Do not add an ordinary `Functor` to `Term n`: n is a scope index, not an element type.
- `Vec n a` really does vary over elements. Lawful `Functor`, `Foldable`, and `Traversable` instances can replace `vecMap`, `vecToList`-based folds, and `vecTraverse` plumbing while retaining indexed helpers. An `Applicative (Vec n)` additionally needs evidence of n to implement `pure`; do not add a constrained length mechanism solely for symmetry with a list API.
- `Dim` has a natural lawful `Semigroup`/`Monoid` under dimension multiplication, with `dimOne` as identity. It is optional: explicit names may be clearer at dimensional call sites. Do not invent a `Num` instance for dimensions or affine magnitudes whose failure/precision semantics cannot obey its expectations.
- `Spread` and branch-cause accumulation have simple lawful max/union-style meanings. Add law tests and repair R9 before using generic reassociation more broadly.
- Keep backend arithmetic explicitly configured. A conventional `Floating` instance cannot express every domain refusal, precision choice, nudge identity, and sample operation currently represented by `Scalar`.

### Refactoring priorities

1. Split backend-independent matrix traversal from scalar arithmetic and pivot policy. The affine and double kernels currently duplicate list indexing/elimination, but their pivot guarantees differ. Share mechanics without conflating interval certification with nominal or per-copy branching.
2. Centralise range-safe double statistics and floating-point support. Avoid repeated mean/variance/error-estimate implementations.
3. Separate the evaluator's runtime-only strictness marker from lintable Typed Core more explicitly. `strictify` inserts `TPrimApp "(evaluated first)" numT` after lint even for non-number arguments. The runtime knows this convention, but the type no longer carries its advertised invariant. A small prepared-term wrapper or explicitly typed runtime node would make the boundary reviewable; do not merely rerun lint on the current marker.
4. Do not blanket-enable `StrictData` or deep forcing. Closures, cycles, constructor fields, chart rotations, and tensor components deliberately rely on laziness. The measured closure/accumulator fixes are working in the tested cases.
5. The ≤64-component eager-argument rule changes evaluation behaviour deliberately. `first [1, spin 0]` hits the steps limit, while `[1, spin 0].0` returns 1. This is documented in §8, so it is an accepted tradeoff to reconsider, not an undiscovered bug. Component-level demand information would be a better long-term foundation than a size-dependent semantic boundary.

HLint found no hints. Source inspection did not establish a further safe dead-code deletion. Public exports and internal invariant cases should not be called cruft merely because one module currently uses them. Small documentation drift includes the obsolete “another branch is reorganising” sentence in overview, the affine-only introduction in AGENTS, and the “no dispatch on value tags” claim despite runtime `tensor`/`point` destructuring. Group these with R13 rather than making separate cleanup commits for each sentence.

## Haskell package shortlist

Versions below are from the **pinned Nix GHC 9.12 package set**, not assumed from web search results. `packages.json` records versions and broken flags. Source archives for the three leading candidates were inspected; `PackageProbe.hs` compiled and ran with them. This is compatibility evidence, not a completed Metron integration benchmark.

| Package | Internal overlap and recommendation | Fit, costs, and evidence |
|---|---|---|
| **[fp-ieee](https://hackage.haskell.org/package/fp-ieee), 0.1.0.6** | **Adopt behind a small floating-point support module** for next-up/down, FMA, and directed conversions; evaluate its augmented operations for residual handling. | BSD-3-Clause. Pinned source exposes these operations and has dedicated tests. GHC 9.12.3 smoke test passed. Its scaling/subnormal code is substantially more careful than the current handful of helpers. It does not supply Metron's whole running-bound proof or stochastic identity policy; test those separately. Floating/NaN behaviour must remain deliberate. |
| **[integer-roots](https://hackage.haskell.org/package/integer-roots), 1.0.4.0** | **Adopt after a focused benchmark** in place of the internal integer square root, or use immediately as an independent test oracle. | MIT; narrow dependency surface (`base`, `ghc-bignum` here), tests and GHC 9.12 listed. Pinned build and 1,000-digit root smoke test passed. Keep Metron's scaling and enclosure wrapper; this package replaces the exact integer kernel only. Prefer it to all of `arithmoi` for this need. |
| **[statistics](https://hackage.haskell.org/package/statistics), 0.16.5.0** | **Adapt selected pieces**: Student-t quantiles and compensated sums; independent checks for sample summaries. | BSD-2-Clause package; source modules retain their own notices. Compiled on the pinned compiler. Broader dependencies include `math-functions`, `mwc-random`, and vector packages. A 31-df t quantile is 2.039513446396411, avoiding the hand-coded approximation. Its own unscaled standard deviation fails the extreme-scale probes: add a scaling wrapper. Preserve Metron's reproducible ordering and constant-sample behaviour. |
| **[binary](https://hackage.haskell.org/package/binary), compiler-bundled** | **Adapt `Data.Binary.Get`** to replace the hand-written decoder state/offset plumbing. | BSD-3-Clause; already available in the pinned compiler package database. Preserve explicit tags/varints and canonical encoding; do not derive a new `Binary` wire format accidentally. Denominator, length, resource, and semantic checks remain Metron's responsibility. Byte-for-byte round trips and hash golden tests are acceptance criteria. |
| **[hmatrix](https://hackage.haskell.org/package/hmatrix), 0.20.2** | **Use as an independent numerical oracle first**; consider an optional fast numerical path later. | BSD-3-Clause; BLAS/LAPACK, foreign dependencies, and different operation order. Marked unbroken in pinned set, not built in this review. Not a replacement for affine correlation or copy-wise semantics. Dense double solving/decomposition would benefit, but it would need an explicit backend contract and error wrapping. |
| **[linear](https://hackage.haskell.org/package/linear), 1.23.3** | **Reference/adapt**, especially explicit affine-space and covector APIs; retain the generic tensor runtime. | BSD-3-Clause; useful small fixed-dimensional vector/quaternion conventions. Pinned package unbroken, not integration-tested. Its standard numeric class assumptions do not directly fit configured/error-producing `Scalar`; lens and supporting dependencies add cost. It is not a complete exterior-algebra replacement. |
| **[splitmix](https://hackage.haskell.org/package/splitmix), 0.1.3.2** | **Retain the stateless copy-key policy; consider package reuse only behind it.** | BSD-3-Clause; tested upstream PRNG. Replacing a hash finaliser with a mutable sequential stream would break lazy-order and batch independence. Package quality does not establish independence properties of Metron's particular operand-key scheme. |
| **[dimensional](https://hackage.haskell.org/package/dimensional), 1.6.2 upstream** | **Use as a design/reference oracle, not the language type checker.** | BSD-3-Clause, active modern compiler support. Haskell-level dimensions and Metron's runtime HM inference solve different problems; Metron also treats angle as a separate base dimension. Reuse constants/conventions selectively after checking semantics. No pinned integration build performed. |
| **[rounded](https://hackage.haskell.org/package/rounded), 1.1.1 upstream** | **Do not adopt unchanged; investigate for an independent MPFR oracle.** | BSD-3-Clause wrapper over MPFR; published bounds exclude this project's `base-4.21` and `ghc-prim` versions. Requires compatibility work and foreign libraries. It cannot replace affine nudge propagation by itself. A separate C/MPFR test harness may be the simpler first step. |
| **[clifford](https://hackage.haskell.org/package/clifford), 0.1.0.14 upstream** | **Do not adopt as the foundation.** | BSD-3-Clause; published 2014 release has `base <4.9`, old vector/lens constraints, and a broad legacy dependency graph. Its existence does not establish modern quality or compatibility. Use mathematical references and small independently checked prototypes instead. This is not a claim that no other suitable algebra package can exist. |

Existing choices—`megaparsec`, `containers`, `vector`, `async`, Unicode normalisation—already avoid substantial reinvention. No evidence here justifies replacing them. Likewise, moving SHA-256 to a larger cryptography package solely for fashion adds little; hash format/provenance correctness matters more than changing the digest library.

### Established-tool lessons to carry forward

- [MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) specifies precision and rounding explicitly. Use directed, higher-precision reference calculations where a claim is an enclosure; comparisons against the same algorithm at a higher precision are weaker evidence.
- [glibc's accuracy policy](https://sourceware.org/glibc/manual/latest/html_node/Errors-in-Math-Functions.html) does not certify the ad hoc 1/2-ulp function constants in `Double.libmUlps`. Its test threshold is not a universal bound either. The design already marks this open; keep the public claim conditional rather than resolving it by substituting “9 ulps” without further evidence.
- [Al-Mohy and Higham](https://eprints.maths.manchester.ac.uk/1442/) address scaling/squaring overscaling and matrix exponential algorithm choice. Their work is relevant to the generic series path, but a BLAS/Padé substitution still needs a verified enclosure wrapper for affine inputs.
- [JCGM 101](https://doi.org/10.59161/JCGM101-2008) propagates specified input distributions. A standard uncertainty alone does not determine a distribution; Gaussian sampling is a modelling choice, especially for published constants and truncated/domain-limited quantities.
- [Unison's content-addressing model](https://www.unison-lang.org/docs/the-big-idea/) is a useful precedent for immutable terms and mutable names. Metron correctly makes this separation, but hashes do not validate decoding or make log writes transactional.

## Performance and strictness evidence

Each measurement starts a fresh CLI process, including standard-library seeding. Times are single observations under a shared host, not a controlled benchmark comparison. Heap allocation is cumulative; maximum residency is GC-sampled live memory, not total process RSS.

| Workload | Size | Allocated bytes | Max residency bytes | Elapsed seconds |
|---|---:|---:|---:|---:|
| Scalar accumulator | 10,000 | 485,180,024 | 4,535,584 | 0.114 |
| Scalar accumulator | 100,000 | 1,259,900,856 | 4,535,608 | 0.214 |
| Scalar accumulator | 1,000,000 | 9,007,101,280 | 4,535,632 | 1.055 |
| Lazy range consumed by length | 10,000 | 568,559,432 | 4,534,408 | 0.124 |
| Lazy range consumed by length | 100,000 | 2,106,480,408 | 4,535,472 | 0.272 |
| Lazy range consumed by length | 1,000,000 | 17,485,680,408 | 4,534,456 | 1.619 |
| Sampled nonlinear expression | 100 | 397,736,424 | 4,550,320 | 0.104 |
| Sampled nonlinear expression | 1,000 | 400,392,304 | 4,550,344 | 0.127 |
| Sampled nonlinear expression | 10,000 | 426,927,192 | 4,550,368 | 0.124 |

The accumulator and list probes run at `-K1M`. These results support the recent thunk-reuse and closure-narrowing work. They do **not** demonstrate constant memory for all recursive programs or large branch mixtures. The documented retention of stopped Monte Carlo groups remains a known limitation and was not reclassified as a new finding.

The incremental allocation is roughly 8.6 KB per scalar loop step and 17 KB per list step. That is a possible optimisation target, not a demonstrated leak. `-O1` Core contains separate `evalAt_$seval1`/`$srunPrim` for `Magnitude` and `evalAt_$seval`/`$srunPrim1` for `Dbl`, without a `Scalar` dictionary parameter in those signatures. STG retains the specialised evaluators. Therefore “the new Scalar class lost all specialisation” is not supported. `keepFree` also forces its reconstructed environment spine before capturing it. Excerpts are retained in `core-excerpts.txt`.

Static performance risks to measure before rewriting:

- `Numerical.Linear` and the double kernels use lists, repeated `!!`, and end-appends inside matrix loops. A flat indexed buffer can reduce traversal and allocation overhead without changing numeric order; quantify per kernel and matrix size first.
- Matrix exponential positions/hash keys repeatedly include complete operand matrices. Cache immutable operation provenance where measurement shows hashing dominates; do not weaken R1's identity semantics.
- `Store.loadStore` reads all objects and uses several lazy folds; deep dependency histories deserve a large-store residency/stack benchmark. No large-store leak was demonstrated here.
- Avoid replacing ordered sample concatenation with a parallel mean/variance reduction if bit-identical K=1/2/4 output remains a requirement. Mathematically equivalent reductions differ in floating-point rounding.
- The cached precision buckets retain previously demanded constants for the process lifetime. This is deliberate memoisation, not by itself a leak. Measure a long interactive sequence of increasing precisions before setting a cache policy.

## Coverage map

“Source” means the relevant implementation paths were inspected; “suite” means the existing groups ran in both baseline and strengthened runs. It does not claim exhaustive source coverage or independent proof.

| Subsystem / modules | Contract checked | Evidence and outcome |
|---|---|---|
| Lexer, Parser, Syntax, Unicode, Fixity, Desugar | Grouping, unit sugar, operator spellings, literal/index boundaries | Source of shared fixities and quantity/type dispatch; syntax/operator/property suites. No new parsing defect established; the first wedge probe had a shell-escaping mistake and was corrected using `wedge`. |
| Core, TCore, Check, Infer, Type/Base/Syntax/Match, Dimension, Primitive/Types, Builtin | Scope, saturation, kinds, dimensions, inference/lint separation, nominal identities | Source of traversal, checking, matching and frame/point signatures; typed/blind/traversal suites. Runtime strictness-marker boundary noted above; no new accepted ill-typed term reproduced. |
| Affine, Numerical.Approx | Correlation, slack, rounding, bound/stat separation, elementary enclosures | Deep arithmetic/approximation path inspection, exact examples, precision suite. R1, R2, R9, R14. Fixed-point proofs not independently completed. |
| Numerical.Linear, Eval products | Determinants, inversion, covariance, exterior products, rotations | Kernel inspection and algebra probes; tensor/rotation suites. R10, R11, R13; existing uncertainty limitations distinguished from false bounds. |
| Double, Scalar | IEEE values, running bounds, copies, sampling/statistics, backend capability | Deep source inspection and exact rational grid; backend suite. R3, R4, R6–R8. |
| Batch, Branch, Remark, Needs, Compile | Copy identity, branch selection, merging, capability preflight | Source inspection, K=1/2/4 probe, backend/limit suite. Existing split accounting/retention caveats retained; general concurrency proof not performed. |
| Eval, Strictness, Limits, C support | Call-by-need, resource checks, strictness, closure retention | Source, million-step/1 MB stack probes, Core/STG, limit tests. No new leak in tested patterns; documented eager-small-tensor tradeoff reproduced. |
| Charts, spaces, frames, UnitHint | Offset vs delta, rotations, explicit conversion, moving configurations | Primitive types, chart runtime and F3–F7 inspected; chart/frame/unit suites. Same-frame pose relabelling is deliberate body-coordinate semantics, not an accidental missing conversion. |
| Hash, Encode, Store | Canonical encoding, recovery, versioning, persistence | Encoder/decoder/load/sync paths, temporary-store probe, store suite. R5. Durability/concurrency concerns need fault-injection work. |
| Codebase, Resolve/Error, NameResolution, Update, Source, Edit | Names vs hashes, history, dependency propagation, export/edit | Architecture and selected checking/propagation paths; codebase/namespaces/export/edit suites. Known export/history and type-update limitations retained. |
| Driver, Session modules, Command, Repl, Main, Pretty | Settings, diagnostics, backend selection, printing and CLI lifecycle | Source of startup/settings/evaluation/printing boundaries; CLI/REPL/end-to-end suites. Statistical output issue R8; mathematical promise wording needs tightening. |
| Prelude, astronomy library | Constants, solver contracts, anomaly/coordinate formulas | Astro design and selected formulas, existing published-example tests. R12; missing-field-zero and exact-adopted-constant modelling risks noted, not a complete constants re-audit. |
| Build, documentation, test infrastructure | Reproducibility, warnings, correspondence, oracle strength | Build/test/HLint plus history of 106 commits since `dca2dc0`; candidate package smoke tests. Documentation corrections R10/R13/R14 and generator gaps above. |

## Remediation sequence

1. **Restore hard-error guarantees:** R1 and R2 in affine arithmetic; R3 in double bounds. Add independent counterexamples before editing. R1's dependence identity must be settled before broader nudge/refactoring work.
2. **Preserve samples and recoverability:** R4 determinant/pivot paths, R5 decoder validation, R6 stochastic neighbour selection. Test exceptional inputs and copy-wise results, not only printed nominal numbers.
3. **Repair statistics and language promises:** R7 range-safe summaries, R8 estimator/output interpretation, R14 distribution assumptions. These affect the meaning of numerical results; amend the design before implementation.
4. **Fix algebraic contracts:** R9 lawful accumulation, R11 consistent SPD behaviour, R12 stable `asinh`. Keep PSD support as an explicitly designed extension rather than a hidden change to Cholesky.
5. **Align the documentation:** R10 rotation/exterior rationale, R13 actual inverse algorithm, then the small documentation drift. Separate established implementation from future mathematical methods.
6. **Adopt focused packages:** first `fp-ieee` and `integer-roots` behind existing boundaries, then selected `statistics` and `binary` utilities. Preserve operation order, reproducibility and canonical bytes; benchmark the replacement kernels. Do not upgrade the whole toolchain just to obtain a candidate.
7. **Prepare exterior algebra:** write the grade/space/metric/orientation/dimension model and exact-law tests. Only then decide representation and add general grades. Clifford products follow that foundation.
8. **Optimise demonstrated costs:** measure dense kernels, long histories and branch mixtures, then change one bottleneck at a time. Preserve lazy/error semantics and run the existing memory regressions.

Acceptance for correctness fixes: the minimal counterexamples pass, an independently specified property covers the general failure mode, the full suite remains green, K=1/2/4 agrees where promised, and HLint stays clear. Hash-affecting library/desugaring/encoding changes must be recorded and stores recreated according to project policy. No owner input is required to begin the confirmed bug fixes; decisions about estimator meaning, statistical distributions, PSD support and general algebra should be recorded explicitly rather than silently invented.
