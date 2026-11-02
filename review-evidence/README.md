# Review evidence

Follow-up artifacts prefixed `recheck-main` reproduce the findings on
finished main (`5160cd1`). Files prefixed `fixes-` record the first repair
batch; see [FIXES.md](../FIXES.md) for scope and results. `fixes-before.txt`
intentionally contains failing regressions against the old implementation.

These are diagnostic probes and captured outputs for [REVIEW.md](../REVIEW.md), against commit `d907a4306b484de4a045fb1b0af0da8c95e9f3a3`. They are not new production tests or implementation fixes. Some intentionally provoke errors. A shell script's exit status alone is therefore not its result: inspect the labelled expressions and output.

## Reproduction

Use the pinned project shell. Run from `/tmp/metron-review`. The shell probes record the exact executable path used; adjust their `bin` assignment if rebuilding elsewhere. Build all components before using that executable. Every interpreter or test invocation must stay within the memory cap; individual scripts add their own timeouts but do not create the cap.

```sh
cap() { systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 "$@"; }
nix develop path:$PWD -c cabal -v0 build all
cap timeout 900 nix develop path:$PWD -c cabal test --test-show-details=direct
cap timeout 900 nix develop path:$PWD -c cabal test --test-show-details=direct --test-options='--quickcheck-tests 2000'
cap timeout 900 bash review-evidence/slack.sh
```

Use the same capped command for any other `.sh` probe. Most use `--no-codebase`. `store-probe.sh` instead creates a new `/tmp/metron-review-store.XXXXXX` directory and deliberately inserts corrupt bytes there. It never uses the default database; its printed path identifies the disposable directory.

The standalone Haskell probes use the freshly built local library:

```sh
cap timeout 120 nix develop path:$PWD -c cabal exec -- runghc -package=metron review-evidence/DecoderProbe.hs
cap timeout 120 nix develop path:$PWD -c cabal exec -- runghc -package=metron review-evidence/LawProbe.hs
cap timeout 120 nix develop path:$PWD -c cabal exec -- runghc -package=metron review-evidence/ExtremeProbe.hs
cap timeout 900 nix shell --impure --expr 'import ./review-evidence/package-env.nix' -c runghc review-evidence/PackageProbe.hs
```

The package environment is independent of Metron's Cabal dependencies. It uses the project's pinned nixpkgs input; no global tools or dependencies are installed. The package smoke output also contains Nix build/fetch messages from the first run.

HLint was run on production and test sources with the required extensions:

```sh
nix run nixpkgs#hlint -- -XGHC2024 -XOverloadedRecordDot -XOverloadedStrings -XNoFieldSelectors -XDuplicateRecordFields lib src test
```

## Evidence map

| Files | Purpose |
|---|---|
| `build.txt`, `tests.txt`, `properties.txt`, `hlint.txt` | Baseline build, full suite, increased QuickCheck count, lint. Empty build output means the quiet build succeeded. |
| `slack.*` | R1: false correlation in nonlinear anonymous error. |
| `probes.*`, `more.*`, `more-algebra.*`, `quotient.*` | Uncertain widths, double extremes, stochastic underflow, statistics, determinants, Cholesky, and `asinh`. `more.txt` includes an initial malformed escaped wedge expression; the later algebra probes correct it. |
| `confidence.*` | R8: fixed nominal error versus shrinking sample-mean statistic. |
| `algebra.*`, `more-algebra.*` | Exterior identities, chart rotations and covariance permutation behaviour. |
| `batches.*` | Representative K=1/2/4 comparisons. |
| `DecoderProbe.hs`, `decoder.txt`, `store-probe.sh`, `store.txt` | R5: direct malformed rational decoding and isolated-store startup. |
| `LawProbe.hs`, `law.txt` | R9: non-associative `SecondOrder` combination through public constructors/operations. |
| `ExtremeProbe.hs`, `extremes.txt` | R3: exact-rational containment over 13,068 arithmetic cases. Prints the total violations and first 12 examples. Nonfinite outputs/bounds are excluded from the violation predicate, not certified. |
| `perf.*` | Fresh-process RTS observations; timings include startup and are not controlled comparative benchmarks. |
| `core-excerpts.txt` | Specialised evaluator/primitive signatures from actual `-O1` Core and STG. Full generated dumps remain in the temporary build directory, outside this evidence folder. |
| `packages.json`, `package-db.txt`, `package-sources.txt` | Pinned versions, compiler package database, and source archive provenance. |
| `PackageProbe.hs`, `package-smoke.txt`, `package-env.nix` | Candidate package compatibility and numerical boundary checks. |

The Core build used a separate build directory with `-ddump-simpl -ddump-stg-final -ddump-to-file`, retaining Cabal's normal `-O1` optimisation. The report distinguishes inspected specialised paths from a claim about every possible dispatch. It also distinguishes mathematical counterexamples from empirical performance observations and untested risks.

The existing suite's success does not invalidate the counterexamples: its generators do not cover these same domains. Conversely, a proposed repair must become a proper regression and a general property before implementation can be considered validated.
