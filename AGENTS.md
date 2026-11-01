# Agent guide

This file tells a coding agent how to work on Metron. Read it before you change anything.

## What Metron is

Metron is a unit-aware calculator language, written in Haskell (GHC 9.12, cabal, a nix flake). Every number carries a dimension that the type checker checks, and every approximate number carries an affine error form, so a result prints with an honest bound or a standard uncertainty. Definitions live in a content-addressed codebase, as in Unison: a name is a label that points at the hash of a term. The project was called `eval` before. It is a proof of concept, and its language and store format can change.

## Documents

| Document | What it holds |
|---|---|
| [doc/overview.md](doc/overview.md) | Start here: goals, principles, the pipeline, the module map, the feature map and the glossary |
| [doc/design.md](doc/design.md) | The specification: every rule, default and decision, with where each is implemented and tested |
| [doc/core.md](doc/core.md) | Why Core is small, its invariants, and the test any change to Core must pass |
| [doc/style.md](doc/style.md) | Haskell style for this project |
| [README.md](README.md), [TUTORIAL.md](TUTORIAL.md) | User-facing introduction and tutorial |
| [CHANGELOG.md](CHANGELOG.md) | What changed, including every change that moves hashes |

## Build, test and run

All commands run from the repository root, inside the flake's shell:

```sh
nix develop path:$PWD -c cabal -v0 build all
nix develop path:$PWD -c cabal test
nix develop path:$PWD -c cabal list-bin metron
```

If direnv loaded the shell, `cabal` works directly. After a dependency change, direnv can hold a stale shell. Use `nix develop path:$PWD` explicitly in that case.

`cabal test` does not rebuild the executable. Run `cabal build all` before you run the `metron` binary, or you test an old build.

To run part of the suite, give tasty a pattern, for example `cabal test --test-options='-p "/affine/"'`. To run the QuickCheck properties at more cases, add `--quickcheck-tests 2000`.

## Safety rules

A Metron expression can ask for more memory than the machine has. Cap every run of `metron` and of `cabal test`:

```zsh
cap() { systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 "$@"; }
cap timeout 120 "$(nix develop path:$PWD -c cabal list-bin metron)" --no-codebase '5 km/h to m/s'
cap timeout 900 nix develop path:$PWD -c cabal test
```

- Write the cap as a shell function. A prefix stored in a variable does not split into words in zsh.
- Do not use `ulimit -v`. GHC's runtime reserves a large address space, and the limit breaks it.
- Use `--no-codebase` for experiments, so that you do not write to the user's store.

## Agent worktrees

A new agent worktree starts from `origin/main`, which can be far behind the local `main`. Before you start, reset your branch onto the local `main`, then make sure that `git merge-base --is-ancestor main HEAD` succeeds.

## The owner's rules

- **No legacy support.** When a design changes, remove what it replaced. Do not strike text through, do not keep the old form working, and do not add hints for old forms.
- **Design first.** Record a decision in doc/design.md, marked `**Decided.**`, before you build it. If the owner has not decided, mark the item `**Open.**` and ask.
- **Hashes can change.** A change to desugaring, the encoding or the standard library can move hashes. Stores are recreated, not migrated. List each hash-affecting change in the changelog.
- **Code follows the design.** When the code and doc/design.md disagree, change one of them deliberately, and say which.

## Lint and format

Run hlint with the project's extensions. Plain `hlint` misreads record-dot syntax and reports false positives. Do not "fix" those.

```sh
hlint -XGHC2024 -XOverloadedRecordDot -XOverloadedStrings -XNoFieldSelectors -XDuplicateRecordFields lib src test
```

Run `fourmolu -i` on each file you touch. Follow [doc/style.md](doc/style.md). The code must build with `-Wall` and no warnings. If `hlint` or `fourmolu` is not on your PATH, use `nix run nixpkgs#hlint --` or `nix run nixpkgs#fourmolu --`.

## Testing norms

- Add a regression test for every bug you fix.
- Add property tests where a rule holds over many inputs. For a risky change, run QuickCheck at a higher count (`--quickcheck-tests 2000` or more).
- Give each new test a timeout, as the existing groups do (`localOption (mkTimeout …)`).
- Where batches are involved (the double backend with `samples N`), make sure that results, tables and limit errors are identical for every `cores` setting. The tests check K = 1, 2 and 4.
- Each design subsection names its test groups under **Tested by:**. Keep those names accurate when you add or rename a group.

## Commits

- Commit in green steps: each commit builds and passes the tests.
- End each commit message with the attribution lines that the harness gives you.
- Update doc/design.md, the changelog and the tests in the same commit as the code they describe.
