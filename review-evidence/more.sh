#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
probe() { printf '\nEXPR: %s\n' "$*"; timeout 60 "$bin" --no-codebase "$@"; }
probe --backend double '((1e100 + 1) - 1e100) / 1e200'
probe --backend double 'atan2 ((1e200 + 1) - 1e200) 1e200'
probe --backend double 'det [[(1e20 + 1) - 1e20]]'
probe --backend double --set samples 100 --set cores 1 'det [[0 +-s 1]]'
probe --backend double --set samples 100 --set cores 1 'errorOf (1e-200 * 1e-200)'
probe 'let a = [1 +- 0.1, 2 +- 0.1, 3 +- 0.1]; let b = [4 +- 0.1, 5 +- 0.1, 6 +- 0.1]; let w = a /\\ b; w + transpose w == 0 * w'
probe '0 +- (0 +-s 1)'
probe '0 +-s (0 +-s 1)'
