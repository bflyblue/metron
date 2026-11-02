#!/usr/bin/env bash
set -u
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
probe() { printf '\nEXPR: %s\n' "$*"; timeout 60 "$bin" --no-codebase "$@"; }
probe '0 +- (1 +-s 1)'
probe '0 +-s (1 +-s 1)'
probe '0 +-s (1 +- 1)'
probe 'cholesky [[0,0],[0,0]]'
probe 'star [[1,2,3],[4,5,6],[7,8,9]]'
probe --backend double 'norm [1e200, 1e200]'
probe --backend double 'norm [1e-200, 1e-200]'
probe --backend double --set samples 100 --set cores 1 '1e-200 * 1e-200'
probe --backend double --set samples 100 --set cores 1 --set rounding nearest 'sd (0 +-s 1e200)'
probe --backend double --set samples 100 --set cores 1 --set rounding nearest 'sd (0 +-s 1e-200)'
probe --backend double 'det [[0.1 + 0.2 - 0.3 - 5.551115123125783e-17]]'
probe --backend double 'fma (2^-537) (2^-538) 0'
probe --backend double 'atan2 (1e200 + 1e190) 1e200'
