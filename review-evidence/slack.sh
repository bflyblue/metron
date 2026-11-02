#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
probe() { printf '\nEXPR: %s\n' "$*"; timeout 60 "$bin" --no-codebase "$@"; }
probe 'let x = 0 +- (0 +- 1); let y = 0 +- (0 +- 1); (x-y, x*x-y*y)'
probe 'let x = 0 +- (0 +- 1); let y = 0 +- (0 +- 1); exp x - exp y'
probe 'let x = 0 +- (0 +- 1); (x, x*x, x*x == 0)'
