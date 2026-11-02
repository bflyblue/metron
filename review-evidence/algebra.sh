#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
probe() { printf '\nEXPR: %s\n' "$*"; timeout 60 "$bin" --no-codebase "$@"; }
probe 'let a = [1 +- 0.1, 2 +- 0.1, 3 +- 0.1]; let b = [4 +- 0.1, 5 +- 0.1, 6 +- 0.1]; let w = wedge a b; w + transpose w == 0 * w'
probe 'let a = [1 +- 0.1, 2 +- 0.1, 3 +- 0.1]; let w = wedge a a; w == 0 * w'
probe 'cholesky [[1,0],[0,0]]'
probe 'star [[0,1,0],[0,0,0],[0,0,0]]'
probe 'let a = [1 +- 0.1, 2 +- 0.1, 3 +- 0.1]; let b = [4 +- 0.1, 5 +- 0.1, 6 +- 0.1]; space S = Vec 3 m; chart c on S by wedge a b; rotationOf c'
probe --backend double 'astro.kepler.asinh (-1e20)'
