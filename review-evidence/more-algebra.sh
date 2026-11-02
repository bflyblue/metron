#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
probe() { printf '\nEXPR: %s\n' "$*"; timeout 60 "$bin" --no-codebase "$@"; }
probe 'let a = [1 +- 0.1, 2 +- 0.1, 3 +- 0.1]; space S = Vec 3 m; chart c on S by wedge a a; rotationOf c'
probe 'cholesky [[0,0],[0,1]]'
probe '[0,0] +-s [[0,0],[0,1]]'
probe '[0,0] +-s [[1,0],[0,0]]'
probe --backend double 'det [[0/0]]'
probe --set steps 10000 'let spin n = spin (n+1); let first v = v.0; first [1, spin 0]'
probe --set steps 10000 'let spin n = spin (n+1); [1, spin 0].0'
