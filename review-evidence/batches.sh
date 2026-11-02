#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
for k in 1 2 4; do
  printf '\nCORES %s determinant\n' "$k"
  timeout 60 "$bin" --no-codebase --backend double --set samples 100 --set cores "$k" 'det [[0 +-s 1]]'
  printf '\nCORES %s branch\n' "$k"
  timeout 60 "$bin" --no-codebase --backend double --set samples 100 --set cores "$k" 'let x = 0 +-s 1; if x > 0 then x*x else -x'
done
