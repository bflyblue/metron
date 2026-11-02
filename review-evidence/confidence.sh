#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
for n in 100 10000; do
  printf '\nSAMPLES %s\n' "$n"
  timeout 60 "$bin" --no-codebase --backend double --set samples "$n" --set cores 1 '(1 / 10, errorOf (1 / 10), 1 + 1e-16, errorOf (1 + 1e-16))'
done
