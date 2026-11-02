#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
for n in 10000 100000 1000000; do
  printf '\nACCUMULATOR %s\n' "$n"
  timeout 60 "$bin" --no-codebase "let go n acc = if n == 0 then acc else go (n - 1) (acc + 1); go $n 0" +RTS -s -K1M -RTS
  printf '\nLIST LENGTH %s\n' "$n"
  timeout 60 "$bin" --no-codebase "length (range 0 $n)" +RTS -s -K1M -RTS
done
for n in 100 1000 10000; do
  printf '\nMC %s\n' "$n"
  timeout 60 "$bin" --no-codebase --backend double --set cores 1 --set samples "$n" 'exp ((1 +-s 0.01) * (2 +-s 0.02))' +RTS -s -RTS
done
