#!/usr/bin/env bash
set -u
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
store=$(mktemp -d /tmp/metron-review-store.XXXXXX)
printf 'Temporary store: %s\n' "$store"
timeout 60 "$bin" --codebase "$store" 1
printf '\003\000\000\001\001\000' > "$store/terms/0000000000000000000000000000000000000000000000000000000000000000"
printf 'Load with malformed scalar term:\n'
timeout 60 "$bin" --codebase "$store" 1
printf 'exit=%s\n' "$?"
