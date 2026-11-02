#!/usr/bin/env bash
bin=/tmp/metron-review/dist-newstyle/build/x86_64-linux/ghc-9.12.3/metron-0.1.0.0/x/metron/build/metron/metron
timeout 60 "$bin" --no-codebase --backend double 'nextUp 0 / nextUp (nextUp (nextUp 0))'
