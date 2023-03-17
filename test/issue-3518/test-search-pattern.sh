#!/bin/sh
exec kore-exec \
    definition.kore \
    --pattern pgm.kore \
    --output test-search-pattern.sh.out \
    --module LAMBDA \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 40 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt none \
    --log-level \
    warning \
    --enable-log-timestamps \
    --search searchFile.kore \
     \
    --searchType FINAL \
    "$@"
