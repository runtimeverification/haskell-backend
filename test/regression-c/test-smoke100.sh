#!/bin/sh
exec kore-exec \
    test-smoke-definition.kore \
    --pattern test-smoke-pgm.kore \
    --output test-smoke100.sh.out \
    --module C \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 40 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --depth 100 \
    "$@"
