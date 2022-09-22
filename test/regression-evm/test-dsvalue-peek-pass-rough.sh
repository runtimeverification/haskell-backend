#!/bin/sh
exec kore-exec \
    test-dsvalue-peek-pass-rough-definition.kore \
    --output test-dsvalue-peek-pass-rough.sh.out \
    --module VERIFICATION \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 40 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove test-dsvalue-peek-pass-rough-spec.kore \
    --spec-module DSVALUE-PEEK-PASS-ROUGH-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
