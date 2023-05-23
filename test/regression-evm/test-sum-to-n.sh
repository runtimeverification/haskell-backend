#!/bin/sh
exec kore-exec \
    test-sum-to-n-definition.kore \
    --output test-sum-to-n.sh.out \
    --module VERIFICATION \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 99 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove test-sum-to-n-spec.kore \
    --spec-module SUM-TO-N-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
