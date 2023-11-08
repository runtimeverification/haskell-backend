#!/bin/sh
exec kore-exec \
    test-sum-to-n-definition.kore \
    --output test-sum-to-n.sh.out \
    --module VERIFICATION \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 125 \
    --smt-retry-limit 3 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-format=oneline \
    --log-level \
    warning \
    --enable-log-timestamps \
    --log-entries \
    DebugTransition \
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
