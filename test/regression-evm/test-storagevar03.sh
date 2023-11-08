#!/bin/sh
exec kore-exec \
    test-storagevar03-definition.kore \
    --output test-storagevar03.sh.out \
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
    --prove test-storagevar03-spec.kore \
    --spec-module STORAGEVAR03-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
