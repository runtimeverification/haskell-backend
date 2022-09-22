#!/bin/sh
exec kore-exec \
    test-storagevar03-definition.kore \
    --output test-storagevar03.sh.out \
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
    --prove test-storagevar03-spec.kore \
    --spec-module STORAGEVAR03-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
