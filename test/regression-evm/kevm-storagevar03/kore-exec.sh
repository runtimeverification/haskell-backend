#!/bin/sh
exec kore-exec \
    vdefinition.kore \
    --output result.kore \
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
    --prove spec.kore \
    --spec-module STORAGEVAR03-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
