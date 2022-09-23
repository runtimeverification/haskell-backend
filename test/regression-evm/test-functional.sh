#!/bin/sh
exec kore-exec \
    test-functional-definition.kore \
    --output test-functional.sh.out \
    --module FUNCTIONAL-SPEC-SYNTAX \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 40 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove test-functional-spec.kore \
    --spec-module FUNCTIONAL-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
