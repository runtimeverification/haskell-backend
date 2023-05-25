#!/bin/sh
exec kore-exec \
    test-lemmas-definition.kore \
    --output test-lemmas.sh.out \
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
    --prove test-lemmas-spec.kore \
    --spec-module LEMMAS-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
