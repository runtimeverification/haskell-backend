#!/bin/sh
exec kore-exec \
    test-lemmas-definition.kore \
    --output test-lemmas.sh.out \
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
