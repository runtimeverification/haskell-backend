#!/bin/sh
exec kore-exec \
    test-totalSupply-definition.kore \
    --output test-totalSupply.sh.out \
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
    --prove test-totalSupply-spec.kore \
    --spec-module TOTALSUPPLY-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
