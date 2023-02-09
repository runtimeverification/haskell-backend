#!/bin/sh
exec kore-exec \
    test-optimism-invariant-definition.kore \
    --output test-optimism-invariant.sh.out \
    --module FOUNDRY-MAIN \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 40 \
    --smt-retry-limit 1 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove test-optimism-invariant-spec.kore \
    --spec-module CALLDATASPEC-TEST-DEPOSITTRANSACTION-EMIT-CREATIONTRUE-SENDER-EQUALS-ORIGIN-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
    "$@"
