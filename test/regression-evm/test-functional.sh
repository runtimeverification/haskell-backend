#!/bin/sh
exec kore-exec \
    test-functional-definition.kore \
    --output test-functional.sh.out \
    --module FUNCTIONAL-SPEC-SYNTAX \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 125 \
    --smt-retry-limit 3 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log \
    /home/sguest/work/haskell-backend/evm-semantics/tests/specs/benchmarks/functional-spec.debug-log \
    --log-format=oneline \
    --log-level \
    warning \
    --enable-log-timestamps \
    --log-entries \
    DebugTransition \
    --prove test-functional-spec.kore \
    --spec-module FUNCTIONAL-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
