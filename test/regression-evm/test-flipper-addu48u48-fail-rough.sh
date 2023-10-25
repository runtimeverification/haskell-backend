#!/bin/sh
exec kore-exec \
    test-flipper-addu48u48-fail-rough-definition.kore \
    --output test-flipper-addu48u48-fail-rough.sh.out \
    --module VERIFICATION \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 125 \
    --smt-retry-limit 3 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log \
    /home/sguest/work/haskell-backend/evm-semantics/tests/specs/mcd/flipper-addu48u48-fail-rough-spec.debug-log \
    --log-format=oneline \
    --log-level \
    warning \
    --enable-log-timestamps \
    --log-entries \
    DebugTransition \
    --prove test-flipper-addu48u48-fail-rough-spec.kore \
    --spec-module FLIPPER-ADDU48U48-FAIL-ROUGH-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
