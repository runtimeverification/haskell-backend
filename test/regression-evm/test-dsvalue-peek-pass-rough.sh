#!/bin/sh
exec kore-exec \
    test-dsvalue-peek-pass-rough-definition.kore \
    --output test-dsvalue-peek-pass-rough.sh.out \
    --module VERIFICATION \
    --strategy all \
    --max-counterexamples 1 \
    --smt-timeout 125 \
    --smt-retry-limit 3 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log \
    /home/sguest/work/haskell-backend/evm-semantics/tests/specs/mcd/dsvalue-peek-pass-rough-spec.debug-log \
    --log-format=oneline \
    --log-level \
    warning \
    --enable-log-timestamps \
    --log-entries \
    DebugTransition \
    --prove test-dsvalue-peek-pass-rough-spec.kore \
    --spec-module DSVALUE-PEEK-PASS-ROUGH-SPEC \
    --graph-search breadth-first \
     \
     \
     \
     \
     \
     \
    "$@"
