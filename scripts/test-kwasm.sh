#!/usr/bin/env bash

set -exuo pipefail

cd $KWASM_DIR

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-simple-arithmetic-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/simple-arithmetic-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-loops-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/loops-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-memory-symbolic-type-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/memory-symbolic-type-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-locals-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/locals-spec.k.prove
