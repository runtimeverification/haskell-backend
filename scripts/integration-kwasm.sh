#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
KWASM_DIR=${KWASM_DIR:-$TOP/wasm-semantics}
KORE=${KORE:-$TOP}
export KWASM_DIR KORE

# Prefer to use Kore master
PATH="$KORE/.build/kore/bin${PATH:+:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

cd $KWASM_DIR

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-simple-arithmetic-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/simple-arithmetic-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-loops-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/loops-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-memory-symbolic-type-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/memory-symbolic-type-spec.k.prove

env KORE_EXEC_OPTS="--rts-statistics $TOP/kwasm-locals-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/proofs/locals-spec.k.prove
