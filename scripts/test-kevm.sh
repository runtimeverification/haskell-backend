#!/usr/bin/env bash

set -exuo pipefail

make -j8 TEST_CONCRETE_BACKEND=haskell TEST_SYMBOLIC_BACKEND=haskell test-interactive-search

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-add0-stats${STATS_SUFFIX}.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-pop1-stats${STATS_SUFFIX}.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-sum-to-10-stats${STATS_SUFFIX}.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/interactive/sumTo10.evm.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-sum-to-n-spec-stats${STATS_SUFFIX}.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/specs/examples/sum-to-n-spec.k.prove
