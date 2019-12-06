#!/usr/bin/env bash

set -exuo pipefail

# Configuration
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-true}"

TOP=${TOP:-$(git rev-parse --show-toplevel)}
KEVM_DIR=$TOP/evm-semantics
KORE=${KORE:-$TOP}
export KEVM_DIR KORE

# Prefer to use Kore master
PATH="$KORE/.build/kore/bin${PATH:+:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

$KORE/scripts/checkout-kevm.sh
$KORE/scripts/test-kevm.sh

make -j8 TEST_CONCRETE_BACKEND=haskell TEST_SYMBOLIC_BACKEND=haskell test-interactive-search

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-add0-stats.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-pop1-stats.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-sum-to-10-stats.json" \
    make TEST_CONCRETE_BACKEND=haskell tests/interactive/sumTo10.evm.run-interactive

env KORE_EXEC_OPTS="--rts-statistics $TOP/kevm-sum-to-n-spec-stats.json" \
    make TEST_SYMBOLIC_BACKEND=haskell tests/specs/examples/sum-to-n-spec.k.prove
