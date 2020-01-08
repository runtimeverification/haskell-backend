#!/usr/bin/env bash

set -exuo pipefail

# Configuration
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-true}"

TOP=${TOP:-$(git rev-parse --show-toplevel)}
KEVM_DIR=$TOP/evm-semantics
export KEVM_DIR

# Prefer to use Kore master
PATH="$TOP/.build/kore/bin${PATH:+:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

mkdir -p $(dirname $KEVM_DIR)

rm -rf $KEVM_DIR
git clone --recurse-submodules 'https://github.com/kframework/evm-semantics' $KEVM_DIR --branch 'master'

cd $KEVM_DIR

# Display the HEAD commit on evm-semantics for the log.
git show -s HEAD

# Use the K Nightly build from the Kore integration tests.
rm -rf deps/k/k-distribution/target/release/k
mkdir -p deps/k/k-distribution/target/release
ln -s $TOP/.build/k deps/k/k-distribution/target/release

[[ "$OPAM_SETUP_SKIP" != "false" ]] || ./deps/k/k-distribution/target/release/k/bin/k-configure-opam-dev

make build-haskell -B

make -j8 TEST_CONCRETE_BACKEND=haskell TEST_SYMBOLIC_BACKEND=haskell \
  test-interactive-search \
  tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json.run-interactive \
  tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json.run-interactive \
  tests/interactive/sumTo10.evm.run-interactive \
  tests/specs/examples/sum-to-n-spec.k.prove
