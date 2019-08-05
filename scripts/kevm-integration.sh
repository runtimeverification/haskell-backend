#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
EVM_SEMANTICS=$TOP/evm-semantics
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-true}"

# Prefer to use Kore master
PATH="$TOP/.build/kore/bin${PATH:+:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

mkdir -p $(dirname $EVM_SEMANTICS)

rm -rf $EVM_SEMANTICS
git clone --recurse-submodules 'https://github.com/kframework/evm-semantics' $EVM_SEMANTICS --branch 'master'

cd $EVM_SEMANTICS

# Use the K Nightly build from the Kore integration tests.
rm -rf deps/k/k-distribution/target/release/k
mkdir -p deps/k/k-distribution/target/release
ln -s $TOP/.build/k deps/k/k-distribution/target/release

[[ "$OPAM_SETUP_SKIP" != "false" ]] || ./deps/k/k-distribution/target/release/k/bin/k-configure-opam-dev

make build-haskell -B

make test-interactive-run -j8 TEST_CONCRETE_BACKEND=haskell
