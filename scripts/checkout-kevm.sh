#!/usr/bin/env bash

set -exuo pipefail

# Configuration
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-true}"

mkdir -p $(dirname ${KEVM_DIR:?})

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
