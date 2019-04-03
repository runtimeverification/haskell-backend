#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
EVM_SEMANTICS=$TOP/evm-semantics
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-false}"

mkdir -p $(dirname $EVM_SEMANTICS)

ci_git() {
    git -c user.email='admin@runtimeverification.com' -c user.name='CI Server' "$@"
}

rm -rf $EVM_SEMANTICS
git clone --recurse-submodules 'https://github.com/kframework/evm-semantics' $EVM_SEMANTICS --branch 'master'

cd $EVM_SEMANTICS

# Use the K Nightly build from the Kore integration tests.
rm -rf .build/k/k-distribution/target/release/k
ln -s $TOP/.build/k .build/k/k-distribution/target/release

[[ "$OPAM_SETUP_SKIP" != "false" ]] || ./.build/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev

make build-haskell -B
(   cd .build/k/haskell-backend/src/main/native/haskell-backend
    git log --max-count 1
)

make test-vm-haskell -j8
