#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
EVM_SEMANTICS=$TOP/evm-semantics
OPAM_SETUP_SKIP="${OPAM_SETUP_SKIP:-false}"

# Prefer to use Kore master
PATH=$(stack path --local-install-root)/bin"${PATH:-:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

mkdir -p $(dirname $EVM_SEMANTICS)

ci_git() {
    git -c user.email='admin@runtimeverification.com' -c user.name='CI Server' "$@"
}

rm -rf $EVM_SEMANTICS
git clone --recurse-submodules 'https://github.com/kframework/evm-semantics' $EVM_SEMANTICS --branch 'master'

cd $EVM_SEMANTICS

# Use the K Nightly build from the Kore integration tests.
rm -rf .build/k/k-distribution/target/release/k
mkdir -p .build/k/k-distribution/target/release
ln -s $TOP/.build/k .build/k/k-distribution/target/release

[[ "$OPAM_SETUP_SKIP" != "false" ]] || ./.build/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev

make build-haskell -B

make test-vm-haskell -j8
