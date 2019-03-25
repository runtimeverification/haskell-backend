#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
EVM_SEMANTICS=$TOP/evm-semantics

mkdir -p $(dirname $EVM_SEMANTICS)

git config --global user.email 'admin@runtimeverification.com'
git config --global user.name  'CI Server'

rm -rf $EVM_SEMANTICS
git clone --recurse-submodules 'https://github.com/kframework/evm-semantics' $EVM_SEMANTICS --branch 'master'

cd $EVM_SEMANTICS

(   cd .build/k
    (   cd haskell-backend/src/main/native/haskell-backend
        git fetch $TOP
        git checkout FETCH_HEAD
    )
    git add haskell-backend/src/main/native/haskell-backend
    git commit -m '!!! haskell-backend/src/main/native/haskell-backend: integration testing haskell backend'
)

git add .build/k
git commit -m '!!! .build/k: integration testing haskell backend'

make clean
git submodule update --init --recursive
./.build/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev

make haskell-deps  -B
make build-haskell -B
(   cd .build/k/haskell-backend/src/main/native/haskell-backend
    git log --max-count 1
)

make test-vm-haskell -j8
