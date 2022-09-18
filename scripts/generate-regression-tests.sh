#!/usr/bin/env bash

shopt -s extglob
set -exuo pipefail

kollect() {
    local name="$1"
    mkdir kevm-$name
    mv kevm-bug-$name.tar.gz kevm-$name
    cd kevm-$name
    tar -xf kevm-bug-$name.tar.gz
    rm ./!(kore-exec.sh|spec.kore|vdefinition.kore)
    $KORE/scripts/trim-source-paths.sh *.kore
    cd $KORE/evm-semantics

    local regression_evm=$KORE/test/regression-evm
    local testdir=$regression_evm/kevm-$name

    if [ -d $testdir ]
    then
        echo "Replacing $testdir..."
        rm -rf $testdir
    else
        echo "Creating $testdir..."
    fi

    mv kevm-$name $regression_evm

}

build-evm() {
    cd $KORE
    git clone git@github.com:runtimeverification/evm-semantics.git
    cd evm-semantics
    git submodule update --init --recursive
    make plugin-deps
    export PATH=$(pwd)/.build/usr/bin:$PATH
    make build-haskell
}

generate-evm() {
    cd $KORE/evm-semantics

    export \
        TEST_CONCRETE_BACKEND=haskell \
        TEST_SYMBOLIC_BACKEND=haskell \
        KEVM_OPTS=--bug-report \
        CHECK=true \
        KEEP_OUTPUTS=true

    make tests/specs/examples/sum-to-n-spec.k.prove -s -e
    kollect sum-to-n

    make tests/specs/functional/lemmas-spec.k.prove -s -e
    kollect lemmas

    make tests/specs/benchmarks/storagevar03-spec.k.prove -s -e
    kollect storagevar03

    make tests/specs/erc20/ds/totalSupply-spec.k.prove -s -e
    kollect totalSupply

    make tests/specs/mcd/flipper-addu48u48-fail-rough-spec.k.prove -s -e
    kollect flipper-addu48u48-fail-rough

    make tests/specs/mcd/dsvalue-peek-pass-rough-spec.k.prove -s -e
    kollect dsvalue-peek-pass-rough
}

build-evm
generate-evm
rm -rf $KORE/evm-semantics
