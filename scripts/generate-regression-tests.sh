#!/usr/bin/env bash

shopt -s extglob
set -exuo pipefail

kollect() {
    local name="$1"

    local archive=kevm-bug-$name.tar.gz
    local script=test-$name.sh
    local def=test-$name-definition.kore
    local spec=test-$name-spec.kore
    local tmp=$name-tmp

    cd $KORE/evm-semantics

    mkdir $tmp
    mv $archive $tmp
    cd $tmp
    tar -xf $archive
    rm ./!(kore-exec.sh|spec.kore|vdefinition.kore)
    mv kore-exec.sh $script
    mv vdefinition.kore $def
    mv spec.kore $spec

    $KORE/scripts/trim-source-paths.sh *.kore
    sed -i "s/result.kore/$script.out/g" test-$name.sh
    sed -i "s/vdefinition.kore/$def/g" test-$name.sh
    sed -i "s/spec.kore/$spec/g" test-$name.sh

    mv * $KORE/evm-semantics
    cd $KORE/evm-semantics
    rm -rf $tmp
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

replace-tests() {
    local testdir=$KORE/$1
    local tests=$KORE/$2/test-*

    if [ -d $testdir ]
    then
        rm $testdir/!(*.golden|Makefile)
    else
        mkdir $testdir
        echo "include \$(CURDIR)/../include.mk" > $testdir/Makefile
        echo "" >> $testdir/Makefile
        echo "test-%.sh.out: \$(TEST_DIR)/test-%-*" >> $testdir/Makefile
    fi
    mv $tests $testdir
}

build-evm
generate-evm
replace-tests "test/regression-evm" "evm-semantics"
rm -rf $KORE/evm-semantics
