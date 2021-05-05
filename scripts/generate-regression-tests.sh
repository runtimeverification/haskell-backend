#!/usr/bin/env bash

shopt -s extglob
set -exuo pipefail

kollect() {
    local name="$1"
    shift
    echo '#!/bin/sh' > "$name.sh"
    "$@" | xargs $KORE/scripts/kollect.sh "$name" >> "$name.sh"
    chmod +x "$name.sh"
}

kollect-file() {
    local name="$1"
    local path="$2"
    shift
    shift
    echo '#!/bin/sh' > "$name.sh"
    "$@"
    cat $path | xargs $KORE/scripts/kollect.sh "$name" >> "$name.sh"
    chmod +x "$name.sh"
}

build-evm() {
    cd $KORE
    git clone git@github.com:kframework/evm-semantics.git
    cd evm-semantics
    git submodule update --init --recursive
    make plugin-deps
    make build-haskell
    export PATH=$(pwd)/.build/usr/bin:$PATH
}

build-wasm() {
    cd $KORE
    git clone git@github.com:kframework/wasm-semantics.git
    cd wasm-semantics
    git submodule update --init --recursive
    make build-haskell
}

generate-evm() {
    cd $KORE/evm-semantics

    export \
        TEST_CONCRETE_BACKEND=haskell \
        TEST_SYMBOLIC_BACKEND=haskell \
        TEST_OPTIONS="--dry-run --save-temps" \
        CHECK=true \
        KEEP_OUTPUTS=true

    local testpop1=tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json
    local testadd0=tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json
    local testsumTo10=tests/interactive/sumTo10.evm

    kollect-file test-pop1 "$testpop1.haskell-out" \
        make "$testpop1.run-interactive" -e
    
    kollect-file test-add0 "$testadd0.haskell-out" \
        make "$testadd0.run-interactive" -e
    
    kollect-file test-sumTo10 $testsumTo10.haskell-out \
        make "$testsumTo10.run-interactive" -e

    for search in \
        branching-no-invalid straight-line-no-invalid \
        branching-invalid straight-line
    do
        kollect-file "test-$search" "tests/interactive/search/$search.evm.search-out" \
            make "tests/interactive/search/$search.evm.search" -e
    done
            
    kollect test-sum-to-n \
        make tests/specs/examples/sum-to-n-spec.k.prove -e
}

generate-wasm() {
    cd $KORE/wasm-semantics

    export KPROVE_OPTS="--dry-run --save-temps"

    for spec in \
        simple-arithmetic \
        locals \
        loops
    do
        kollect "test-$spec" \
            make tests/proofs/"$spec"-spec.k.prove -e
    done
    
    kollect "test-memory" \
        make tests/proofs/memory-spec.k.prove -e
    
    kollect "test-wrc20" \
        make tests/proofs/wrc20-spec.k.prove -e
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

build-wasm
generate-wasm
replace-tests "test/regression-wasm" "wasm-semantics"
rm -rf $KORE/wasm-semantics
