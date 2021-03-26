#!/usr/bin/env bash

shopt -s extglob
set -exuo pipefail

kollect() {
    local name="$1"
    shift
    echo '#!/bin/sh' > "$name.sh"
    "$@" --save-temps --dry-run | xargs $KORE/scripts/kollect.sh "$name" >> "$name.sh"
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

    kollect test-pop1 env MODE=VMTESTS SCHEDULE=DEFAULT \
        kevm run --backend haskell \
            tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json
    
    kollect test-add0 env MODE=VMTESTS SCHEDULE=DEFAULT \
        kevm run --backend haskell \
            tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json \
    
    kollect test-sumTo10 env MODE=VMTESTS SCHEDULE=DEFAULT \
        kevm run --backend haskell \
            tests/interactive/sumTo10.evm \
    
    for search in \
        branching-no-invalid straight-line-no-invalid \
        branching-invalid straight-line
    do
        kollect "test-$search" \
            kevm search --backend haskell \
                "tests/interactive/search/$search.evm" \
                "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>"
    done
            
    kollect test-sum-to-n \
        kevm prove --backend haskell \
            tests/specs/examples/sum-to-n-spec.k \
            VERIFICATION --format-failures
}

generate-wasm() {
    cd $KORE/wasm-semantics

    for spec in \
        simple-arithmetic \
        locals \
        loops
    do
        kollect "test-$spec" \
            ./kwasm prove --backend haskell \
                tests/proofs/"$spec"-spec.k \
                KWASM-LEMMAS
    done
    
    kollect "test-memory" \
        ./kwasm prove --backend haskell \
            tests/proofs/memory-spec.k \
            KWASM-LEMMAS \
            --concrete-rules WASM-DATA.wrap-Positive,WASM-DATA.setRange-Positive,WASM-DATA.getRange-Positive
    
    kollect "test-wrc20" \
        ./kwasm prove --backend haskell tests/proofs/wrc20-spec.k WRC20-LEMMAS --format-failures \
        --concrete-rules WASM-DATA.wrap-Positive,WASM-DATA.setRange-Positive,WASM-DATA.getRange-Positive,WASM-DATA.get-Existing,WASM-DATA.set-Extend
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
        # TODO: do we want to "make golden" here?
    fi
    mv $tests $testdir
}

# build-evm
# generate-evm
# replace-tests "test/regression-evm" "evm-semantics"
# rm -rf $KORE/evm-semantics

build-wasm
generate-wasm
replace-tests "test/regression-wasm" "wasm-semantics"
rm -rf $KORE/wasm-semantics
