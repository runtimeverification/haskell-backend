#!/usr/bin/env bash


set -exuo pipefail

kollect() {
    local name="$1"
    shift
    echo '#!/bin/sh' > "$name.sh"
    # TODO Mircea: change debug to save-temps after the evm-semantics repo is updated to use the latest backend
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

replace-tests() {
    local testdir=$KORE/$1
    local tests=$KORE/$2/test-*

    if [ -d $testdir ]
    then
        rm $testdir/test-*
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
