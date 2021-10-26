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
    shift 2
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
    export PATH=$(pwd)/.build/usr/bin:$PATH
    make build-haskell
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

    local testpop1=tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmIOandFlowOperations/pop1.json
    local testadd0=tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json
    local testmul0=tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/mul0.json
    local testsha3_bigSize=tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmSha3Test/sha3_bigSize.json
    local testand0=tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmBitwiseLogicOperation/and0.json
    local testsumTo10=tests/interactive/sumTo10.evm

    kollect-file test-pop1 "$testpop1.haskell-out" \
        make "$testpop1.run-interactive" -e

    kollect-file test-add0 "$testadd0.haskell-out" \
        make "$testadd0.run-interactive" -e

    kollect-file test-mul0 "$testmul0.haskell-out" \
        make "$testmul0.run-interactive" -e

    kollect-file test-and0 "$testand0.haskell-out" \
        make "$testand0.run-interactive" -e

    kollect-file test-sha3_bigSize "$testsha3_bigSize.haskell-out" \
        make "$testsha3_bigSize.run-interactive" -e

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
        make tests/specs/examples/sum-to-n-spec.k.prove -s -e

    kollect test-lemmas \
        make tests/specs/functional/lemmas-spec.k.prove -s -e

    kollect test-storagevar03 \
        make tests/specs/benchmarks/storagevar03-spec.k.prove -s -e

    kollect test-totalSupply \
        make tests/specs/erc20/ds/totalSupply-spec.k.prove -s -e

    kollect test-addu48u48 \
        make tests/specs/mcd/flipper-addu48u48-fail-rough-spec.k.prove -s -e

    $KORE/scripts/trim-source-paths.sh *.kore
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
                KWASM-LEMMAS --dry-run --save-temps
    done

    kollect "test-memory" \
        ./kwasm prove --backend haskell \
            tests/proofs/memory-spec.k \
            KWASM-LEMMAS \
            --concrete-rules WASM-DATA.wrap-Positive,WASM-DATA.setRange-Positive,WASM-DATA.getRange-Positive \
            --dry-run --save-temps

    kollect "test-wrc20" \
        ./kwasm prove --backend haskell tests/proofs/wrc20-spec.k WRC20-LEMMAS --format-failures \
        --concrete-rules WASM-DATA.wrap-Positive,WASM-DATA.setRange-Positive,WASM-DATA.getRange-Positive,WASM-DATA.get-Existing,WASM-DATA.set-Extend \
        --dry-run --save-temps

    $KORE/scripts/trim-source-paths.sh *.kore
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
