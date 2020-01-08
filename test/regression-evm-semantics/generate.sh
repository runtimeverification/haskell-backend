#!/usr/bin/env bash

set -exuo pipefail

kollect() {
    local name="$1"
    shift
    echo '#!/bin/sh' > "$name.sh"
    "$@" --debug --dry-run | xargs $KORE/scripts/kollect.sh "$name" >> "$name.sh"
    chmod +x "$name.sh"
}

make build-haskell

kollect test-pop1 env MODE=VMTESTS SCHEDULE=DEFAULT \
    ./kevm run --backend haskell \
        tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json

kollect test-add0 env MODE=VMTESTS SCHEDULE=DEFAULT \
    ./kevm run --backend haskell \
        tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json

kollect test-sumTo10 env MODE=VMTESTS SCHEDULE=DEFAULT \
    ./kevm run --backend haskell \
        tests/interactive/sumTo10.evm

for search in \
    branching-no-invalid straight-line-no-invalid \
    branching-invalid straight-line
do
    kollect "test-$search" \
        ./kevm search --backend haskell \
            "tests/interactive/search/$search.evm" \
            "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>"
done

kollect sum-to-n \
    ./kevm prove --backend haskell \
        tests/specs/examples/sum-to-n-spec.k \
        --format-failures --def-module VERIFICATION

mv test-*.sh *.kore $KORE/test/regression-evm-semantics/
