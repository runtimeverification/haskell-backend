#!/usr/bin/env bash

# Generate standalone Kore tests from evm-semantics.
# Usage:
#   1. Clone the `evm-semantics` repository.
#   2. Follow the instructions to prepare the dependencies on your system.
#   3. Set the KORE environment variable in your shell to the location of the
#      `kore` repository.
#   4. Run this script in the root of the `evm-semantics` repository.
#   5. Copy the resulting files back into this directory.

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

kollect test-sum-to-n \
    ./kevm prove --backend haskell \
        tests/specs/examples/sum-to-n-spec.k \
        VERIFICATION \
        --format-failures
