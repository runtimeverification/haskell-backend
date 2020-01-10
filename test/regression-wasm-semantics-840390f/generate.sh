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

for spec in \
    simple-arithmetic \
    locals \
    loops \
    memory-concrete-type \
    memory-symbolic-type
do
    kollect "test-$spec" \
        ./kwasm prove --backend haskell \
            tests/proofs/"$spec"-spec.k \
            --def-module KWASM-LEMMAS
done
