#!/usr/bin/env nix-shell
#!nix-shell ../../test.nix -i bash

set -xeou pipefail

dir="${1:?}"; shift

export KORE_EXEC="$(nix-build $dir -A kore --arg release true --no-out-link)/bin/kore-exec"

cd $(dirname $0)

out="${1:?}"; shift

tests=(add0 branching-invalid branching-no-invalid pop1 straight-line-no-invalid straight-line sum-to-n sumTo10)

echo "name,allocated_bytes,max_live_bytes" >"$out"
for each in "${tests[@]}"
do
    ./test-${each}.sh --rts-statistics "$each.json" >/dev/null
    echo "\"$each\",$(jq -r .allocated_bytes <"$each.json" ),$(jq -r .max_live_bytes <"$each.json" )" >>"$out"
    rm "$each.json"
done
