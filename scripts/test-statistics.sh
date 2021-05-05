#!/usr/bin/env nix-shell
#!nix-shell ../test.nix -i bash

# Usage: test-statistics.sh KORE_DIR TEST_DIR TEST_DIR ...
# Output: tabular JSON on standard output

set -eou pipefail

kore_dir="${1:?}"; shift
export KORE_EXEC="$(nix-build "$kore_dir" -A kore --arg release true --no-out-link)/bin/kore-exec"

while [[ $# -gt 0 ]]
do
    test_dir="${1:?}"; shift
    (
        cd "$test_dir"
        for each in $(find ./ -name 'test-*.sh')
        do
            json="${each%sh}.json"
            "${each}" --rts-statistics "$json" >/dev/null
            jq ". | { name: \"$test_dir${each#.}\", allocated_bytes: .allocated_bytes, max_live_bytes: .max_live_bytes }" < "$json"
            rm "$json"
        done
    )
done



