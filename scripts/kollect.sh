#!/usr/bin/env bash

# Collect the intermediate files produced by `krun` and `kprove`
# to produce a standalone Kore test.

# Usage:
#
# krun ... --save-temps --dry-run | xargs kollect.sh NAME
#
# or
#
# kprove ... --save-temps --dry-run | xargs kollect.sh NAME
#
# Output:
#   on standard output:
#     A command to run `kore-exec` equivalent to the `krun` or `kprove` command.
#     The `kore-exec` command is replaced by `$KORE_EXEC`, so that variable must
#     be set at runtime.

set -euo pipefail

kollected=
name=${1:?}
shift

while [[ $# -gt 0 ]]
do
    case "$1" in
        *kore-exec)
            echo -n '$KORE_EXEC '
            ;;
        --output)
            shift
            ;;
        */definition.kore)
            cp "$1" "$name-definition.kore"
            echo -n "$name-definition.kore "
            ;;
        *.kore)
            cp "$1" "$name-$(basename "$1")"
            echo -n "$name-$(basename "$1") "
            kollected=1
            ;;
        *)
            echo -n "$1 "
    esac
    shift
done

echo '"$@"'

if [[ -z "${kollected:-}" ]]
then
    echo >&2 "Did not collect any Kore files!"
    exit 1
fi

#TODO Mircea: delete temporary folder at the end?
