#!/usr/bin/env bash

# Collect the intermediate files produced by `krun` and `kprove`
# to produce a standalone Kore test.

# Usage:
#
# krun ... --debug --dry-run | xargs kollect.sh NAME
#
# or
#
# kprove ... --debug --dry-run | xargs kollect.sh NAME
#
# Output:
#   on standard output:
#     A command to run `kore-exec` equivalent to the `krun` or `kprove` command.
#     The `kore-exec` command is replaced by `$KORE_EXEC`, so that variable must
#     be set at runtime.
#   file NAME-definition.kore: `krun` only
#   file NAME-pgm.kore: `krun` only
#   file NAME-pattern.kore: `krun --search` only
#   file NAME-spec.kore: `kprove` only
#   file NAME-vdefinition.kore: `kprove` only

set -euo pipefail

kollect=
name=${1:?}
shift

while [[ $# -gt 0 ]]
do
    case "$1" in
        *kore-exec)
            echo -n '$KORE_EXEC '
            ;;
        */definition.kore)
            cp "$1" "$name-definition.kore"
            echo -n "$name-definition.kore "
            ;;
        --output)
            ;;
        */result.kore)
            dir="$(dirname "$1")"
            if [[ -f "$dir/spec.kore" ]]
            then
                mv "$dir/spec.kore" "$name-spec.kore"
                mv "$dir/vdefinition.kore" "$name-vdefinition.kore"
            elif [[ -f "$dir/pgm.kore" ]]
            then
                mv "$dir/pgm.kore" "$name-pgm.kore"
                ! [[ -f "$dir/pattern.kore" ]] || mv "$dir/pattern.kore" "$name-pattern.kore"
            else
                echo >&2 "$dir does not contain spec.kore or pgm.kore!"
                exit 1
            fi
            rmdir "$dir"
            kollected=1
            ;;
        */pgm.kore)
            echo -n "$name-pgm.kore "
            ;;
        */spec.kore)
            echo -n "$name-spec.kore "
            ;;
        */vdefinition.kore)
            echo -n "$name-vdefinition.kore "
            ;;
        */pattern.kore)
            echo -n "$name-pattern.kore "
            ;;
        *)
            echo -n "$1 "
    esac
    shift
done

echo '"$@"'

if [[ -z "${kollected-}" ]]
then
    echo >&2 "Did not collect any Kore files!"
    exit 1
fi
