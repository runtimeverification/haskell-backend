#!/usr/bin/env bash

set -euo pipefail

kollect=
name=${1:?}
shift

while [[ $# -gt 0 ]]
do
    case "$1" in
        *kore-exec)
            echo -n 'exec $KORE_EXEC '
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

if [[ -z "$kollected" ]]
then
    echo >&2 "Did not collect any Kore files!"
    exit 1
fi
