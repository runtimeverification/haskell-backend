#!/bin/sh

case $(uname) in
    # MacOS
    Darwin*)
        sed="gsed"
    ;;
    # Assumed to be Linux
    *)
        sed="sed"
    ;;
esac

dir="${KORE}/"

$sed \
   -e "s|$dir||g" \
    -i "$@"
