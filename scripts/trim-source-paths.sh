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

$sed \
   -e "s|$KORE||g" \
    -i "$@"
