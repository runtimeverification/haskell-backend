#!/usr/bin/env bash

set -e

find "$@" \( -name '*.hs' -o -name '*.hs-boot' \) \
    -execdir stylish-haskell -i '{}' \; \
    && $(dirname "$0")/git-assert-clean.sh
