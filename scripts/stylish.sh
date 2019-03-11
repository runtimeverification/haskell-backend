#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

HS_TOP="$TOP/kore"
HS_SOURCE_DIRS="$HS_TOP/src $HS_TOP/app $HS_TOP/test $HS_TOP/bench"

# Install stylish-haskell in the local .stack-work
stack build stylish-haskell
stylish="$(stack path --local-install-root)/bin/stylish-haskell"

find $HS_SOURCE_DIRS \
    \( -name '*.hs' -o -name '*.hs-boot' \) \
    -print0 | xargs -0L1 "$stylish" -i
