#!/bin/sh

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

HS_TOP="$TOP/src/main/haskell/kore"
HS_SOURCE_DIRS="$HS_TOP/src $HS_TOP/app $HS_TOP/test $HS_TOP/bench"

find $HS_SOURCE_DIRS \
    \( -name '*.hs' -o -name '*.hs-boot' \) \
    -print0 | xargs -0L1 stylish-haskell -i
