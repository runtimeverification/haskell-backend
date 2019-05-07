# Assumes $TOP is defined.
# By default, it shoud be: export TOP=${TOP:-$(git rev-parse --show-toplevel)}

function runOnHaskellFiles() {
    TOP=$1
    shift

    HS_TOP="$TOP/kore"
    HS_SOURCE_DIRS="$HS_TOP/src $HS_TOP/app $HS_TOP/test $HS_TOP/bench"

    find $HS_SOURCE_DIRS \
        \( -name '*.hs' -o -name '*.hs-boot' \) \
        -print0 | xargs -0L1 $*
}


