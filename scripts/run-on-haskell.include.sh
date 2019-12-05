# Assumes $TOP is defined.
# By default, it shoud be: export TOP=${TOP:-$(git rev-parse --show-toplevel)}

function runOnHaskellFiles() {
    local dir=$1
    shift
    find $dir \
        \( -name '*.hs' -o -name '*.hs-boot' \) \
        -print0 | xargs -0L1 $*
}
