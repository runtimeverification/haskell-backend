# Assumes $TOP is defined.
# By default, it shoud be: export TOP=${TOP:-$(git rev-parse --show-toplevel)}

find_haskell_files() {
    local TOP=$1
    shift
    find $TOP -type f -name '*.hs*' '(' ! -path '*/.stack-work*' ')' '(' ! -path '*/dist*' ')' $*
}

function runOnHaskellFiles() {
    local TOP=$1
    shift
    find_haskell_files $TOP -print0 | xargs -0L1 $*
}
