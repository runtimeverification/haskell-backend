# #!/usr/bin/env bash
#
# generate-regression-tests.sh
#
#   extracts kore files and run scripts for proofs from evm-semantics
#   to update tests/regression-evm files.
#
#   Particular test names can be provided as arguments, for instance,
#
#   $ generate-regression-tests.sh functional/lemmas erc20/ds/totalSupply
#
#   Some environment variables can be used to control working
#   directories and K version
#
#   * KORE - Working directory, default: top-level of haskell-backend.
#
#   * EVM_SEMANTICS - Optional directory with checked-out tree of
#                     evm-semantics.  This tree will be modified,
#                     building master with a custom K version.  If
#                     nothing is provided, $KORE/evm-semantics will be
#                     used.
#
#   * K_VERSION - Optional revision identifier for K repository If
#                 given, this K version will be used as the
#                 evm-semantics dependency (otherwise deps/k_version
#                 will be used).
#
################################################################################

shopt -s extglob
set -e -o pipefail

log() {
    level=${2:-info}
    echo "$(date +'%Y-%m-%d %T.%N') [$level] $1"
}

err() {
    log "$1" error
    log "Aborting script execution." error
    return 1
}

# working directory
if [ -z "$KORE" ]; then
    KORE=$(cd $(dirname $0)/.. && pwd)
    log "No working directory, defaulting to $KORE" warn
else
    KORE=$(realpath $KORE)
    [ -d "$KORE" ] || err "$KORE: no such directory"
fi

pushd $KORE
trap popd EXIT

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
which $sed > /dev/null || err "$sed tool not available"
which git > /dev/null || err "git not available"

# evm-semantics checkout (created unless one is provided)
if [ -z "${EVM_SEMANTICS}" ]; then
    log "No evm-semantics directory provided, using $KORE/evm-semantics" info
    EVM_SEMANTICS=$KORE/evm-semantics
    git clone git@github.com:runtimeverification/evm-semantics.git $EVM_SEMANTICS || \
        [ -f "${EVM_SEMANTICS}/include/kframework/evm.md" ] || \
        err "Unable to use $KORE/evm-semantics directory"
    (cd $EVM_SEMANTICS && git submodule update --init --recursive)
else
    EVM_SEMANTICS=$(realpath ${EVM_SEMANTICS})
    [ -f "$EVM_SEMANTICS/include/kframework/evm.md" ] || \
        err "Provided evm-semantics directory '${EVM_SEMANTICS}' appears damaged"
fi

# determine K version to use from $KORE/deps/k, unless provided
# deps/k_release contains a version number, the tag has a prefix 'v'
if [ -z "${K_VERSION}" ]; then
    [ -f $KORE/deps/k_release ] && K_VERSION=v$(cat $KORE/deps/k_release)
    log "K version set to ${K_VERSION}"
fi

kollect() {
    local name="$1"

    local archive=kevm-bug-$name.tar.gz
    local script=test-$name.sh
    local def=test-$name-definition.kore
    local spec=test-$name-spec.kore
    local tmp=$name-tmp

    cd ${EVM_SEMANTICS}

    mkdir $tmp
    mv $archive $tmp
    cd $tmp
    tar -xf $archive
    rm ./!(kore-exec.sh|spec.kore|vdefinition.kore)
    mv kore-exec.sh $script
    mv vdefinition.kore $def
    mv spec.kore $spec

    $sed -i -e "s,${EVM_SEMANTICS}/,evm-semantics/,g" *.kore
    $sed -i -e "s/result.kore/$script.out/g" \
        -e "s/vdefinition.kore/$def/g" \
        -e "s/spec.kore/$spec/g" \
        $script

    cd ..
    mv $tmp/* .
    rmdir $tmp
}

build-evm() {
    log "Checking out latest master in ${EVM_SEMANTICS}"
    cd ${EVM_SEMANTICS}
    git checkout master
    git pull
    git submodule update --init --recursive
    log "Manually setting K dependency to ${K_VERSION}"
    (cd deps/k && git checkout ${K_VERSION} && git submodule update --init --recursive)
    log "Building evm-semantics with dependencies"
    make deps plugin-deps poetry kevm-pyk
    export PATH=$(pwd)/.build/usr/bin:$PATH
    make build-haskell
}

# test paths will be prefixed with tests/specs, and suffixed with -spec.k.prove
ALL_TESTS="\
        examples/sum-to-n \
        functional/lemmas \
        benchmarks/storagevar03 \
        erc20/ds/totalSupply \
        mcd/flipper-addu48u48-fail-rough \
        mcd/dsvalue-peek-pass-rough \
        benchmarks/functional \
        "

generate-evm() {
    local prior=$(pwd)

    TARGETS=$@

    if [ -z "$TARGETS" ]; then
        TARGETS=$ALL_TESTS
    fi

    log "Generating test data for tests $TARGETS"

    cd ${EVM_SEMANTICS}

    # FIXME check that test files actually exist before running anything?

    export \
        TEST_CONCRETE_BACKEND=haskell \
        TEST_SYMBOLIC_BACKEND=haskell \
        CHECK=true \
        KEEP_OUTPUTS=true

    for TEST in $TARGETS; do
        log "Running $TEST"
        make tests/specs/$TEST-spec.k.prove -e  KPROVE_OPTS="--bug-report"
        log "Collecting data for $TEST"
        kollect $(basename $TEST)
    done
}

replace-tests() {
    local testdir=$KORE/$1
    local tests=$2/test-*

    if [ ! -d $testdir ]
    then
        mkdir $testdir
        echo "include \$(CURDIR)/../include.mk" > $testdir/Makefile
        echo "" >> $testdir/Makefile
        echo "test-%.sh.out: \$(TEST_DIR)/test-%-*" >> $testdir/Makefile
    fi
    mv $tests $testdir
}

build-evm
generate-evm $@
replace-tests "test/regression-evm" ${EVM_SEMANTICS}
rm -rf $KORE/evm-semantics
