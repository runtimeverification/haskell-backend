#!/usr/bin/env bash
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
#   * EVM_VERSION - Optional revision identifier for the evm-semantics
#                   repository. If given, the run will use this version
#                   of evm-semantics (otherwise using master).
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
    KORE=$(cd "$(dirname "$0")"/.. && pwd)
    log "No working directory, defaulting to $KORE" warn
else
    KORE=$(realpath "$KORE")
    [ -d "$KORE" ] || err "$KORE: no such directory"
fi

pushd "$KORE"
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
    git clone git@github.com:runtimeverification/evm-semantics.git "$EVM_SEMANTICS" || \
        [ -f "${EVM_SEMANTICS}/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md" ] || \
        err "Unable to use $KORE/evm-semantics directory"
else
    EVM_SEMANTICS=$(realpath "${EVM_SEMANTICS}")
    log "Using directory ${EVM_SEMANTICS} for evm-semantics" info
    [ -f "$EVM_SEMANTICS/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md" ] || \
        err "Provided evm-semantics directory '${EVM_SEMANTICS}' appears damaged"
fi

# determine K version to use from $KORE/deps/k, unless provided
# deps/k_release contains a version number, the tag has a prefix 'v'
if [ -z "${K_VERSION}" ]; then
    [ -f "$KORE"/deps/k_release ] && K_VERSION=v$(cat "$KORE"/deps/k_release)
    log "K version set to ${K_VERSION}"
fi

# build evm-semantics
log "Checking out and building ${EVM_VERSION:-latest master} in ${EVM_SEMANTICS}"
cd "${EVM_SEMANTICS}"
git fetch
git checkout "${EVM_VERSION:-master}"
git submodule update --init --recursive

log "Checking out and building K ${K_VERSION} in ${EVM_SEMANTICS}/deps/k"
# if we are under a nix develop shell (NIX variable set), don't build K
if [ -z "$NIX" ]; then
    cd deps
    if [ ! -d k ]; then
        git clone git@github.com:runtimeverification/k.git
    fi
    cd k
    git fetch
    git checkout "$K_VERSION"
    git submodule update --init --recursive
    mvn package -DskipTests || err "Unable to build K ${K_VERSION}"
    PATH=$(pwd)/k-distribution/target/release/k/bin:$PATH
    export PATH
    which kore-exec
    cd "${EVM_SEMANTICS}"
else
    log "Testing nix-provided K (kompile --version)"
    kompile --version || err "K unavailable but NIX=$NIX"
fi

log "Building evm-semantics with dependencies"
make poetry
#poetry -C kevm-pyk run kevm-dist clean
poetry -C kevm-pyk run kevm-dist build plugin
poetry -C kevm-pyk run kevm-dist build -j"$(nproc)"

kollect() {
    local name="$1"

    local script=test-$name.sh
    local def=test-$name-definition.kore
    local spec=test-$name-spec.kore
    local tmp=$name-tmp

    pushd "${EVM_SEMANTICS}"/"$name"

    mkdir "$tmp"
    cp kevm-bug-*.tar.gz "$tmp"
    cd "$tmp"
    tar -xf kevm-bug-*.tar.gz
    rm ./!(kore-exec.sh|spec.kore|vdefinition.kore)
    mv kore-exec.sh "$script"
    mv vdefinition.kore "$def"
    mv spec.kore "$spec"

    $sed -i \
         -e "s,/nix/store/[a-z0-9]*-k-[^/]*maven/include/kframework/,evm-semantics/,g" \
         -e "s,${EVM_SEMANTICS}/deps/k/k-distribution/target/release/k/include/kframework/,evm-semantics/,g" \
         -e "s,${EVM_SEMANTICS}/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/,evm-semantics/,g" \
         -e "s,${EVM_SEMANTICS}/kevm-pyk/src/kevm_pyk/kproj/plugin/,evm-semantics/plugin/,g" \
         ./*.kore
    $sed -i -e "s/result.kore/$script.out/g" \
        -e "s/vdefinition.kore/$def/g" \
        -e "s/spec.kore/$spec/g" \
        "$script"

    cd ..
    mv "$tmp"/* "${EVM_SEMANTICS}"
    rmdir "$tmp"
    popd
}

# test paths will be prefixed with tests/specs, and suffixed with -spec.k.prove
# conecutive entries from a pair indicating the test name followed by its main module
ALL_TESTS=(
        "examples/sum-to-n" "VERIFICATION"
        "functional/lemmas" "VERIFICATION"
        "benchmarks/storagevar03" "VERIFICATION"
        "erc20/ds/totalSupply" "VERIFICATION"
        "mcd/flipper-addu48u48-fail-rough" "VERIFICATION"
        "mcd/dsvalue-peek-pass-rough" "VERIFICATION"
        "benchmarks/functional" "FUNCTIONAL-SPEC-SYNTAX"
)

generate-evm() {
    TARGETS=( "$@" )

    if [ ${#TARGETS[@]} -eq 0 ]; then
        TARGETS=( "${ALL_TESTS[@]}" )
    fi 

    log "Generating test data for tests ${TARGETS[*]}"

    # check that test files actually exist before running anything
    for (( idx=0 ; idx<${#TARGETS[@]} ; idx+=2 )); do
        TEST=${TARGETS[idx]}
        log "Checking tests/specs/$TEST-spec.k"
        [ -f "${EVM_SEMANTICS}"/tests/specs/"$TEST"-spec.k ] || err "$TEST's K file does not exist"
    done

    for (( idx=0 ; idx<${#TARGETS[@]} ; idx+=2 )); do
        TEST=${TARGETS[idx]}
        MOD=${TARGETS[idx+1]}
        log "Running $TEST"
        local testabs=${EVM_SEMANTICS}/tests/specs/$TEST-spec.k
        local testdir
        testdir=${EVM_SEMANTICS}/$(basename "$TEST")
        mkdir "$testdir"
        pushd "$testdir"
        poetry -C "${EVM_SEMANTICS}"/kevm-pyk run kevm-pyk kompile "$testabs" --target haskell --syntax-module "$MOD" --main-module "$MOD" --output .
        poetry -C "${EVM_SEMANTICS}"/kevm-pyk run kevm-pyk prove-legacy "$testabs" --definition . --bug-report-legacy
        log "Collecting data for $TEST"
        kollect "$(basename "$TEST")"
        popd
        rm -rf "$testdir"
    done
}

replace-tests() {
    local testdir=$KORE/$1
    local tests=("$2"/test-*)

    if [ ! -d "$testdir" ]
    then
        mkdir "$testdir"
        echo "include \$(CURDIR)/../include.mk" > "$testdir"/Makefile
        echo "" >> "$testdir"/Makefile
        echo "test-%.sh.out: \$(TEST_DIR)/test-%-*" >> "$testdir"/Makefile
    fi
    mv "${tests[@]}" "$testdir"
}

generate-evm "$@"
replace-tests "test/regression-evm" "${EVM_SEMANTICS}"
rm -rf "$KORE"/evm-semantics
