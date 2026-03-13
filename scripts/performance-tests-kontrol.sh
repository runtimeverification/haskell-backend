#!/usr/bin/env bash
set -euxo pipefail

# Disable the Python keyring, otherwise poetry sometimes asks for password. See
#  https://github.com/pypa/pip/issues/7883
export PYTHON_KEYRING_BACKEND=keyring.backends.null.Keyring

KONTROL_VERSION=${KONTROL_VERSION:-'master'}

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
. "$SCRIPT_DIR/downstream-perf-lib.sh"

BASELINE_REF=${BASELINE_REF:-origin/master}
HEAD_COMMIT="$(git rev-parse HEAD)"
BASELINE_COMMIT=${BASELINE_COMMIT:-"$(downstream_perf_baseline_commit "$BASELINE_REF")"}
BASELINE_COMMIT_SHORT="$(git rev-parse --short "$BASELINE_COMMIT")"

FEATURE_BRANCH_NAME=${FEATURE_BRANCH_NAME:-"$(git rev-parse --abbrev-ref HEAD)"}
FEATURE_BRANCH_NAME="$(downstream_perf_normalize_feature_branch "$FEATURE_BRANCH_NAME")"

PYTEST_PARALLEL=${PYTEST_PARALLEL:-2}
TIMEOUT_SECONDS=${DOWNSTREAM_PERF_TIMEOUT_SECONDS:-${DOWNSTREAM_PERF_FEATURE_BUDGET_SECONDS:-14400}}
DOWNSTREAM_PERF_SUITE=kontrol
FEATURE_STATUS=running
BASELINE_STATUS=not-run
COMPARE_STATUS=not-run
SKIP_REASON=''
FEATURE_DURATION_SECONDS=''
BASELINE_DURATION_SECONDS=''
FEATURE_LOG=''
BASELINE_LOG=''
COMPARE_FILE=''

# Create a temporary directory and store its name in a variable.
TEMPD=$(mktemp -d)
KEEP_TEMPD=${KEEP_TEMPD:-''}

# Exit if the temp directory wasn't created successfully.
if [ ! -e "$TEMPD" ]; then
    >&2 echo "Failed to create temp directory"
    exit 1
fi

clean_up () {
    downstream_perf_write_manifest_snapshot "${DOWNSTREAM_PERF_MANIFEST:-}"
    if [ -z "$KEEP_TEMPD" ]; then
        rm -rf "$TEMPD"
    fi
    killall kore-rpc-booster || echo "no zombie processes found"
}

# Make sure the temp directory gets removed (unless KEEP_TEMPD is set) and kore-rpc-booster gets killed on script exit.
trap "exit 1"  HUP INT PIPE QUIT TERM
trap clean_up  EXIT

cd $TEMPD
git clone --depth 1 --branch $KONTROL_VERSION https://github.com/runtimeverification/kontrol.git
cd kontrol
git submodule update --init --recursive --depth 1


if [[ $KONTROL_VERSION == "master" ]]; then
  KONTROL_VERSION=$(git name-rev --tags --name-only $(git rev-parse HEAD))
else
  KONTROL_VERSION="${KONTROL_VERSION//\//-}"
fi

KEVM_VERSION="v$(cat deps/kevm_release)"

BUG_REPORT=''
POSITIONAL_ARGS=()

while [[ $# -gt 0 ]]; do
  case $1 in
    --bug-report)
      mkdir -p $SCRIPT_DIR/bug-reports/kontrol-$KONTROL_VERSION-$FEATURE_BRANCH_NAME
      BUG_REPORT="--bug-report --bug-report-dir $SCRIPT_DIR/bug-reports/kontrol-$KONTROL_VERSION-$FEATURE_BRANCH_NAME"
      shift # past argument
      ;;
    -*|--*)
      echo "Unknown option $1"
      exit 1
      ;;
    *)
      POSITIONAL_ARGS+=("$1") # save positional arg
      shift # past argument
      ;;
  esac
done

set -- "${POSITIONAL_ARGS[@]}" # restore positional parameters


# it takes long to clone kevm-pyk, so we just do a shallow clone locally and override pyproject.toml
git clone --depth 1 --branch $KEVM_VERSION https://github.com/runtimeverification/evm-semantics.git
cd evm-semantics
git submodule update --init --recursive --depth 1 kevm-pyk/src/kevm_pyk/kproj/plugin

cd ..

# Patch kontrol
sed -i'' -e "s|git = \"https://github.com/runtimeverification/evm-semantics.git\", tag = \"$KEVM_VERSION\", subdirectory = \"kevm-pyk\"|path = \"evm-semantics/kevm-pyk/\"|g" pyproject.toml
sed -i'' -e "s|'forge', 'build'|'forge', 'build', '--no-auto-detect'|g" src/kontrol/foundry.py
sed -i'' -e "s|'forge', 'build'|'forge', 'build', '--no-auto-detect'|g" src/tests/utils.py
sed -i'' -e "s|'forge', 'build'|'forge', 'build', '--no-auto-detect'|g" src/tests/integration/conftest.py
# update the lock file to keep the build tool from complaining
uv lock

feature_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input kevm/k-framework/haskell-backend $SCRIPT_DIR/../  --command bash -c "export PATH=\"$DOWNSTREAM_PERF_RUNTIME_PATH:\$PATH\"; $1"
}

master_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input kevm/k-framework/haskell-backend github:runtimeverification/haskell-backend/$BASELINE_COMMIT --command bash -c "export PATH=\"$DOWNSTREAM_PERF_RUNTIME_PATH:\$PATH\"; $1"
}

first_existing_file() {
  local candidate=''
  for candidate in "$@"; do
    if [ -e "$candidate" ]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

# Keep nix develop as the primary environment, and add missing tool binaries
# needed by blockchain-k-plugin (k tools + clang + cmake from ~/.local/bin).
K_BIN_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths "github:runtimeverification/k/v$(cat deps/k_release)#k")/bin"
CLANG_BIN_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths github:NixOS/nixpkgs/nixos-24.05#clang_14)/bin"
OPENSSL_OUT_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths nixpkgs#openssl.out)"
OPENSSL_DEV_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths nixpkgs#openssl.dev)"
GMP_OUT_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths nixpkgs#gmp.out)"
GMP_DEV_DIR="$(nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths nixpkgs#gmp.dev)"
OPENSSL_CRYPTO_LIB="$(first_existing_file "$OPENSSL_OUT_DIR/lib/libcrypto.so" "$OPENSSL_OUT_DIR/lib/libcrypto.so.3" "$OPENSSL_OUT_DIR/lib/libcrypto.dylib" "$OPENSSL_OUT_DIR/lib/libcrypto.a")"
OPENSSL_SSL_LIB="$(first_existing_file "$OPENSSL_OUT_DIR/lib/libssl.so" "$OPENSSL_OUT_DIR/lib/libssl.so.3" "$OPENSSL_OUT_DIR/lib/libssl.dylib" "$OPENSSL_OUT_DIR/lib/libssl.a")"
GMP_LIB="$(first_existing_file "$GMP_OUT_DIR/lib/libgmp.so" "$GMP_OUT_DIR/lib/libgmp.so.10" "$GMP_OUT_DIR/lib/libgmp.dylib" "$GMP_OUT_DIR/lib/libgmp.a")"
PLUGIN_TOOLCHAIN_PATH="$HOME/.local/bin:$K_BIN_DIR:$CLANG_BIN_DIR"
DOWNSTREAM_PERF_RUNTIME_PATH="$PLUGIN_TOOLCHAIN_PATH"
PLUGIN_CMAKE_PREFIX_PATH="$OPENSSL_OUT_DIR:$OPENSSL_DEV_DIR:$GMP_OUT_DIR:$GMP_DEV_DIR"
PLUGIN_LIBFF_FLAGS="-DOPENSSL_ROOT_DIR=$OPENSSL_OUT_DIR -DOPENSSL_INCLUDE_DIR=$OPENSSL_DEV_DIR/include -DOPENSSL_CRYPTO_LIBRARY=$OPENSSL_CRYPTO_LIB -DOPENSSL_SSL_LIBRARY=$OPENSSL_SSL_LIB -DGMP_INCLUDE_DIR=$GMP_DEV_DIR/include -DGMP_LIBRARY=$GMP_LIB"

# kompile Kontrol's K dependencies
# Ensure plugin build prerequisites are available on self-hosted runners.
feature_shell "export CMAKE_PREFIX_PATH=\"$PLUGIN_CMAKE_PREFIX_PATH\"; export LIBFF_CMAKE_FLAGS=\"$PLUGIN_LIBFF_FLAGS\"; uv run kdist --verbose build evm-semantics.plugin evm-semantics.haskell kontrol.* --jobs 4"

# kompile the test contracts, to be reused in feature_shell and master_shell. Copy the result from pytest's temp directory
PYTEST_TEMP_DIR=$TEMPD/pytest-temp-dir
mkdir -p $PYTEST_TEMP_DIR
FOUNDRY_DIR=$TEMPD/foundry
mkdir -p $FOUNDRY_DIR
feature_shell "make test-integration TEST_ARGS='--basetemp=$PYTEST_TEMP_DIR -n0 --dist=no -k test_foundry_kompile --update-expected-output'"
cp -r $PYTEST_TEMP_DIR/foundry/* $FOUNDRY_DIR

mkdir -p $SCRIPT_DIR/logs
FEATURE_LOG="$SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-$FEATURE_BRANCH_NAME.log"
BASELINE_LOG="$SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-baseline-$BASELINE_COMMIT_SHORT.log"
COMPARE_FILE="$SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-baseline-$BASELINE_COMMIT_SHORT-$FEATURE_BRANCH_NAME-compare"

# use special options if given, but restore KORE_RPC_OPTS afterwards
FEATURE_SERVER_OPTS=${FEATURE_SERVER_OPTS:-''}
if [ ! -z "${FEATURE_SERVER_OPTS}" ]; then
    echo "Using special options '${FEATURE_SERVER_OPTS}' via KORE_RPC_OPTS"
    if [ ! -z "${KORE_RPC_OPTS:-}" ]; then
        PRIOR_OPTS=${KORE_RPC_OPTS}
    fi
    export KORE_RPC_OPTS=${FEATURE_SERVER_OPTS}
fi

# set test arguments and select which tests to run
QUOTE='"'
TEST_ARGS="--foundry-root $FOUNDRY_DIR --maxfail=0 --numprocesses=$PYTEST_PARALLEL -vv $BUG_REPORT -k 'not (test_kontrol_cse or test_foundry_minimize_proof or test_kontrol_end_to_end)'"

read -r feature_exit feature_duration < <(
    downstream_perf_run_and_log \
        "$FEATURE_LOG" \
        feature_shell \
        "timeout ${TIMEOUT_SECONDS}s make test-integration TEST_ARGS=$QUOTE$TEST_ARGS$QUOTE"
)
FEATURE_DURATION_SECONDS=$feature_duration
killall kore-rpc-booster || echo "no zombie processes found"

if [[ $feature_exit -ne 0 ]]; then
    if [[ $feature_exit -eq 124 ]]; then
        FEATURE_STATUS=timeout
        if [[ $BASELINE_COMMIT == $HEAD_COMMIT ]]; then
            BASELINE_STATUS=skipped
            COMPARE_STATUS=skipped
            SKIP_REASON='feature-run-timeout-baseline-same-as-head'
            exit 1
        fi

        rm -rf $FOUNDRY_DIR/out/proofs
        read -r baseline_exit baseline_duration < <(
            downstream_perf_run_and_log \
                "$BASELINE_LOG" \
                master_shell \
                "timeout ${TIMEOUT_SECONDS}s make test-integration TEST_ARGS=$QUOTE$TEST_ARGS$QUOTE"
        )
        BASELINE_DURATION_SECONDS=$baseline_duration
        killall kore-rpc-booster || echo "no zombie processes found"

        if [[ $baseline_exit -eq 124 ]]; then
            BASELINE_STATUS=timeout
            COMPARE_STATUS=skipped
            SKIP_REASON='feature-and-baseline-run-timeout'
            exit 0
        fi

        if [[ $baseline_exit -ne 0 ]]; then
            BASELINE_STATUS=failure
            COMPARE_STATUS=skipped
            SKIP_REASON='feature-timeout-baseline-failed'
            exit 0
        fi

        BASELINE_STATUS=success
        COMPARE_STATUS=skipped
        SKIP_REASON='feature-run-timeout-baseline-succeeded'
        exit 1
    fi
    FEATURE_STATUS=failure
    if [[ $BASELINE_COMMIT == $HEAD_COMMIT ]]; then
        BASELINE_STATUS=skipped
        COMPARE_STATUS=skipped
        SKIP_REASON='feature-run-failed-baseline-same-as-head'
        exit "$feature_exit"
    fi

    rm -rf $FOUNDRY_DIR/out/proofs
    read -r baseline_exit baseline_duration < <(
        downstream_perf_run_and_log \
            "$BASELINE_LOG" \
            master_shell \
            "timeout ${TIMEOUT_SECONDS}s make test-integration TEST_ARGS=$QUOTE$TEST_ARGS$QUOTE"
    )
    BASELINE_DURATION_SECONDS=$baseline_duration
    killall kore-rpc-booster || echo "no zombie processes found"

    if [[ $baseline_exit -ne 0 ]]; then
        BASELINE_STATUS=failure
        COMPARE_STATUS=skipped
        SKIP_REASON='feature-and-baseline-run-failed'
        exit 0
    fi

    BASELINE_STATUS=success
    COMPARE_STATUS=skipped
    SKIP_REASON='feature-run-failed-baseline-succeeded'
    exit "$feature_exit"
fi

FEATURE_STATUS=success

if [ -z "$BUG_REPORT" ]; then
    if [ ! -z "${PRIOR_OPTS:-}" ]; then
        export KORE_RPC_OPTS=${PRIOR_OPTS}
    else
        unset KORE_RPC_OPTS
    fi
    if [[ $BASELINE_COMMIT == $HEAD_COMMIT ]]; then
      BASELINE_STATUS=skipped
      COMPARE_STATUS=skipped
      SKIP_REASON='baseline-same-as-head'
    else
      rm -rf $FOUNDRY_DIR/out/proofs
      read -r baseline_exit baseline_duration < <(
          downstream_perf_run_and_log \
              "$BASELINE_LOG" \
              master_shell \
              "timeout ${TIMEOUT_SECONDS}s make test-integration TEST_ARGS=$QUOTE$TEST_ARGS$QUOTE"
      )
      BASELINE_DURATION_SECONDS=$baseline_duration
      killall kore-rpc-booster || echo "no zombie processes found"

      if [[ $baseline_exit -ne 0 ]]; then
        BASELINE_STATUS=failure
        COMPARE_STATUS=skipped
        SKIP_REASON='baseline-run-failed'
        exit "$baseline_exit"
      fi

      BASELINE_STATUS=success
    fi
fi

cd $SCRIPT_DIR
if [[ $BASELINE_STATUS == success ]]; then
    python3 compare.py "$FEATURE_LOG" "$BASELINE_LOG" > "$COMPARE_FILE"
    COMPARE_STATUS=success
fi
