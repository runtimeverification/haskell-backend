#!/usr/bin/env bash
set -euxo pipefail

# Disable the Python keyring, otherwise poetry sometimes asks for password. See
#  https://github.com/pypa/pip/issues/7883
export PYTHON_KEYRING_BACKEND=keyring.backends.null.Keyring

KEVM_VERSION=${KEVM_VERSION:-'v1.0.335'}

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

MASTER_COMMIT="$(git rev-parse origin/main)"

FEATURE_BRANCH_NAME=${FEATURE_BRANCH_NAME:-"$(git rev-parse --abbrev-ref HEAD)"}
FEATURE_BRANCH_NAME="${FEATURE_BRANCH_NAME//\//-}"

PYTEST_PARALLEL=${PYTEST_PARALLEL:-2}

if [[ $FEATURE_BRANCH_NAME == "master" ]]; then
  FEATURE_BRANCH_NAME="feature"
fi

# Create a temporary directory and store its name in a variable.
TEMPD=$(mktemp -d)

# Exit if the temp directory wasn't created successfully.
if [ ! -e "$TEMPD" ]; then
    >&2 echo "Failed to create temp directory"
    exit 1
fi

# Make sure the temp directory gets removed and kore-rpc-booster gets killed on script exit.
trap "exit 1"           HUP INT PIPE QUIT TERM
trap 'rm -rf "$TEMPD" && killall kore-rpc-booster'  EXIT

feature_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input k-framework/booster-backend $SCRIPT_DIR/../ --command bash -c "$1"
}

master_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input k-framework/booster-backend github:runtimeverification/hs-backend-booster/$MASTER_COMMIT --command bash -c "$1"
}

cd $TEMPD
git clone --depth 1 --branch $KEVM_VERSION https://github.com/runtimeverification/evm-semantics.git
cd evm-semantics
git submodule update --init --recursive --depth 1 kevm-pyk/src/kevm_pyk/kproj/plugin



feature_shell "make poetry && poetry run -C kevm-pyk -- kevm-dist --verbose build plugin haskell --jobs 4"

feature_shell "make test-prove-pyk PYTEST_PARALLEL=$PYTEST_PARALLEL PYTEST_ARGS='--maxfail=0 --timeout 7200 -vv --use-booster' | tee $SCRIPT_DIR/kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME.log"

if [ ! -e "$SCRIPT_DIR/kevm-$KEVM_VERSION-master-$MASTER_COMMIT.log" ]; then
  master_shell "make test-prove-pyk PYTEST_PARALLEL=$PYTEST_PARALLEL PYTEST_ARGS='--maxfail=0 --timeout 7200 -vv --use-booster' | tee $SCRIPT_DIR/kevm-$KEVM_VERSION-master-$MASTER_COMMIT.log"
fi

cd $SCRIPT_DIR
grep ' call  ' kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME.log > kevm-$KEVM_VERSION-master-$MASTER_COMMIT.$FEATURE_BRANCH_NAME
grep ' call  ' kevm-$KEVM_VERSION-master-$MASTER_COMMIT.log > kevm-$KEVM_VERSION-master-$MASTER_COMMIT.master
python3 compare.py kevm-$KEVM_VERSION-master-$MASTER_COMMIT.$FEATURE_BRANCH_NAME kevm-$KEVM_VERSION-master-$MASTER_COMMIT.master > kevm-$KEVM_VERSION-master-$MASTER_COMMIT-$FEATURE_BRANCH_NAME-compare
