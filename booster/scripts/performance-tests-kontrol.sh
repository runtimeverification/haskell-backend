#!/usr/bin/env bash
set -euxo pipefail

# Disable the Python keyring, otherwise poetry sometimes asks for password. See
#  https://github.com/pypa/pip/issues/7883
export PYTHON_KEYRING_BACKEND=keyring.backends.null.Keyring

KONTROL_VERSION=${KONTROL_VERSION:-'master'}

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

MASTER_COMMIT="$(git rev-parse origin/main)"
MASTER_COMMIT_SHORT="$(git rev-parse --short origin/main)"

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
trap 'rm -rf "$TEMPD" && killall kore-rpc-booster || echo "no zombie processes found"'  EXIT

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

# poetry takes too long to clone kevm-pyk, so we just do a shallow clone locally and override pyproject.toml
git clone --depth 1 --branch $KEVM_VERSION https://github.com/runtimeverification/evm-semantics.git
cd evm-semantics
git submodule update --init --recursive --depth 1 kevm-pyk/src/kevm_pyk/kproj/plugin

cd ..

# Patch kontrol
sed -i'' -e "s|git = \"https://github.com/runtimeverification/evm-semantics.git\", tag = \"$KEVM_VERSION\", subdirectory = \"kevm-pyk\"|path = \"evm-semantics/kevm-pyk/\"|g" pyproject.toml
sed -i'' -e "s|'forge', 'build'|'forge', 'build', '--no-auto-detect'|g" src/kontrol/foundry.py
sed -i'' -e "s|'forge', 'build'|'forge', 'build', '--no-auto-detect'|g" src/tests/integration/test_foundry_prove.py

feature_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input kevm/k-framework/booster-backend $SCRIPT_DIR/../ --command bash -c "$1"
}

master_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input kevm/k-framework/booster-backend github:runtimeverification/hs-backend-booster/$MASTER_COMMIT --command bash -c "$1"
}

feature_shell "poetry install && poetry run kdist --verbose build evm-semantics.plugin evm-semantics.haskell kontrol.foundry --jobs 4"

mkdir -p $SCRIPT_DIR/logs

feature_shell "make test-integration TEST_ARGS='--maxfail=0 --numprocesses=$PYTEST_PARALLEL -vv' | tee $SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-$FEATURE_BRANCH_NAME.log"
killall kore-rpc-booster || echo "no zombie processes found"

if [ ! -e "$SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-master-$MASTER_COMMIT_SHORT.log" ]; then
  master_shell "make test-integration TEST_ARGS='--maxfail=0 --numprocesses=$PYTEST_PARALLEL -vv' | tee $SCRIPT_DIR/logs/kontrol-$KONTROL_VERSION-master-$MASTER_COMMIT_SHORT.log"
  killall kore-rpc-booster || echo "no zombie processes found"
fi

cd $SCRIPT_DIR
python3 compare.py logs/kontrol-$KONTROL_VERSION-$FEATURE_BRANCH_NAME.log logs/kontrol-$KONTROL_VERSION-master-$MASTER_COMMIT_SHORT.log > logs/kontrol-$KONTROL_VERSION-master-$MASTER_COMMIT_SHORT-$FEATURE_BRANCH_NAME-compare
