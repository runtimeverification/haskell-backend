#!/usr/bin/env bash
set -euxo pipefail

# Disable the Python keyring, otherwise poetry sometimes asks for password. See
#  https://github.com/pypa/pip/issues/7883
export PYTHON_KEYRING_BACKEND=keyring.backends.null.Keyring

KEVM_VERSION=${KEVM_VERSION:-'master'}

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

MASTER_COMMIT="$(git rev-parse origin/main)"
MASTER_COMMIT_SHORT="$(git rev-parse --short origin/main)"

FEATURE_BRANCH_NAME=${FEATURE_BRANCH_NAME:-"$(git rev-parse --abbrev-ref HEAD)"}
FEATURE_BRANCH_NAME="${FEATURE_BRANCH_NAME//\//-}"

PYTEST_PARALLEL=${PYTEST_PARALLEL:-3}

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
trap 'rm -rf "$TEMPD" && killall kore-rpc-booster || echo "No zombie processes found"'  EXIT

feature_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input k-framework/booster-backend $SCRIPT_DIR/../ --command bash -c "$1"
}

master_shell() {
  GC_DONT_GC=1 nix develop . --extra-experimental-features 'nix-command flakes' --override-input k-framework/booster-backend github:runtimeverification/hs-backend-booster/$MASTER_COMMIT --command bash -c "$1"
}

cd $TEMPD
git clone --depth 1 --branch $KEVM_VERSION https://github.com/runtimeverification/evm-semantics.git
cd evm-semantics

if [[ $KEVM_VERSION == "master" ]]; then
  KEVM_VERSION=$(git name-rev --tags --name-only $(git rev-parse HEAD))
else
  KEVM_VERSION="${KEVM_VERSION//\//-}"
fi

git submodule update --init --recursive --depth 1 kevm-pyk/src/kevm_pyk/kproj/plugin

BUG_REPORT=''
POSITIONAL_ARGS=()

while [[ $# -gt 0 ]]; do
  case $1 in
    --bug-report)
      mkdir -p $SCRIPT_DIR/bug-reports/kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME
      BUG_REPORT="--bug-report --bug-report-dir $SCRIPT_DIR/bug-reports/kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME"
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

feature_shell "make poetry && poetry run -C kevm-pyk -- kdist --verbose build evm-semantics.plugin evm-semantics.haskell --jobs 4"


mkdir -p $SCRIPT_DIR/logs

feature_shell "make test-prove-pyk PYTEST_PARALLEL=$PYTEST_PARALLEL PYTEST_ARGS='--maxfail=0 --timeout 7200 -vv --use-booster $BUG_REPORT' | tee $SCRIPT_DIR/logs/kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME.log"
killall kore-rpc-booster || echo "No zombie processes found"


if [ -z "$BUG_REPORT" ]; then
if [ ! -e "$SCRIPT_DIR/logs/kevm-$KEVM_VERSION-master-$MASTER_COMMIT_SHORT.log" ]; then
  master_shell "make test-prove-pyk PYTEST_PARALLEL=$PYTEST_PARALLEL PYTEST_ARGS='--maxfail=0 --timeout 7200 -vv --use-booster' | tee $SCRIPT_DIR/logs/kevm-$KEVM_VERSION-master-$MASTER_COMMIT_SHORT.log"
  killall kore-rpc-booster || echo "No zombie processes found"
fi

cd $SCRIPT_DIR
python3 compare.py logs/kevm-$KEVM_VERSION-$FEATURE_BRANCH_NAME.log logs/kevm-$KEVM_VERSION-master-$MASTER_COMMIT_SHORT.log > logs/kevm-$KEVM_VERSION-master-$MASTER_COMMIT_SHORT-$FEATURE_BRANCH_NAME-compare
fi