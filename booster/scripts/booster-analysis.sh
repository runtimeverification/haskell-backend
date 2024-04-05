#!/usr/bin/env bash
set -euxo pipefail

# Environment variables:
#   LOG_DIR: path to bug report run logs, defaults to $BUG_REPORT_DIR-logs
#   PARALLEL: number of bug reports to process in parallel, defaults to $(nproc)

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"


PARALLEL=${PARALLEL:-$(nproc)}

BUG_REPORT_DIR=$1

nix_shell() {
  GC_DONT_GC=1 nix develop $SCRIPT_DIR/..#cabal --extra-experimental-features 'nix-command flakes' --command bash -c "$1"
}

nix_shell "cabal build kore-rpc-booster"

export SERVER=$(nix_shell "cabal exec which kore-rpc-booster")

nix_shell "cabal build kore-rpc-client"

export CLIENT=$(nix_shell "cabal exec which kore-rpc-client")

export LOG_DIR=${LOG_DIR:-"$BUG_REPORT_DIR-logs"}

mkdir -p $LOG_DIR

K_VERSION=$(cat $SCRIPT_DIR/../deps/k_release)
export PATH="$(nix build github:runtimeverification/k/v$K_VERSION#k.openssl.procps.secp256k1 --no-link  --print-build-logs --json | jq -r '.[].outputs | to_entries[].value')/bin:$PATH"
PLUGIN_VERSION=$(cat $SCRIPT_DIR/../deps/blockchain-k-plugin_release)
export PLUGIN_DIR=$(nix build github:runtimeverification/blockchain-k-plugin/$PLUGIN_VERSION --no-link --json | jq -r '.[].outputs | to_entries[].value')



run_tarball(){
  echo "######## $1 ########";
  $SCRIPT_DIR/run-with-tarball.sh $1 -l Aborts --print-stats 2>&1 | tee $LOG_DIR/$(basename $1).out;
}

export -f run_tarball
export SCRIPT_DIR

find $BUG_REPORT_DIR -name \*tar -print0 | xargs -0 -t -I {} -P $PARALLEL bash -c 'run_tarball "$@"' $(basename {}) {}

# for tar in $(find $BUG_REPORT_DIR -name \*tar );
# do
#   echo "######## $tar ########";
#   $SCRIPT_DIR/run-with-tarball.sh $tar -l Aborts --print-stats 2>&1 | tee $LOG_DIR/$(basename $tar).out;
# done

cd $LOG_DIR

# Counting abort reasons
grep -e "Uncertain about" *log | sed -e 's,/tmp/tmp.[^/]*/evm-semantics/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/,,' -e "s/.*Uncertain about \(.*\)$/\1/" -e "s/jumpi.true :.*/jumpi.true/" | nix_shell "runghc --ghc-arg='-package extra' --ghc-arg='-package containers' $SCRIPT_DIR/Count.hs" > abort_reasons.count

# Counting uncertain conditions by rule and actual outcome in kore-rpc
grep -E -e "^\[Aborts.*Uncertain about a condition| Booster aborted, kore yields"  *log | sed -n -e '/Uncertain about/,/yields/{/yields/{!p};p}' | sed  -e 's/\(jumpi\.true\) :.*$/\1/' | sed -n -e 'N;s/.*Uncertain about a condition in \(.*\)\n.*kore yields \(.*\)/ \1 -- \2 /g;p' | less | nix_shell "runghc --ghc-arg='-package extra' --ghc-arg='-package containers' $SCRIPT_DIR/Count.hs" > uncertain_conditions.count
