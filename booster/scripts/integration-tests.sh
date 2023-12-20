#!/usr/bin/env bash
set -euxo pipefail

K_VERSION=$(cat deps/k_release)
PLUGIN_VERSION=$(cat deps/blockchain-k-plugin_release)
export PATH="$(nix build github:runtimeverification/k/v$K_VERSION#k.openssl.procps --no-link  --print-build-logs --json | jq -r '.[].outputs | to_entries[].value')/bin:$PATH"

if [ -f cabal.project.local ]; then
    echo "[WARN] local cabal project configuration found"
fi

cabal update
cabal test llvm-integration

# The runDirectoryTest.sh script expects the following env vars to be set
export PLUGIN_DIR=$(nix build github:runtimeverification/blockchain-k-plugin/$PLUGIN_VERSION --no-link --json | jq -r '.[].outputs | to_entries[].value')
cabal build all
KORE_RPC_BOOSTER=$(cabal exec which kore-rpc-booster)
BOOSTER_DEV=$(cabal exec which booster-dev)
KORE_RPC_DEV=$(cabal exec which kore-rpc-dev)
export CLIENT=$(cabal exec which kore-rpc-client)

cd test/rpc-integration
for dir in $(ls -d test-*); do
    name=${dir##test-}
    echo "Running $name..."
    case "$name" in
        "a-to-f" | "diamond")
            SERVER=$BOOSTER_DEV ./runDirectoryTest.sh test-$name $@
            SERVER=$KORE_RPC_DEV ./runDirectoryTest.sh test-$name $@
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name $@
            ;;
        "substitutions" | "vacuous")
            SERVER=$KORE_RPC_DEV ./runDirectoryTest.sh test-$name $@
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name $@
            ;;
        "get-model")
            SERVER=$BOOSTER_DEV ./runDirectoryTest.sh test-$name $@
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name $@
            ;;
        "no-evaluator")
            SERVER=$BOOSTER_DEV ./runDirectoryTest.sh test-$name $@
            ;;
        "foundry-bug-report")
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name --time $@
            SERVER=$KORE_RPC_BOOSTER SERVER_OPTS="--interim-simplification 100" ./runDirectoryTest.sh test-$name --time $@
            ;;
        "imp")
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name --time $@
            ;;
        *)
            SERVER=$KORE_RPC_BOOSTER ./runDirectoryTest.sh test-$name $@
            ;;
    esac
done
