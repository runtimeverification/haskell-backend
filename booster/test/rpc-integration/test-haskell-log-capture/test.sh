#!/usr/bin/env bash

# Round-trip test for the per-request `haskell-logging` JSON-RPC flag.
#
# Uses the variables provided by runDirectoryTest.sh: ${client} (already
# carrying "-p <port>"), ${dir} (this directory), and "$@" (extra args).
#
# The capture-and-attach logic lives in the proxy (booster/tools/booster/Proxy.hs),
# so this test is only meaningful against kore-rpc-booster — see the entry in
# scripts/booster-integration-tests.sh.
#
# Assertions:
#   * an `execute` request with `haskell-logging: true` comes back with a
#     non-empty `haskell-log-entries` array on its result;
#   * the same request WITHOUT the flag omits `haskell-log-entries` entirely.
#
# We assert on shape (present-and-non-empty vs absent) rather than diffing a
# golden file: the captured entries contain timing- and scheduling-sensitive
# content that is not stable across runs.

set -exuo pipefail

# runDirectoryTest.sh forwards extra args (e.g. --regenerate). There are no
# golden files here, so drop --regenerate and pass the rest to the client.
client_args=""
for arg in $*; do
    case "$arg" in
        --regenerate) ;;
        *) client_args+=" $arg" ;;
    esac
done

workdir=$(mktemp -d)

with_flag="$workdir/response-with-flag.json"
without_flag="$workdir/response-without-flag.json"

echo "Sending execute request WITH haskell-logging:true"
${client} execute "$dir/state.execute" \
    --param-file "$dir/params-logging.json" \
    --output "$with_flag" ${client_args}

echo "Sending execute request WITHOUT the flag (control)"
${client} execute "$dir/state.execute" \
    --param-file "$dir/params-control.json" \
    --output "$without_flag" ${client_args}

echo "Asserting the flagged response carries a non-empty haskell-log-entries array"
jq -e '.result["haskell-log-entries"] | type == "array" and length > 0' "$with_flag" > /dev/null

echo "Asserting the control response omits haskell-log-entries"
jq -e '.result | has("haskell-log-entries") | not' "$without_flag" > /dev/null

rm -rf "$workdir"
echo "haskell-logging capture round-trip OK"
