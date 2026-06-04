#!/usr/bin/env bash

# Round-trip test for the per-request `haskell-logging` JSON-RPC flag.
#
# The request carries a list of entry/context names to capture; the matching
# log entries come back in-band on `haskell-log-entries`.  Uses variables
# provided by runDirectoryTest.sh: ${client} (with port), ${dir}, and "$@".
#
# The capture-and-attach happens in the proxy (booster/tools/booster/Proxy.hs),
# so this test is only meaningful under kore-rpc-booster — see the entry in
# scripts/booster-integration-tests.sh.
#
# Assertions (against the small `a-to-f` definition, whose execute exercises the
# booster-side contexts):
#   1. a name list of booster contexts comes back with a non-empty
#      `haskell-log-entries` array;
#   2. narrowing the list to just ["Proxy"] still captures entries, and *every*
#      captured entry carries a proxy context — i.e. the list selects per
#      request (subset correctness);
#   3. omitting the flag omits `haskell-log-entries` entirely.
#
# We assert on shape/selection rather than diffing a golden file: the captured
# entries contain timing- and scheduling-sensitive content that is not stable.

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
contexts="$workdir/contexts.json"
proxy_only="$workdir/proxy-only.json"
control="$workdir/control.json"

echo "1. execute with a booster-context name list -> non-empty capture"
${client} execute "$dir/state.execute" \
    --param-file "$dir/params-contexts.json" \
    --output "$contexts" ${client_args}
jq -e '.result["haskell-log-entries"] | type == "array" and length > 0' "$contexts" > /dev/null

echo "2. execute selecting only [\"Proxy\"] -> non-empty, and every entry carries a proxy context"
${client} execute "$dir/state.execute" \
    --param-file "$dir/params-proxy-only.json" \
    --output "$proxy_only" ${client_args}
jq -e '.result["haskell-log-entries"] | type == "array" and length > 0' "$proxy_only" > /dev/null
jq -e '.result["haskell-log-entries"] | all((.context | tostring) | test("proxy"))' "$proxy_only" > /dev/null

echo "3. execute WITHOUT the flag (control) -> haskell-log-entries omitted"
${client} execute "$dir/state.execute" \
    --param-file "$dir/params-control.json" \
    --output "$control" ${client_args}
jq -e '.result | has("haskell-log-entries") | not' "$control" > /dev/null

rm -rf "$workdir"
echo "haskell-logging capture round-trip OK"
