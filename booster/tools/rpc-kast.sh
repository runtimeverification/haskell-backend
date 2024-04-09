#!/usr/bin/env bash

set -euo pipefail
shopt -s extglob
set -o allexport
debug=false
profile=false
verbose=false

run_pretty_json_request() {
    kore_json="$(jq .term $1)"
    if [[ "$kore_json" == "null" ]]; then
        echo "Error: malformed Kore JSON request"
        exit 1
    else
        echo $kore_json | pyk json-to-kore | kast --definition $K_DEFINITION --input kore --output pretty /dev/stdin
   fi
}

run_pretty_json_simplify_response() {
    kore_json="$(jq .result.state.term $1)"
    if [[ "$kore_json" == "null" ]]; then
        echo "Error: malformed Kore JSON 'simplify' response"
        exit 1
    else
        echo $kore_json | pyk json-to-kore | kast --definition $K_DEFINITION --input kore --output pretty /dev/stdin
    fi
}

run_pretty_json_execute_response() {
    kore_json="$(jq .result.state.term.term $1)"
    if [[ "$kore_json" == "null" ]]; then
        echo "Error: malformed Kore JSON 'simplify' response"
        exit 1
    else
        echo $kore_json | pyk json-to-kore | kast --definition $K_DEFINITION --input kore --output pretty /dev/stdin
    fi
}

if [[ $# -eq 0 ]]; then
    run_command='help'
else
    run_command="$1"
fi

if [[ "$run_command" == 'help' ]] || [[ "$run_command" == '--help' ]] ; then
    echo "
        Pretty-print kore-rpc JSON using the K definition specified by K_DEFINITION environment variable.

        usage: rpc-kast --request  : pretty print a kore-rpc request
               rpc-kast --simplify : pretty print a kore-rpc 'simplify' response
               rpc-kast --execute  : pretty print a kore-rpc 'execute' response
    "
    exit 0
fi

case "$run_command" in
    "--request"  ) run_pretty_json_request           "$2"      ;;
    "--simplify" ) run_pretty_json_simplify_response "$2"      ;;
    "--execute" ) run_pretty_json_execute_response "$2"      ;;
    *            ) $0 help; echo "Unknown command $run_command"; exit 1 ;;
esac
