#!/usr/bin/env bash

# Run RPC integration tests using files in a given directory.
# The directory name is expected to match "test-<stem>"
#
# - starts an RPC server (SERVER)
#   - with a kore definition resources/<stem>.kore
#   - if it exists, using an llvm library resources/<stem>.dylib
# - sends the files named test-<stem>/state-<test>.<suffix> as requests
#   - using CLIENT
#   - the file suffix indicates how to send the file:
#     - for suffix ".send", send the json as-is
#     - for suffix "execute", send an "execute" request, with additional
#       parameters from file test-<stem>/params-<test>.json
#     - for suffix "simplify", send a "simplify" request, with additional
#       parameters from file test-<stem>/params-<test>.json
#   - expecting the response to match test-<stem>/response-<test>.json
#
# Environment variables
#   SERVER:      path to RPC server executable
#                  (default <top>/.build/booster/bin/booster)
#   CLIENT:      path to RPC client executable
#                  (default <top>/.build/booster/bin/rpc-client)
#   SERVER_OPTS: additional options to pass to the SERVER
#                  (default: none)

directory=${1?"Please provide a test directory in a single argument"}

set -eu

pushd $(dirname $0)
shift

dir=$(basename $directory)
bindir=../../.build/booster/bin

server=${SERVER:-$bindir/kore-rpc-booster}
client=${CLIENT:-$bindir/rpc-client}

kore=resources/${dir#test-}.kore
kompile=resources/${dir#test-}.kompile
dylib=resources/${dir#test-}.dylib

echo "Running tests from $dir with definition $kore"

# make sure directory and kore file exist
[ ! -d "./$dir" ] && exit 1
if [ ! -f "./$kore" ]; then
  [ ! -f "./$kompile" ] && exit 2
  cd resources
  ./${dir#test-}.kompile
  cd ..
  [ ! -f "./$kore" ] && exit 3
fi

if [ -f "./$dylib" ]; then
    server_params="--llvm-backend-library ./$dylib ${SERVER_OPTS:-""}"
else
    server_params=${SERVER_OPTS:-""}
fi

MODULE=$(grep -o -e "^module [A-Z0-9-]*" ./$kore | tail -1 | sed -e "s/module //")

echo "Starting server: $server $kore --module ${MODULE:-UNKNOWN} $server_params"
$server $kore --module ${MODULE?"Unable to find main module"} $server_params &
server_pid=$!

trap 'kill -2 ${server_pid}; popd' ERR EXIT
echo "Server PID ${server_pid}"

sleep 2

for test in $( ls $dir/state-*.{execute,send,simplify} ); do
    tmp=${test#$dir/state-}
    testname=${tmp%.*}
    # determine send mode from suffix
    mode=${test##*.}
    printf "########## Test: %10s %20s\n" "$mode" "$testname #######"
    if [ -f "$dir/params-${testname}.json" ]; then
        params="--param-file $dir/params-${testname}.json"
    else
        params=""
    fi
    # call rpc-client
    echo "$client --$mode $test $params --expect $dir/response-${testname}.json $*"
    $client --$mode $test $params --expect $dir/response-${testname}.json $*
done
