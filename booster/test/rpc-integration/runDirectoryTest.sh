#!/bin/env bash

directory=${1?"Please provide a test directory in a single argument"}

set -eu

pushd $(dirname $0)

dir=$(basename $directory)
bindir=../../.build/kore/bin

server=${SERVER:-$bindir/hs-backend-booster}
client=${CLIENT:-$bindir/rpc-client}

kore=resources/${dir#test-}.kore

echo "Running tests from $dir with definition $kore"

# make sure directory and kore file exist
[ ! -d "./$dir" ] && exit 1
[ ! -f "./$kore" ] && exit 2

echo "Starting server"
$server $kore --module TEST &
server_pid=$!

trap 'kill -9 ${server_pid}; popd' ERR EXIT
echo "Server ${server_pid}"

sleep 2

for test in $(ls $dir/state-*.json); do
    testname=${test#$dir/state-}
    if [ -f "$dir/params-${testname}" ]; then
        params="--param-file $dir/params-${testname}"
    else
        params=""
    fi
    echo "$client --execute $test $params --expect $dir/response-${testname}"
done
