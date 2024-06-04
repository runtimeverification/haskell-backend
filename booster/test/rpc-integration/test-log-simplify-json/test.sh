#!/usr/bin/env bash

set -exuo pipefail

# using variables from runDirectoryTest.sh

echo "client=$client"
echo "dir=$dir"
echo "arguments=$*"

diff="git diff --no-index"
# remove "--regenerate" and tweak $diff if it is present

regenerate () {
    cp $2 $1
}

client_args=""
for arg in $*; do
    case "$arg" in
        --regenerate)
            echo "Re-generating expectation files"
            diff="regenerate"
            ;;
        *)
            client_args+=" $arg"
            ;;
    esac
done

# send a simplification request and compare the log files
echo "Running a request which will produce the simplify-log.txt log file"
${client} \
    send $dir/state.send ${client_args} > /dev/null

if [ -n "${SERVER_PID}" ]; then
    timeout 10s bash -c "while kill -2 ${SERVER_PID} 2>/dev/null; do sleep 1; done"
fi
${diff} $dir/simplify-log.txt.golden $dir/simplify-log.txt
