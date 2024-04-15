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
    send $dir/state-002.send ${client_args} > /dev/null
${diff} $dir/simplify-log.txt.golden $dir/simplify-log.txt
