#!/usr/bin/env bash

# using variables from runDirectoryTest.sh

echo "client=$client"
echo "dir=$dir"
echo "arguments=$*"


diff="diff -s -"
# remove "--regenerate" and tweak $diff if it is present

client_args=""
for arg in $*; do
    case "$arg" in
        --regenerate)
            echo "Re-generating expectation files"
            diff="tee"
            ;;
        *)
            client_args+=" $arg"
            ;;
    esac
done

# execute with logging (to a stuck state), compare with time fields removed
echo "Running a request which gets stuck, with logTiming enabled"
${client} \
    execute $dir/state-c.execute ${client_args} -O log-timing=true | \
    jq 'del(.result.logs[].time)' | \
    ${diff} $dir/response-c.json
