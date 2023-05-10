
directory=${1?"Please provide a test directory in a single argument"}

set -eu

pushd $(dirname $0)
shift

dir=$(basename $directory)
bindir=../../.build/kore/bin

server=${SERVER:-$bindir/hs-backend-booster}
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

echo "Starting server"
$server $kore --module ${MODULE?"Unable to find main module"} $server_params &
server_pid=$!

trap 'kill -2 ${server_pid}; popd' ERR EXIT
echo "Server PID ${server_pid}"

sleep 2

for test in $(ls $dir/state-*.json); do
    testname=${test#$dir/state-}
    if [ -f "$dir/params-${testname}" ]; then
        params="--param-file $dir/params-${testname}"
    else
        params=""
    fi
    # choose --send (raw) mode if name ends in "-raw.json"
    if [[ $test == *-raw.json ]]; then
        mode="--send"
    else
        mode="--execute"
    fi
    echo "$client $mode $test $params --expect $dir/response-${testname} $*"
    $client $mode $test $params --expect $dir/response-${testname} $*
done
