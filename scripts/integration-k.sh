#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

# Set the number of concurrent test jobs.
# In order, try:
#  1. the JOBS specified by the user
#  2. the number of processors reported by GNU coreutils' nproc
#  3. the number of processors reported by macOS' sysctl
# or else run single-threaded.
# We must set a limit, or we will surely run out of memory.
[[ -n "${JOBS:-}" ]] || JOBS=$(nproc) || JOBS=$(sysctl -n hw.ncpus) || JOBS=1

if make --version | grep -q 'GNU Make 4' 2>/dev/null
then
    MAKE="make --output-sync --jobs ${JOBS:?} --directory $TOP"
else
    MAKE="make -j ${JOBS:?} -C $TOP"
fi

$MAKE kore
$MAKE build-test
$MAKE test-k
