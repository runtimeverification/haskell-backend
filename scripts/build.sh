#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

# Dockerfile caches only snapshot dependencies.
# Make non-snapshot dependencies available early.
stack build --only-dependencies --test --no-run-tests --bench --no-run-benchmarks

MAKE="make -O -j --directory $TOP"
$MAKE clean
$MAKE k-frontend
$MAKE coverage_report haskell_documentation
