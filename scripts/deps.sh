#!/usr/bin/env bash

set -exuo pipefail

# Dockerfile caches only snapshot dependencies.
# Make non-snapshot dependencies available early.
stack build --only-dependencies --test --no-run-tests --bench --no-run-benchmarks
