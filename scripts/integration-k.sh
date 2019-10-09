#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

MAKE="make --output-sync --jobs --directory $TOP"
$MAKE test-k
$MAKE test-bmc
