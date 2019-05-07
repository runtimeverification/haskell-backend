#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

source $TOP/scripts/run-on-haskell.include.sh

# Install stylish-haskell in the local .stack-work
stack build stylish-haskell
stylish="$(stack path --local-install-root)/bin/stylish-haskell"

runOnHaskellFiles "$TOP" "$stylish" -i
