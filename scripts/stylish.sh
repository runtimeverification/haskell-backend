#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

source $TOP/scripts/run-on-haskell.include.sh

stack install stylish-haskell-0.9.4.4

runOnHaskellFiles "$TOP" .build/kore/bin/stylish-haskell -i
