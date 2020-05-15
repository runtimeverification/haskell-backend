#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

source $TOP/scripts/run-on-haskell.include.sh

runOnHaskellFiles "$TOP" stylish-haskell -i
