#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
KWASM_DIR=${KWASM_DIR:-$TOP/wasm-semantics}
KORE=${KORE:-$TOP}
export KWASM_DIR KORE

# Prefer to use Kore master
PATH="$KORE/.build/kore/bin${PATH:+:}$PATH"
export PATH
rm -f .build/k/bin/kore-*

$KORE/scripts/checkout-kwasm.sh
$KORE/scripts/test-kwasm.sh
