#!/usr/bin/env bash

TOP=${TOP:-$(git rev-parse --show-toplevel)}
export TOP

KEVM_DIR=$TOP/evm-semantics
export KEVM_DIR

# Prefer to use Kore master
PATH="$TOP/.build/kore/bin${PATH:+:}$PATH"
export PATH
