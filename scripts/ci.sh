#!/bin/sh

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

if ! command -v stylish-haskell >/dev/null; then
    stack install stylish-haskell
fi

$TOP/scripts/check.sh

MAKE="make -O -j --directory $TOP"
$MAKE clean
$MAKE k-frontend
$MAKE coverage_report haskell_documentation test-k
