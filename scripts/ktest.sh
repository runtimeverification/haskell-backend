#!/bin/sh

set -e
set -u
set -o

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

MAKE="make -O -j --directory $TOP"
$MAKE test-k
