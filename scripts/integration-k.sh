#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
export PATH="$(stack path --local-bin)${PATH:+:$PATH}"

if make --version | grep -q 'GNU Make 4' 2>/dev/null
then
    MAKE="make --output-sync --jobs --directory $TOP"
else
    MAKE="make -j -C $TOP"
fi

$MAKE test-k
