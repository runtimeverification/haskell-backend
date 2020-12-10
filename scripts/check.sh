#!/usr/bin/env bash

set -exuo pipefail

export PATH="$HOME/.local/bin${PATH:+:}$PATH"

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

source $TOP/scripts/run-on-haskell.include.sh

if ! $TOP/scripts/git-assert-clean.sh
then
    echo >&2 "Please commit your changes!"
    exit 1
fi

stack build --only-dependencies
if ! $TOP/scripts/git-assert-clean.sh
then
    echo >&2 "Found changes after building dependencies!"
    echo >&2 "Did you forget to run 'stack build' after updating 'stack.yaml'?"
    exit 1
fi
