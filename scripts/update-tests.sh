#!/usr/bin/env bash

set -exuo pipefail

# Create a pull request to update the regression test suite.

git fetch --all
git checkout -B _update origin/_update || git checkout -B _update origin/master

export KORE=$(pwd)
./scripts/generate-regression-tests.sh

git add test/regression-evm test/regression-wasm
git commit -m 'Update regression tests'
git push -u origin _update
if ! hub pr list --format '%H%n' | grep -q '^_update$'; then
  hub pull-request                      \
    --head _update --base master        \
    --reviewer ana-pantilie --assign ana-pantilie \
    --labels automerge                  \
    --message 'Update regression tests'
fi
