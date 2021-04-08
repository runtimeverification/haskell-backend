#!/usr/bin/env bash

# Create a pull request to update the regression test suite.

git fetch --all
if git branch --all | grep -q 'origin/_update'; then
  # _update exists on remote
  git checkout -B _update origin/_update
else
  # _update does not exist on remote
  git checkout -B _update origin/master
fi

export KORE=$(pwd)
./scripts/generate-regression-tests.sh

git add test/regression-evm test/regression-wasm
git commit -m 'Update regression tests'
git push -u origin _update
if ! hub pr list --format '%H%n' | grep -q '_update'; then
  hub pull-request                      \
    --head _update --base master        \
    --reviewer ttuegel --assign ttuegel \
    --labels automerge                  \
    --message 'Update regression tests'
fi