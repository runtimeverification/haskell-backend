#!/usr/bin/env bash

branch_name="${1:?}"
git status --porcelain \
    | awk '/^UU/{print $2}' \
    | xargs -L 1 git checkout "$branch_name" --
