#!/usr/bin/env bash

set -exuo pipefail

merge_branch="$1" ; shift
[[ -z "$1" ]] || { linear="$1" ; shift ; }

# check "ahead of master"
common_hash="$(git rev-parse "$merge_branch")"
merge_base_hash="$(git merge-base "$merge_branch" 'HEAD')"

if [[ "$common_hash" != "$merge_base_hash" ]]; then
    echo "HEAD not based on '$merge_branch'" >&2
    exit 1
fi

[[ ! -z "$linear" ]] || exit 0

# check linear history
for rev in $(git rev-list HEAD "^$merge_branch"); do
    if git rev-parse "$rev^"'2' &>/dev/null; then
        echo "Merge commit found: $rev" >&2
        exit 1
    fi
done
