#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
UPSTREAM_REMOTE=${UPSTREAM_REMOTE:-origin}
UPSTREAM_BRANCH=${UPSTREAM_BRANCH:-master}

git fetch $(git remote get-url $UPSTREAM_REMOTE) $UPSTREAM_BRANCH

TRIGGER_STRING="$1" ; shift

if git --no-pager log --oneline "$UPSTREAM_REMOTE/$UPSTREAM_BRANCH..HEAD" | grep "$TRIGGER_STRING" &>/dev/null; then
    echo 'true'
fi
