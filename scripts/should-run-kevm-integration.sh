#!/usr/bin/env bash

set -exuo pipefail

TOP=${TOP:-$(git rev-parse --show-toplevel)}
UPSTREAM_REMOTE=${UPSTREAM_REMOTE:-origin}
UPSTREAM_BRANCH=${UPSTREAM_BRANCH:-master}

TRIGGER_STRING="$1" ; shift

git fetch $(git remote get-url $UPSTREAM_REMOTE) $UPSTREAM_BRANCH

if git --no-pager log -n 1 --oneline 'FETCH_HEAD..HEAD' | grep "$TRIGGER_STRING" &>/dev/null; then
    echo 'true'
fi
