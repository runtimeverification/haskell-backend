#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}
UPSTREAM_REMOTE=${UPSTREAM_REMOTE:-origin}

git fetch $(git remote get-url $UPSTREAM_REMOTE) master
UPSTREAM_BRANCH=FETCH_HEAD

if ! $TOP/scripts/git-assert-clean.sh
then
    echo >&2 "Please commit your changes!"
    exit 1
fi

stack install stylish-haskell
changed=()
for file in $(git diff --name-only --diff-filter=d $UPSTREAM_BRANCH)
do
    case $file in
        *.hs|*.hs-boot) ;;
        *) continue ;;
    esac
    $TOP/.build/kore/bin/stylish-haskell $file >$file.tmp
    # (diff ...) exits with 0 when the files are the same
    # (! diff ...) means the files are _different_
    # Maybe it should have been named "same" :-\
    if ! diff -Nau $file $file.tmp
    then
        changed+=($file)
    fi
    rm $file.tmp
done

if [[ ${#changed[@]} -ne 0 ]]
then
    echo >&2 "Please run 'stylish-haskell':"
    echo >&2 "stack exec -- stylish-haskell -i" "${changed[@]}"
    exit 1
fi
