#!/usr/bin/env bash

set -exuo pipefail

export PATH="$HOME/.local/bin:${PATH:+:}$PATH"

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

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

changed=()
for file in $(find . -type f -name '*.hs*' '(' ! -path '*/.stack-work*' ')' '(' ! -path '*/dist*' ')')
do
    case $file in
        *.hs|*.hs-boot) ;;
        *) continue ;;
    esac
    stylish-haskell $file >$file.tmp
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

hlint kore
