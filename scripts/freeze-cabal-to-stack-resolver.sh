#/usr/bin/env bash

stack --test ls dependencies \
    | sed -e 's/^\([a-zA-Z0-9.-]*\) \([0-9.]*\)/--constraint="\1 == \2"/' \
    | xargs -x cabal freeze --enable-tests

git diff cabal.project.freeze
