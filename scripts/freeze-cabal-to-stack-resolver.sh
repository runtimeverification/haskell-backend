#/usr/bin/env bash

set -euxo pipefail

# must remove the prior freeze file to actually update
rm -f cabal.project.freeze

stack --test ls dependencies \
    | sed -e 's/^\([a-zA-Z0-9.-]*\) \([0-9.]*\)/--constraint="\1 == \2"/' \
    | xargs -x cabal freeze --enable-tests

# ghc-bignum is removed from the freeze file because it is wired into
# GHC and creates problems when nix builds tools with different GHCs
sed -i -e '/any\.ghc-bignum/d' -e '/any\.happy/d' -e '/any\.alex/d' cabal.project.freeze

git diff cabal.project.freeze
