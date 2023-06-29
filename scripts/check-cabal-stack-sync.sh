#/usr/bin/env bash

set -eux

diff -s \
     <(stack --test ls dependencies | sed -e '/^kore.*$/d') \
     <(sed -n -e 's/^\(constraints:\| *\) any\.\([a-zA-Z0-9-]*\) ==\([0-9.]*\),/\2 \3/p' cabal.project.freeze) \
    && echo "Dependencies are in sync" \
    || (echo "Dependencies differ"; exit 1)
