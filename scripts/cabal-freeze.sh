#!/bin/sh

cabal v2-freeze

# Do not freeze kore itself.
# This prevents building with different flags, for example.
sed -i cabal.project.freeze -e '/^[[:space:]]\+kore/ d'
