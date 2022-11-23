#!/bin/sh

# https://github.com/tweag/ormolu/issues/38
# https://gitlab.haskell.org/ghc/ghc/-/issues/17755
export LOCALE_ARCHIVE=
export LC_ALL=

all_hs_files=$(fd '.*\.hs$')
hs_files=${1:-$all_hs_files}
echo $hs_files | xargs fourmolu -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -o -XCPP -i
