#!/bin/sh

all_hs_files=$(fd '.*\.hs$')
hs_files=${1:-$all_hs_files}
echo $hs_files | xargs fourmolu -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i
