#!/usr/bin/env bash
set -euxo pipefail
expected_fourmolu_version="0.15.0.0"
fourmolu=${FOURMOLU:-$(which fourmolu)} || { echo 'No fourmolu!' ; exit 1 ; }
fourmolu_version=$(${fourmolu} --version | head -n1)
# drop the prefix 'fourmolu ' which is 9 letters long
fourmolu_version=${fourmolu_version:9}
[[ ${fourmolu_version} == ${expected_fourmolu_version} ]] || { echo "Unexpected fourmolu version, got ${fourmolu_version}, expected ${expected_fourmolu_version}" ; exit 1 ; }
git ls-files | grep '.*\.hs$' | xargs ${fourmolu} -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -o -XOverloadedRecordDot -i
