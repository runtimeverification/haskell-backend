#!/usr/bin/env bash
set -euxo pipefail
expected_fourmolu_version=0.8.2.0
fourmolu=${FOURMOLU:-$(which fourmolu)} || { echo 'No fourmolu!' ; exit 1 ; }
fourmolu_version=$(${fourmolu} --version | head -n1 | cut --field=2 --delimiter=' ')
[[ ${fourmolu_version} == ${expected_fourmolu_version} ]] || { echo "Unexpected fourmolu version, got ${fourmolu_version}, expected ${expected_fourmolu_version}" ; exit 1 ; }
git ls-files | grep '.*\.hs$' | xargs ${fourmolu} -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -o -XOverloadedRecordDot -i
