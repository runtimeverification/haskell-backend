#!/usr/bin/env bash
set -euxo pipefail
expected_hlint_version=v3.8
hlint=${HLINT:-$(which hlint)} || { echo 'No hlint!' ; exit 1 ; }
hlint_version=$(${hlint} --version | head -n1 | cut --field=1 --delimiter=',' | cut --field=2 --delimiter=' ')
[[ ${hlint_version} == ${expected_hlint_version} ]] || { echo "Unexpected hlint version, got ${hlint_version}, expected ${expected_hlint_version}" ; exit 1 ; }
${hlint} --git --threads
