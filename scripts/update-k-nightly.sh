#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

new_nightly="$(curl 'https://api.github.com/repos/kframework/k/releases' | jq --raw-output '.[0].assets[].browser_download_url | match("(.*)/nightly.tar.gz").captures[0].string')"

echo $new_nightly > "$TOP/deps/k_release"
