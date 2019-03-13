#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

new_nightly="$(curl 'https://api.github.com/repos/kframework/k/releases' | jq --raw-output '.[0].assets[].browser_download_url | match(".*nightly.tar.gz").string')"

sed -i '/K_NIGHTLY_URL.*/c\'"K_NIGHTLY_URL = $new_nightly" "$TOP/include.mk"
