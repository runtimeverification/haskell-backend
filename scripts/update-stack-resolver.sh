#!/usr/bin/env bash

# Configure the major version of LTS Haskell:
major_version='14'

# Stackage redirects requests for a major version of LTS Haskell to the latest
# minor version in that series, so we ask cURL to follow the redirect and report
# the effective URL. awk extracts the actual resolver name and full version
# from the effective URL.
url="https://www.stackage.org/lts/${major_version}"
lts_version=$( \
    curl -Ls -o /dev/null -I -w '%{url_effective}' "${url}" \
    | awk '{ match($0, /lts-[0-9]+\.[0-9]+/, resolver); print resolver[0] }' \
)

# Replace the resolver in stack.yaml with the newest version.
sed -i ./stack.yaml -e "/^resolver:/ c resolver: ${lts_version}"
