#!/usr/bin/env bash

set -xeuo pipefail

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

version_file="package/version"

version_bump() {
    local version release_commit version_major version_minor version_patch new_version current_version current_version_major current_version_minor current_version_patch
    version="$(cat ${version_file})"
    version_major="$(echo ${version} | cut --delimiter '.' --field 1)"
    version_minor="$(echo ${version} | cut --delimiter '.' --field 2)"
    version_patch="$(echo ${version} | cut --delimiter '.' --field 3)"
    current_version="$(cat ${version_file})"
    current_version_major="$(echo ${current_version} | cut --delimiter '.' --field 1)"
    current_version_minor="$(echo ${current_version} | cut --delimiter '.' --field 2)"
    current_version_patch="$(echo ${current_version} | cut --delimiter '.' --field 3)"
    new_version="${version}"
    if [[ "${version_major}" == "${current_version_major}" ]] && [[ "${version_minor}" == "${current_version_minor}" ]]; then
        new_version="${version_major}.${version_minor}.$((version_patch + 1))"
    fi
    echo "${new_version}" > "${version_file}"
    notif "Version: ${new_version}"
}

version_sub() {
    local version
    version="$(cat $version_file)"
    sed -i "s/^version: '.*'$/version: '${version}'/" dev-tools/package.yaml
    sed -i "s/^version:        .*$/version:        ${version}/" dev-tools/hs-backend-booster-dev-tools.cabal

    sed -i "s/^version: '.*'$/version: '${version}'/" booster/package.yaml
    sed -i "s/^version:        .*$/version:        ${version}/" booster/hs-backend-booster.cabal

    sed -i "s/^version:        .*$/version:        ${version}/" kore/kore.cabal

    sed -i "s/^version:        .*$/version:        ${version}/" ./kore-rpc-types/kore-rpc-types.cabal

    sed -i 's/^k-haskell-backend (.*) unstable; urgency=medium$/k-haskell-backend ('"$version"') unstable; urgency=medium/' package/debian/changelog
}

version_command="$1" ; shift

case "${version_command}" in
    bump) version_bump "$@"                      ;;
    sub)  version_sub  "$@"                      ;;
    *)    fatal "No command: ${version_command}" ;;
esac
