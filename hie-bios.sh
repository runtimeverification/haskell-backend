#!/usr/bin/env bash

out() {
    while [[ "$#" -gt 0 ]]
    do
        if [[ -n "${HIE_BIOS_OUTPUT}" ]]
        then
            echo "$1" >> "${HIE_BIOS_OUTPUT}"
        else
            echo "$1"
        fi
        shift
    done
}

out -i
out -ikore/src/
out -ikore/test/
out -ikore/app/share/
out -ikore/bench/

# Set -package-db options, unless GHC_PACKAGE_PATH is set already.
if [[ -z "${GHC_PACKAGE_PATH}" ]] && [[ -z "${IN_NIX_SHELL}" ]]
then
    out -clear-package-db
    out -package-db $(stack path --local-pkg-db)
    out -package-db $(stack path --snapshot-pkg-db)
    out -package-db $(stack path --global-pkg-db)
fi

yq -r '. "ghc-options" []' < ./kore/package.yaml | while read opt
do
    out "${opt}"
done

yq -r '. "default-extensions" []' < ./kore/package.yaml | while read ext
do
    out "-X${ext}"
done
