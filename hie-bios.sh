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
out -ikore/$(stack path --dist-dir)/build/autogen/
out -clear-package-db
out -package-db $(stack path --local-pkg-db)
out -package-db $(stack path --snapshot-pkg-db)
out -package-db $(stack path --global-pkg-db)

yq -r '. "ghc-options" []' < ./kore/package.yaml | while read opt
do
    out "${opt}"
done

yq -r '. "default-extensions" []' < ./kore/package.yaml | while read ext
do
    out "-X${ext}"
done
