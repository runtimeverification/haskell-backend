#!/usr/bin/env bash
# Load the entire project in GHCi.
# Usage: ghcid.sh [⟨ghcid arguments⟩] -- ⟨ghci arguments⟩
# Example: Load the kore-test test suite in GHCi:
#   $ ghcid.sh -- Driver

ghcid_args=()
while [[ "$#" -gt 0 ]]
do
    arg="$1"
    shift
    if [[ "$arg" == "--" ]]
    then
        break
    else
        ghcid_args+=("$arg")
    fi
done

ghci_args=( $(./hie-bios.sh) )
while [[ "$#" -gt 0 ]]
do
    ghci_args+=("$1")
    shift
done

ghci="ghci ${ghci_args[@]}"
exec ghcid -c "$ghci" "${ghcid_args[@]}"
