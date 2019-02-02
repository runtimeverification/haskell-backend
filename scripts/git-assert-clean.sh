#!/usr/bin/env bash

set -exuo pipefail

if [ ! $(git status --porcelain | wc -l) -eq 0 ]; then
    echo "Found dirty files:"
    git status --porcelain
    exit 1
fi
