#!/usr/bin/env nix-shell
#!nix-shell ../shell.nix -i bash

./scripts/remove-import-groups.sh
./scripts/fourmolu.sh