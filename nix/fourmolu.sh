#!/usr/bin/env nix-shell
#!nix-shell shell.fourmolu.nix -i bash

./scripts/remove-import-groups.sh
./scripts/fourmolu.sh