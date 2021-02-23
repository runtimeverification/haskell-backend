#!/usr/bin/env nix-shell
#!nix-shell ../shell.nix -i bash

fd '.*\.hs$' | xargs fourmolu -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i