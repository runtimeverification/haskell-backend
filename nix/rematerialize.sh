#!/bin/sh

nix-shell --run 'hpack -f kore'
$(nix-build --no-out-link -A rematerialize)
$(nix-build --no-out-link shell.nix -A passthru.rematerialize)
