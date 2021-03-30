#!/bin/sh

nix-shell nix/shell.hpack.nix --run 'hpack -f kore'
$(nix-build --no-out-link -A rematerialize)
$(nix-build --no-out-link shell.nix -A passthru.rematerialize)
