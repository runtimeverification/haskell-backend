#!/bin/sh

$(nix-build --no-out-link -A rematerialize)
$(nix-build --no-out-link shell.nix -A passthru.rematerialize)
