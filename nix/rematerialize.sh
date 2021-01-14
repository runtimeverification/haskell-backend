#!/bin/sh

nix-shell --run 'hpack -f kore'
$(nix-build --no-out-link -A project.stack-nix.passthru.updateMaterialized)
