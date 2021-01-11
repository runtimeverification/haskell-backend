#!/bin/sh

$(nix-build --no-out-link -A pkgs.haskell-nix.internal-nix-tools)/bin/hpack -f kore
$(nix-build --no-out-link -A project.stack-nix.passthru.updateMaterialized)
