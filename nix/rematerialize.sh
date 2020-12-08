#!/bin/sh

$(nix-build --no-out-link -A project.stack-nix.passthru.updateMaterialized)
