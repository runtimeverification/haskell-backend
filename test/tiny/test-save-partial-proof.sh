#!/bin/sh

IGNORE=$($KORE_REPL test-a-to-c-vdefinition.kore -r --repl-script run-one-save-state-repl-script-spec.k.repl --module KARL --prove test-a-to-c-spec.kore --spec-module A-TO-C-SPEC)
IGNORE=$($KORE_REPL test-a-to-c-vdefinition.kore -r --repl-script save-config-repl-script-spec-k.repl --module KARL --prove partial-a-to-c.kore --spec-module PARTIAL-A-TO-C-SPEC)

if grep -q "KARL" partial-a-to-c.kore; then
    diff original-config.out partial-config.out
    rm original-config.out
    rm partial-config.out
    rm partial-a-to-c.kore
else
    echo "Error: Expected main module name not found in partial-a-to-c.kore."
fi
