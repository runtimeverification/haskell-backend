#!/bin/sh

IGNORE=$($KORE_REPL test-a-to-c-vdefinition.kore -r --repl-script run-one-save-state-repl-script-spec.k.repl --module VERIFICATION --prove test-a-to-c-spec.kore --spec-module A-TO-C-SPEC)
IGNORE=$($KORE_REPL test-a-to-c-vdefinition.kore -r --repl-script save-config-repl-script-spec-k.repl --module VERIFICATION --prove partial-a-to-c.kore --spec-module PARTIAL-A-TO-C-SPEC)

diff partial-a-to-c.kore partial-a-to-c.kore.golden
diff original-config.out partial-config.out
rm original-config.out
rm partial-config.out
rm partial-a-to-c.kore
