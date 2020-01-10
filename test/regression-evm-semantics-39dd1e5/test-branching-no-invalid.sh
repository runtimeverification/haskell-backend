#!/bin/sh
$KORE_EXEC test-branching-no-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-branching-no-invalid-pgm.kore --searchType FINAL --search test-branching-no-invalid-pattern.kore "$@"
