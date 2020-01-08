#!/bin/sh
exec $KORE_EXEC test-branching-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-branching-invalid-pgm.kore --searchType FINAL --search test-branching-invalid-pattern.kore "$@"
