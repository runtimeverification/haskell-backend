#!/bin/sh
$KORE_EXEC test-branching-no-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-branching-no-invalid-search-initial.kore --searchType FINAL --search test-branching-no-invalid-search-pattern.kore "$@"
