#!/bin/sh
${KORE_EXEC:?} test-branching-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-branching-invalid-search-initial.kore --searchType FINAL --search test-branching-invalid-search-pattern.kore "$@"
