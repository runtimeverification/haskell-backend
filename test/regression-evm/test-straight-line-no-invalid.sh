#!/bin/sh
${KORE_EXEC:?} test-straight-line-no-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-straight-line-no-invalid-search-initial.kore --searchType FINAL --search test-straight-line-no-invalid-search-pattern.kore "$@"
