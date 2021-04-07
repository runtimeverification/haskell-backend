#!/bin/sh
${KORE_EXEC:?} test-straight-line-definition.kore --module ETHEREUM-SIMULATION --pattern test-straight-line-search-initial.kore --searchType FINAL --search test-straight-line-search-pattern.kore "$@"
