#!/bin/sh
exec $KORE_EXEC test-straight-line-definition.kore --module ETHEREUM-SIMULATION --pattern test-straight-line-pgm.kore --searchType FINAL --search test-straight-line-pattern.kore "$@"
