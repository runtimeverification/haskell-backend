#!/bin/sh
exec $KORE_EXEC test-straight-line-no-invalid-definition.kore --module ETHEREUM-SIMULATION --pattern test-straight-line-no-invalid-pgm.kore --searchType FINAL --search test-straight-line-no-invalid-pattern.kore "$@"
