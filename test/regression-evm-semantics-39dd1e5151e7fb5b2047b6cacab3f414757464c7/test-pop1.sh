#!/bin/sh
exec $KORE_EXEC test-pop1-definition.kore --module ETHEREUM-SIMULATION --pattern test-pop1-pgm.kore "$@"
