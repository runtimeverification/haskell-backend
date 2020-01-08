#!/bin/sh
exec $KORE_EXEC test-sumTo10-definition.kore --module ETHEREUM-SIMULATION --pattern test-sumTo10-pgm.kore "$@"
