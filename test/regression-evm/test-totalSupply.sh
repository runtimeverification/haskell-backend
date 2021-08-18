#!/bin/sh
${KORE_EXEC:?} test-totalSupply-vdefinition.kore --module VERIFICATION --prove test-totalSupply-spec.kore --spec-module TOTALSUPPLY-SPEC "$@"
