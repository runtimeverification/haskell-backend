#!/bin/sh
${KORE_EXEC:?} test-totalSupply-definition.kore --module VERIFICATION --prove test-totalSupply-spec.kore --spec-module TOTALSUPPLY-SPEC "$@"
