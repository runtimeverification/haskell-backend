#!/bin/sh
${KORE_EXEC:?} test-dsvalue-peek-pass-rough-definition.kore --module VERIFICATION --prove test-dsvalue-peek-pass-rough-spec.kore --spec-module DSVALUE-PEEK-PASS-ROUGH-SPEC "$@"
