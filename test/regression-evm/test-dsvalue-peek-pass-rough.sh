#!/bin/sh
${KORE_EXEC:?} test-dsvalue-peek-pass-rough-vdefinition.kore --module VERIFICATION --prove test-dsvalue-peek-pass-rough-spec.kore --spec-module DSVALUE-PEEK-PASS-ROUGH-SPEC "$@"
