#!/bin/sh
${KORE_EXEC:?} test-addu48u48-vdefinition.kore --module VERIFICATION --prove test-addu48u48-spec.kore --spec-module FLIPPER-ADDU48U48-FAIL-ROUGH-SPEC "$@"
