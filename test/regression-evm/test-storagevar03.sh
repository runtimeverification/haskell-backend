#!/bin/sh
${KORE_EXEC:?} test-storagevar03-vdefinition.kore --module VERIFICATION --prove test-storagevar03-spec.kore --spec-module STORAGEVAR03-SPEC "$@"
