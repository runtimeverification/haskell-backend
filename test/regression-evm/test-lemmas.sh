#!/bin/sh
${KORE_EXEC:?} test-lemmas-vdefinition.kore --module VERIFICATION --prove test-lemmas-spec.kore --spec-module LEMMAS-SPEC "$@"
