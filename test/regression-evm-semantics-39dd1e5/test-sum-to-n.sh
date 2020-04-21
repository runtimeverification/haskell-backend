#!/bin/sh
$KORE_EXEC test-sum-to-n-vdefinition.kore --module VERIFICATION --prove test-sum-to-n-spec.kore --spec-module SUM-TO-N-SPEC "$@"
