#!/bin/sh
${KORE_EXEC:?} test-simple-arithmetic-vdefinition.kore --module KWASM-LEMMAS --prove test-simple-arithmetic-spec.kore --spec-module SIMPLE-ARITHMETIC-SPEC "$@"
