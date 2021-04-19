#!/bin/sh
${KORE_EXEC:?} test-locals-vdefinition.kore --module KWASM-LEMMAS --prove test-locals-spec.kore --spec-module LOCALS-SPEC "$@"
