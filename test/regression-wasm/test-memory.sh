#!/bin/sh
${KORE_EXEC:?} test-memory-vdefinition.kore --module KWASM-LEMMAS --prove test-memory-spec.kore --spec-module MEMORY-SPEC "$@"
