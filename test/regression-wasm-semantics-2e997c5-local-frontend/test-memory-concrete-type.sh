#!/bin/sh
$KORE_EXEC test-memory-concrete-type-vdefinition.kore --module KWASM-LEMMAS --prove test-memory-concrete-type-spec.kore --spec-module MEMORY-CONCRETE-TYPE-SPEC "$@"
