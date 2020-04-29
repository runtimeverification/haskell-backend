#!/bin/sh
$KORE_EXEC test-memory-concrete-type-vdefinition.kore --module MEMORY-CONCRETE-TYPE-LEMMAS --prove test-memory-concrete-type-spec.kore --spec-module MEMORY-CONCRETE-TYPE-SPEC "$@"
