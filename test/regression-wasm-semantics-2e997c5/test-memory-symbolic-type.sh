#!/bin/sh
$KORE_EXEC test-memory-symbolic-type-vdefinition.kore --module KWASM-LEMMAS --prove test-memory-symbolic-type-spec.kore --spec-module MEMORY-SYMBOLIC-TYPE-SPEC "$@"
