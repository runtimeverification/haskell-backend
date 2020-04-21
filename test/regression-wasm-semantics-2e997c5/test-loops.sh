#!/bin/sh
$KORE_EXEC test-loops-vdefinition.kore --module KWASM-LEMMAS --prove test-loops-spec.kore --spec-module LOOPS-SPEC "$@"
