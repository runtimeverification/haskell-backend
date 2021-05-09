#!/bin/sh
./kwasm prove --backend haskell tests/proofs/loops-spec.k KWASM-LEMMAS --format-failures 
--dry-run --save-temps ${KORE_EXEC:?} test-loops-vdefinition.kore --module KWASM-LEMMAS --prove test-loops-spec.kore --spec-module LOOPS-SPEC "$@"
