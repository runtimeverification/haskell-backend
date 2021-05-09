#!/bin/sh
./kwasm prove --backend haskell tests/proofs/memory-spec.k KWASM-LEMMAS --format-failures 
--dry-run --save-temps ${KORE_EXEC:?} test-memory-vdefinition.kore --module KWASM-LEMMAS --prove test-memory-spec.kore --spec-module MEMORY-SPEC "$@"
