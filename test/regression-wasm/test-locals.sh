#!/bin/sh
./kwasm prove --backend haskell tests/proofs/locals-spec.k KWASM-LEMMAS --format-failures 
--dry-run --save-temps ${KORE_EXEC:?} test-locals-vdefinition.kore --module KWASM-LEMMAS --prove test-locals-spec.kore --spec-module LOCALS-SPEC "$@"
