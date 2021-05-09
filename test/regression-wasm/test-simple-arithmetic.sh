#!/bin/sh
./kwasm prove --backend haskell tests/proofs/simple-arithmetic-spec.k KWASM-LEMMAS --format-failures 
--dry-run --save-temps ${KORE_EXEC:?} test-simple-arithmetic-vdefinition.kore --module KWASM-LEMMAS --prove test-simple-arithmetic-spec.kore --spec-module SIMPLE-ARITHMETIC-SPEC "$@"
