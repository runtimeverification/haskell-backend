#!/bin/sh
./kwasm prove --backend haskell tests/proofs/wrc20-spec.k WRC20-LEMMAS --format-failures 
--dry-run --save-temps ${KORE_EXEC:?} test-wrc20-vdefinition.kore --module WRC20-LEMMAS --prove test-wrc20-spec.kore --spec-module WRC20-SPEC "$@"
