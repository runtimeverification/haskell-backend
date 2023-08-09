#!/bin/sh
${KORE_EXEC:?} test-wrc20-vdefinition.kore --module WRC20-LEMMAS --prove test-wrc20-spec.kore --spec-module WRC20-SPEC --smt-timeout 40 --smt-retry-limit 1 --smt-reset-interval 100 "$@"
