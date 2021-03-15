#!/bin/sh
$KORE_EXEC definition.kore --pattern pgm.kore --module MICHELSON --smt-timeout 40 --smt z3 --strategy all --log-level warning --enable-log-timestamps --search searchFile.kore --searchType FINAL "$@"
