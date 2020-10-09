#!/bin/sh
exec kore-exec \
    definition.kore \
    --pattern pgm.kore \
    --module TEST \
    --smt-timeout 40 \
    --smt z3 \
    --strategy all \
    --log-level \
    warning \
    --enable-log-timestamps \
    --solver-transcript \
    smt-transcript \
    --search searchFile.kore \
     \
    --searchType FINAL \
    "$@"
