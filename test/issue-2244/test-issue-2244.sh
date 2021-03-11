#!/bin/sh
exec kore-exec \
    vdefinition.kore \
    --module VERIFICATION \
    --strategy all \
    --smt-timeout 40 \
    --smt-reset-interval 100 \
    --smt z3 \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove spec.kore \
    --spec-module LISTSUM-SPEC \
    --graph-search breadth-first \
     \
     \
    "$@"
