#!/bin/sh
exec kore-exec \
    vdefinition.kore \
    --module LIST-SIZER \
    --smt-timeout 40 \
    --smt z3 \
    --strategy all \
    --log-level \
    warning \
    --enable-log-timestamps \
    --prove spec.kore \
    --spec-module INVALID-SIZE \
    --graph-search breadth-first \
     \
     \
    "$@"
