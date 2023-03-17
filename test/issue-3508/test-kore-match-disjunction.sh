#!/bin/sh
exec kore-match-disjunction \
    definition.kore \
    --module IMP \
    --disjunction disjunction.kore \
    --match pattern.kore
    "$@"
