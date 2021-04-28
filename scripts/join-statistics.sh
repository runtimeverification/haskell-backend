#!/usr/bin/env nix-shell
#!nix-shell ../test.nix -i bash

old=${1:?}; shift
new=${1:?}; shift

# 1. Join the statistics files by row according to name.
#    Give the columns from each file a unique prefix.
# 2. Add a column for the (relative) difference between old and new values.
mlr --csv join -j name --lp old_ --rp new_ -f "$old" "$new" \
  | mlr --csv put '$diff_allocated_bytes = 2 * ($new_allocated_bytes - $old_allocated_bytes) / ($new_allocated_bytes + $old_allocated_bytes)' \
  | mlr --csv put '$diff_max_live_bytes = 2 * ($new_max_live_bytes - $old_max_live_bytes) / ($new_max_live_bytes + $old_max_live_bytes)'
