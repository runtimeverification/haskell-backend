#!/usr/bin/env nix-shell
#!nix-shell ../test.nix -i bash

mlr --icsv --omd cut -o -f name,allocated_bytes,diff_allocated_bytes,max_live_bytes,diff_max_live_bytes
