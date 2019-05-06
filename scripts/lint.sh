#!/usr/bin/env bash

exit_code=0

for f in `find ./kore -name '*.hs'`; do
    src/main/python/lint.py $f || exit_code=1
done

exit $exit_code
