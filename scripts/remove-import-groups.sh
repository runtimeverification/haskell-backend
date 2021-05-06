#!/usr/bin/env bash

# Remove distinction between import groups:
# Remove every blank line between 'module' and the last 'import'.

temp=$(mktemp)
for each in $(fd '.*\.hs$')
do
    ( cat "$each"; echo ) | tac - > "$temp"
    sed -e '/^import/,/^module/{/^[[:space:]]*$/d}' -i "$temp"
    tac "$temp" > "$each"
done
rm "$temp"