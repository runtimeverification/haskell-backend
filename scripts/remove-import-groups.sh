#!/usr/bin/env bash

# Remove distinction between import groups:
# Remove every blank line between 'module' and the last 'import'.

temp=$(mktemp)
for each in $(fd '.*\.hs$')
do
    tac "$each" > "$temp"
    sed -i '/^import/,/^module/{/^[[:space:]]*$/d}' -i "$temp"
    tac "$temp" > "$each"
end
rm "$temp"