#!/bin/sh

# hooks: run these commands when project files change

hpack -f kore
stylish-haskell -i -r kore