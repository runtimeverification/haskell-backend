#!/bin/sh

# hooks: run these commands when project files change

hpack -f kore
fd '.*\.hs' | xargs fourmolu -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i