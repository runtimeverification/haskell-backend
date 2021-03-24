#!/bin/sh

fd '.*\.hs$' | xargs fourmolu -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i