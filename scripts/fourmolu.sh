#!/bin/sh

fd '.*\.hs$' | xargs fourmolu -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i
