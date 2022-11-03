git ls-files | grep '.*\.hs$' | xargs ${FOURMOLU:-$(which fourmolu)} -o -XImportQualifiedPost -o -XTypeApplications -o -XPatternSynonyms -o -XBangPatterns -i
