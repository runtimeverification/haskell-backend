{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.IndexedModule.Error
    ( noSort
    , noHead
    , noAlias
    , noSymbol
    )
where
import Kore.AST.Kore

-- | A message declaring that a Sort is undefined
noSort :: MetaOrObject level => Id level -> String
noSort sortId =
    notDefined "Sort" $ show sortId

-- | A message declaring that a Head is undefined
noHead :: MetaOrObject level => SymbolOrAlias level -> String
noHead patternHead =
    notDefined "Head" $ show patternHead

-- | A message declaring that a Alias is undefined
noAlias :: MetaOrObject level => Id level -> String
noAlias identifier =
    notDefined "Alias" $ getIdForError identifier

-- | A message declaring that a Symbol is undefined
noSymbol :: MetaOrObject level => Id level -> String
noSymbol identifier =
    notDefined "Symbol" $ getIdForError identifier

-- | A message declaring that some `tag` is undefined.
notDefined :: String -> String -> String
notDefined tag identifier =
    tag ++ " '" ++ identifier ++ "' not defined."
