{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.IndexedModule.Error
    ( noSort
    , noHead
    , noAlias
    , noSymbol
    ) where

import Kore.Syntax

-- | A message declaring that a Sort is undefined
noSort :: Id -> String
noSort sortId =
    notDefined "Sort" $ getIdForError sortId

-- | A message declaring that a Head is undefined
noHead :: SymbolOrAlias -> String
noHead patternHead =
    notDefined "Head" $ show patternHead

-- | A message declaring that a Alias is undefined
noAlias :: Id -> String
noAlias identifier =
    notDefined "Alias" $ getIdForError identifier

-- | A message declaring that a Symbol is undefined
noSymbol :: Id -> String
noSymbol identifier =
    notDefined "Symbol" $ getIdForError identifier

-- | A message declaring that some `tag` is undefined.
notDefined :: String -> String -> String
notDefined tag identifier =
    tag ++ " '" ++ identifier ++ "' not defined."
