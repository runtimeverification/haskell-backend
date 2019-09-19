{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.IndexedModule.Error
    ( noSort
    , noSortText
    , noHead
    , noAlias
    , noAliasText
    , noSymbol
    , noSymbolText
    ) where

import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Kore.Syntax

-- | A message declaring that a Sort is undefined
noSort :: Id -> String
noSort sortId =
    notDefined "Sort" $ getIdForError sortId

-- | A message declaring that a Sort is undefined
noSortText :: Id -> Text
noSortText sortId = Text.pack (noSort sortId)

-- | A message declaring that a Head is undefined
noHead :: SymbolOrAlias -> String
noHead patternHead =
    notDefined "Head" . getIdForError . symbolOrAliasConstructor $ patternHead

-- | A message declaring that a Alias is undefined
noAlias :: Id -> String
noAlias identifier =
    notDefined "Alias" $ getIdForError identifier

-- | A message declaring that a Alias is undefined
noAliasText :: Id -> Text
noAliasText identifier = Text.pack (noAlias identifier)

-- | A message declaring that a Symbol is undefined
noSymbol :: Id -> String
noSymbol identifier =
    notDefined "Symbol" $ getIdForError identifier

-- | A message declaring that a Symbol is undefined
noSymbolText :: Id -> Text
noSymbolText identifier = Text.pack (noSymbol identifier)

-- | A message declaring that some `tag` is undefined.
notDefined :: String -> String -> String
notDefined tag identifier =
    tag ++ " '" ++ identifier ++ "' not defined."
