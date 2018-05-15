{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , extractMetadataTools
    )
  where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore                    (UnifiedPattern)
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTHelpers
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Map                              as Map (Map, lookup)

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools level = MetadataTools
    { isConstructor    :: SymbolOrAlias level -> Bool
    , isFunctional     :: SymbolOrAlias level -> Bool
    , getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as whether it is functional / constructor,
-- or its argument and result sorts.
--
-- Since there is no clear consensus on how constructor and functionality
-- axioms would be specified yet, we currently assume all symbols
-- are constructors and all of them are functional, too.
extractMetadataTools
    :: MetaOrObject level
    => KoreIndexedModule
    -> MetadataTools level
extractMetadataTools m = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , getArgumentSorts = applicationSortsOperands . getHeadApplicationSorts m
    , getResultSort = applicationSortsResult . getHeadApplicationSorts m
    }

symbolSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule
    -> Map.Map
        (Id level)
        (SentenceSymbol level UnifiedPattern Variable)
symbolSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaSymbolSentences m
        IsObject -> indexedModuleObjectSymbolSentences m

getHeadApplicationSorts
    :: MetaOrObject level
    => KoreIndexedModule
    -> SymbolOrAlias level
    -> ApplicationSorts level
getHeadApplicationSorts m patternHead =
    case resolveThing symbolsMapExtractor m headName of
        Just sentence ->
            case symbolOrAliasSorts headParams sentence of
                Left err     -> error (printError err)
                Right result -> result
        Nothing -> error ("Symbol " ++ show patternHead ++ " not found.")
  where
    headName = symbolOrAliasConstructor patternHead
    headParams = symbolOrAliasParams patternHead
    symbolsMapExtractor = symbolSentencesMap patternHead
