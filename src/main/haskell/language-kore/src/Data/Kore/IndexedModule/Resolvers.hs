{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.IndexedModule.Resolvers
Description : Tools for resolving IDs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.IndexedModule.Resolvers
    ( getHeadApplicationSorts
    , resolveSort
    , resolveAlias
    , resolveSymbol
    ) where

import qualified Data.Map                              as Map
import           Data.Proxy                            (Proxy (..))
import qualified Data.Set                              as Set

import           Data.Kore.AST.Common                  (Id (..), ModuleName,
                                                        SentenceAlias,
                                                        SentenceSymbol,
                                                        SymbolOrAlias (..),
                                                        Variable)
import           Data.Kore.AST.Error                   (koreFailWithLocations)
import           Data.Kore.AST.Kore                    (KoreSentenceAlias,
                                                        KoreSentenceSymbol,
                                                        UnifiedPattern)
import           Data.Kore.AST.MetaOrObject            (IsMetaOrObject (..),
                                                        MetaOrObject,
                                                        isMetaOrObject)
import           Data.Kore.ASTHelpers                  (ApplicationSorts,
                                                        symbolOrAliasSorts)
import           Data.Kore.Error                       (Error, printError)
import           Data.Kore.IndexedModule.IndexedModule (IndexedModule (..),
                                                        KoreIndexedModule,
                                                        SortDescription)

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

aliasSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule
    -> Map.Map
        (Id level)
        (SentenceAlias level UnifiedPattern Variable)
aliasSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaAliasSentences m
        IsObject -> indexedModuleObjectAliasSentences m

sortSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule
    -> Map.Map
        (Id level)
        (SortDescription level)
sortSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaSortDescriptions m
        IsObject -> indexedModuleObjectSortDescriptions m

-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and instantiates sort parameters with the arguments
-- specified by the head to obtain the corresponding 'ApplicationSorts'.
getHeadApplicationSorts
    :: MetaOrObject level
    => KoreIndexedModule   -- ^module representing a verified definition
    -> SymbolOrAlias level -- ^the head we want to find sorts for
    -> ApplicationSorts level
getHeadApplicationSorts m patternHead =
    case resolveSymbol m headName of
        Right sentence ->
            case symbolOrAliasSorts headParams sentence of
                Left err     -> error (printError err)
                Right result -> result
        Left _ ->
            case resolveAlias m headName of
                Right sentence ->
                    case symbolOrAliasSorts headParams sentence of
                        Left err     -> error (printError err)
                        Right result -> result
                Left _ ->
                    error ("Head " ++ show patternHead ++ " not defined.")
  where
    headName = symbolOrAliasConstructor patternHead
    headParams = symbolOrAliasParams patternHead

{-|'resolveThing' looks up an id in an 'IndexedModule', also searching in the
imported modules.
-}
resolveThing
    :: (IndexedModule sortParam pat variable
        -> Map.Map (Id level) (thing level pat variable))
    -- ^ extracts the map into which to look up the id
    -> IndexedModule sortParam pat variable
    -> Id level
    -> Maybe (thing level pat variable)
resolveThing
    mapExtractor
    indexedModule
    thingId
  =
    fst
        ( resolveThingInternal
            (Nothing, Set.empty) mapExtractor indexedModule thingId
        )

resolveThingInternal
    :: (Maybe (thing level pat variable), Set.Set ModuleName)
    -> (IndexedModule sortParam pat variable
        -> Map.Map (Id level) (thing level pat variable))
    -> IndexedModule sortParam pat variable
    -> Id level
    -> (Maybe (thing level pat variable), Set.Set ModuleName)
resolveThingInternal x@(Just _, _) _ _ _ = x
resolveThingInternal x@(Nothing, searchedModules) _ indexedModule _
    | indexedModuleName indexedModule `Set.member` searchedModules = x
resolveThingInternal
    (Nothing, searchedModules)
    mapExtractor
    indexedModule
    thingId
  =
    case Map.lookup thingId things of
        Just thing -> (Just thing, undefined {- this should never evaluate -})
        Nothing ->
            foldr
                (\(_, m) partialResult -> resolveThingInternal
                    partialResult
                    mapExtractor
                    m
                    thingId
                )
                ( Nothing
                , Set.insert (indexedModuleName indexedModule) searchedModules
                )
                (indexedModuleImports indexedModule)
  where
    things = mapExtractor indexedModule

{-|'resolveSymbol' looks up a symbol id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveSymbol
    :: MetaOrObject level
    => KoreIndexedModule
    -> Id level
    -> Either (Error a) (KoreSentenceSymbol level)
resolveSymbol m headId =
    case resolveThing (symbolSentencesMap (Proxy :: Proxy level)) m headId of
        Nothing ->
            koreFailWithLocations
                [headId]
                ("Symbol '" ++ getId headId ++  "' not defined.")
        Just result -> Right result

{-|'resolveAlias' looks up a symbol id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveAlias
    :: MetaOrObject level
    => KoreIndexedModule
    -> Id level
    -> Either (Error a) (KoreSentenceAlias level)
resolveAlias m headId =
    case resolveThing (aliasSentencesMap (Proxy :: Proxy level)) m headId of
        Nothing ->
            koreFailWithLocations
                [headId]
                ("Alias '" ++ getId headId ++  "' not defined.")
        Just result -> Right result


{-|'resolveSort' looks up a sort id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveSort
    :: MetaOrObject level
    => KoreIndexedModule
    -> Id level
    -> Either (Error a) (SortDescription level)
resolveSort m sortId =
    case resolveThing (sortSentencesMap (Proxy :: Proxy level)) m sortId of
        Nothing ->
            koreFailWithLocations
                [sortId]
                ("Sort '" ++ getId sortId ++  "' not declared.")
        Just sortDescription -> Right sortDescription
