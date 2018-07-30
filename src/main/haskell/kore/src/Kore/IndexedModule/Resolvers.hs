{-|
Module      : Kore.IndexedModule.Resolvers
Description : Tools for resolving IDs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.IndexedModule.Resolvers
    ( getHeadApplicationSorts
    , getHeadAttributes
    , resolveSort
    , resolveAlias
    , resolveSymbol
    ) where

import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.Error
       ( koreFailWithLocations )
import Kore.AST.Kore
import Kore.AST.MetaOrObject
       ( IsMetaOrObject (..), MetaOrObject, isMetaOrObject )
import Kore.AST.Sentence
import Kore.ASTHelpers
       ( ApplicationSorts, symbolOrAliasSorts )
import Kore.Error
       ( Error, printError )
import Kore.IndexedModule.IndexedModule
       ( IndexedModule (..), KoreIndexedModule, SortDescription )

symbolSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule atts
    -> Map.Map
        (Id level)
        (atts, SentenceSymbol level UnifiedPattern Variable)
symbolSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaSymbolSentences m
        IsObject -> indexedModuleObjectSymbolSentences m

aliasSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule atts
    -> Map.Map
        (Id level)
        (atts, SentenceAlias level UnifiedPattern Variable)
aliasSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaAliasSentences m
        IsObject -> indexedModuleObjectAliasSentences m

sortSentencesMap
    :: MetaOrObject level
    => a level
    -> KoreIndexedModule atts
    -> Map.Map
        (Id level)
        (atts, SortDescription level)
sortSentencesMap a m =
    case isMetaOrObject a of
        IsMeta   -> indexedModuleMetaSortDescriptions m
        IsObject -> indexedModuleObjectSortDescriptions m

-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and instantiates sort parameters with the arguments
-- specified by the head to obtain the corresponding 'ApplicationSorts'.
getHeadApplicationSorts
    :: MetaOrObject level
    => KoreIndexedModule atts  -- ^module representing a verified definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> ApplicationSorts level
getHeadApplicationSorts m patternHead =
    case resolveSymbol m headName of
        Right (_, sentence) ->
            case symbolOrAliasSorts headParams sentence of
                Left err     -> error (printError err)
                Right result -> result
        Left _ ->
            case resolveAlias m headName of
                Right (_, sentence) ->
                    case symbolOrAliasSorts headParams sentence of
                        Left err     -> error (printError err)
                        Right result -> result
                Left _ ->
                    error ("Head " ++ show patternHead ++ " not defined.")
  where
    headName = symbolOrAliasConstructor patternHead
    headParams = symbolOrAliasParams patternHead


-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and returns its attributes.
-- FIXME: duplicated code as in getHeadApplicationSorts, i.e. use (<|>)
-- The problem is resolveSymbol and resolveAlias return different types
-- you could work around this with some rearrangement
-- but rather just change the types
getHeadAttributes
    :: MetaOrObject level
    => KoreIndexedModule atts  -- ^module representing a verified definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> atts
getHeadAttributes m patternHead =
    case resolveSymbol m headName of
        Right (atts, _) -> atts
        Left _ ->
            case resolveAlias m headName of
                Right (atts, _) -> atts
                Left _ ->
                    error ("Head " ++ show patternHead ++ " not defined.")
  where
    headName = symbolOrAliasConstructor patternHead


{-|'resolveThing' looks up an id in an 'IndexedModule', also searching in the
imported modules.
-}
resolveThing
    :: (IndexedModule sortParam pat variable atts
        -> Map.Map (Id level) (atts, thing level pat variable))
    -- ^ extracts the map into which to look up the id
    -> IndexedModule sortParam pat variable atts
    -> Id level
    -> Maybe (atts, thing level pat variable)
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
    :: (Maybe (atts, thing level pat variable), Set.Set ModuleName)
    -> (IndexedModule sortParam pat variable atts
        -> Map.Map (Id level) (atts, thing level pat variable))
    -> IndexedModule sortParam pat variable atts
    -> Id level
    -> (Maybe (atts, thing level pat variable), Set.Set ModuleName)
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
                (\(_, _, m) partialResult -> resolveThingInternal
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
    => KoreIndexedModule atts
    -> Id level
    -> Either (Error a) (atts, KoreSentenceSymbol level)
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
    => KoreIndexedModule atts
    -> Id level
    -> Either (Error a) (atts, KoreSentenceAlias level)
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
    => KoreIndexedModule atts
    -> Id level
    -> Either (Error a) (atts, SortDescription level)
resolveSort m sortId =
    case resolveThing (sortSentencesMap (Proxy :: Proxy level)) m sortId of
        Nothing ->
            koreFailWithLocations
                [sortId]
                ("Sort '" ++ getId sortId ++  "' not declared.")
        Just sortDescription -> Right sortDescription
