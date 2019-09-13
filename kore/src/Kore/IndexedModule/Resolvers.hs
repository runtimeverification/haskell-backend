{-|
Module      : Kore.IndexedModule.Resolvers
Description : Tools for resolving IDs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.IndexedModule.Resolvers
    ( getSortAttributes
    , getSymbolAttributes
    , resolveSort
    , resolveAlias
    , resolveSymbol
    , resolveHook
    , findIndexedSort

    -- TODO: This symbol is used by `resolveHook`.
    -- `resolveHook` doesn't have tests, but
    -- `getHeadApplicationSorts does. So this is
    -- exported until `resolveHook` has its own
    -- tests.
    , getHeadApplicationSorts

    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import GHC.Stack
    ( HasCallStack
    )

import Kore.AST.Error
    ( koreFailWithLocations
    )
import qualified Kore.Attribute.Sort as Attribute
import Kore.Error
import Kore.IndexedModule.Error
    ( noAliasText
    , noHead
    , noSort
    , noSortText
    , noSymbol
    , noSymbolText
    )
import Kore.IndexedModule.IndexedModule
    ( IndexedModule (..)
    , getIndexedSentence
    , indexedModulesInScope
    )
import Kore.Internal.ApplicationSorts
import Kore.Syntax
import Kore.Syntax.Definition hiding
    ( Alias (..)
    , Symbol (..)
    )

symbolSentencesMap
    :: IndexedModule patternType declAtts axiomAtts
    -> Map.Map Id (declAtts, SentenceSymbol patternType)
symbolSentencesMap = indexedModuleSymbolSentences

aliasSentencesMap
    :: IndexedModule patternType declAtts axiomAtts
    -> Map.Map Id (declAtts, SentenceAlias patternType)
aliasSentencesMap = indexedModuleAliasSentences

sortSentencesMap
    :: IndexedModule patternType declAtts axiomAtts
    -> Map.Map Id (Attribute.Sort, SentenceSort patternType)
sortSentencesMap = indexedModuleSortDescriptions

-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and instantiates sort parameters with the arguments
-- specified by the head to obtain the corresponding 'ApplicationSorts'.
getHeadApplicationSorts
    :: IndexedModule patternType declAtts axiomAtts
    -- ^ Module representing an indexed definition
    -> SymbolOrAlias     -- ^the head we want to find sorts for
    -> ApplicationSorts
getHeadApplicationSorts m patternHead =
    applyToHeadSentence sentenceSorts m patternHead
  where
    sentenceSorts
        :: SentenceSymbolOrAlias sentence
        => [Sort] -> sentence pat -> ApplicationSorts
    sentenceSorts sortParameters sentence =
        assertRight $ symbolOrAliasSorts sortParameters sentence

getSortAttributes
    :: HasCallStack
    => IndexedModule patternType declAtts axiomAtts
    -> Sort
    -> Attribute.Sort
getSortAttributes m (SortActualSort (SortActual sortId _)) =
  case resolveSort m sortId of
    Right (atts, _) -> atts
    Left _ -> error $ noSort sortId
getSortAttributes _ _ = error "Can't lookup attributes for sort variables"

getSymbolAttributes
    :: HasCallStack
    => IndexedModule patternType declAtts axiomAtts
    -> Id
    -> declAtts
getSymbolAttributes m symbolId =
  case resolveSymbol m symbolId of
    Right (atts, _) -> atts
    Left _ -> error $ noSymbol symbolId

{-|'resolveThing' looks up an id in an 'IndexedModule', also searching in the
imported modules.
-}
resolveThing
    ::  (  IndexedModule patternType declAtts axiomAtts
        -> Map.Map Id result
        )
    -- ^ extracts the map into which to look up the id
    -> IndexedModule patternType declAtts axiomAtts
    -> Id
    -> Maybe result
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
    :: (Maybe result, Set.Set ModuleName)
    ->  (  IndexedModule patternType declAtts axiomAtts
        -> Map.Map Id result
        )
    -> IndexedModule patternType declAtts axiomAtts
    -> Id
    -> (Maybe result, Set.Set ModuleName)
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
    :: MonadError (Error e) m
    => IndexedModule patternType declAtts axiomAtts
    -> Id
    -> m (declAtts, SentenceSymbol patternType)
resolveSymbol m headId =
    case resolveThing symbolSentencesMap m headId of
        Nothing ->
            koreFailWithLocations [headId] (noSymbolText headId)
        Just result ->
            return result

{-|'resolveAlias' looks up a symbol id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveAlias
    :: MonadError (Error e) m
    => IndexedModule pat declAtts axiomAtts
    -> Id
    -> m (declAtts, SentenceAlias pat)
resolveAlias m headId =
    case resolveThing aliasSentencesMap m headId of
        Nothing ->
            koreFailWithLocations [headId] (noAliasText headId)
        Just result ->
            return result



{-|'resolveSort' looks up a sort id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveSort
    :: MonadError (Error e) m
    => IndexedModule patternType declAtts axiomAtts
    -> Id
    -> m (Attribute.Sort, SentenceSort patternType)
resolveSort m sortId =
    case resolveThing sortSentencesMap m sortId of
        Nothing ->
            koreFailWithLocations [sortId] $ noSortText sortId
        Just sortDescription ->
            return sortDescription

resolveHook
    :: IndexedModule patternType declAtts axiomAtts
    -> Text
    -> Sort
    -> Either (Error e) Id
resolveHook indexedModule builtinName builtinSort =
    resolveHookHandler builtinName
    $ Set.filter relevant
    $ resolveHooks indexedModule builtinName
  where
    relevant name =
        involvesSort indexedModule builtinSort (SymbolOrAlias name [])

involvesSort
    :: IndexedModule patternType declAtts axiomAtts
    -> Sort
    -> SymbolOrAlias
    -> Bool
involvesSort indexedModule builtinSort sym =
    elem builtinSort $
    (\s -> applicationSortsResult s : applicationSortsOperands s) $
    getHeadApplicationSorts indexedModule sym

resolveHookHandler
    :: Text
    -> Set Id
    -> Either (Error e) Id
resolveHookHandler builtinName results =
    case Set.toList results of
        [hookId] -> return hookId
        [] ->
            koreFail
                ("Builtin '" ++ Text.unpack builtinName ++ "' is not hooked.")
        hookIds ->
            koreFail
                ("Builtin '" ++ Text.unpack builtinName
                    ++ "' is hooked to multiple identifiers: "
                    ++ List.intercalate ", "
                        (squotes . getIdForError <$> hookIds)
                )
      where
        squotes str = "'" ++ str ++ "'"

resolveHooks
    :: IndexedModule patternType declAtts axiomAtts
    -> Text
    -> Set Id
resolveHooks indexedModule builtinName =
    foldMap resolveHooks1 allHooks
  where
    allHooks = indexedModuleHooks <$> indexedModulesInScope indexedModule
    resolveHooks1 hooks =
        maybe Set.empty Set.fromList (Map.lookup builtinName hooks)

{- | Find a sort by name in an indexed module and its imports.

    Similar to 'resolveSort', but does not retrieve the sentence attributes.

 -}
findIndexedSort
    :: MonadError (Error e) error
    => IndexedModule patternType declAtts axiomAtts
    -- ^ indexed module
    -> Id
    -- ^ sort identifier
    -> error (SentenceSort patternType)
findIndexedSort indexedModule sort =
    fmap getIndexedSentence (resolveSort indexedModule sort)


{- Utilities -}

-- It would make sense to put this in a `where` clause; however,
-- the fully type annotation is required even there, and that makes
-- for too much clutter.
applyToHeadSentence
    :: (forall sentence.  SentenceSymbolOrAlias sentence
       => [Sort]
       -> sentence pat
       -> result)
    -> IndexedModule pat declAtts axiomAtts
    -> SymbolOrAlias
    -> result
applyToHeadSentence f =
     applyToResolution (\ params (_, sentence) -> f params sentence)

applyToResolution
    :: HasCallStack
    => (forall sentence.  SentenceSymbolOrAlias sentence
        => [Sort]
        -> (declAtts, sentence pat)
        -> result)
    -> IndexedModule pat declAtts axiomAtts
    -> SymbolOrAlias
    -> result
applyToResolution f m patternHead =
    case symbolResult <> aliasResult of
        Right result -> result
        Left _ -> error $ noHead patternHead
  where
    headName = symbolOrAliasConstructor patternHead
    headParams = symbolOrAliasParams patternHead
    symbolResult = f headParams <$> resolveSymbol m headName
    aliasResult = f headParams <$> resolveAlias m headName
