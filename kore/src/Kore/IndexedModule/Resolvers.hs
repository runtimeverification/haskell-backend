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
    ( HeadType(..)
    , getHeadAttributes
    , getHeadType
    , getSortAttributes
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

import           Data.Functor
                 ( ($>) )
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Error
                 ( koreFailWithLocations )
import           Kore.AST.Kore
import           Kore.AST.Sentence hiding
                 ( Alias (..), Symbol (..) )
import           Kore.ASTHelpers as AST
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import qualified Kore.Attribute.Sort as Attribute
import           Kore.Error
import           Kore.IndexedModule.Error
                 ( noAlias, noHead, noSort, noSymbol )
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), getIndexedSentence,
                 indexedModulesInScope )

symbolSentencesMap
    :: MetaOrObject level
    => a level
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -> Map.Map
        (Id level)
        (declAtts, SentenceSymbol level patternType)
symbolSentencesMap _ m = indexedModuleSymbolSentences m

aliasSentencesMap
    :: MetaOrObject level
    => a level
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -> Map.Map (Id level) (declAtts, SentenceAlias level patternType)
aliasSentencesMap _ m = indexedModuleAliasSentences m

sortSentencesMap
    :: MetaOrObject level
    => a level
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -> Map.Map (Id level) (Attribute.Sort, SentenceSort level patternType)
sortSentencesMap _ m = indexedModuleSortDescriptions m

-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and instantiates sort parameters with the arguments
-- specified by the head to obtain the corresponding 'ApplicationSorts'.
getHeadApplicationSorts
    :: MetaOrObject level
    => IndexedModule sortParam patternType declAtts axiomAtts
    -- ^ Module representing an indexed definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> ApplicationSorts level
getHeadApplicationSorts m patternHead =
    applyToHeadSentence sentenceSorts m patternHead
  where
    sentenceSorts :: SentenceSymbolOrAlias ssoa
                  => [Sort level] -> ssoa level pat -> ApplicationSorts level
    sentenceSorts sortParameters sentence =
        assertRight $ symbolOrAliasSorts sortParameters sentence


-- |Given a KoreIndexedModule and a head, it looks up the 'SentenceSymbol' or
-- 'SentenceAlias', and returns its attributes.
getHeadAttributes
    :: MetaOrObject level
    => IndexedModule sortParam patternType declAtts axiomAtts
    -- ^ module representing an indexed definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> declAtts
getHeadAttributes m patternHead =
    applyToAttributes id m patternHead

-- |The type of a 'SymbolOrAlias'.
data HeadType
    = Alias
    | Symbol

-- |Given a KoreIndexedModule and a head, retrieves the head type.
getHeadType
    :: (HasCallStack, MetaOrObject level)
    => IndexedModule sortParam patternType declAtts axiomAtts
    -- ^ Module representing an indexed definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> HeadType
getHeadType m patternHead =
    case symbol <> alias of
        Right result -> result
        Left _ -> error $ noHead patternHead
  where
    headName = symbolOrAliasConstructor patternHead
    symbol = resolveSymbol m headName $> Symbol
    alias = resolveAlias m headName $> Alias


getSortAttributes
    :: (HasCallStack, MetaOrObject level)
    => IndexedModule sortParam patternType declAtts axiomAtts
    -> Sort level
    -> Attribute.Sort
getSortAttributes m (SortActualSort (SortActual sortId _)) =
  case resolveSort m sortId of
    Right (atts, _) -> atts
    Left _ -> error $ noSort sortId
getSortAttributes _ _ = error "Can't lookup attributes for sort variables"


{-|'resolveThing' looks up an id in an 'IndexedModule', also searching in the
imported modules.
-}
resolveThing
    ::  (  IndexedModule sortParam patternType declAtts axiomAtts
        -> Map.Map (Id level) result
        )
    -- ^ extracts the map into which to look up the id
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -> Id level
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
    ->  (  IndexedModule sortParam patternType declAtts axiomAtts
        -> Map.Map (Id level) result
        )
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -> Id level
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
    :: (MetaOrObject level, MonadError (Error e) m)
    => IndexedModule sortParam patternType declAtts axiomAtts
    -> Id level
    -> m (declAtts, SentenceSymbol level patternType)
resolveSymbol m headId =
    case resolveThing (symbolSentencesMap (Proxy :: Proxy level)) m headId of
        Nothing ->
            koreFailWithLocations [headId] (noSymbol headId)
        Just result ->
            return result

{-|'resolveAlias' looks up a symbol id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveAlias
    :: (MetaOrObject level, MonadError (Error e) m)
    => IndexedModule param pat declAtts axiomAtts
    -> Id level
    -> m (declAtts, SentenceAlias level pat)
resolveAlias m headId =
    case resolveThing (aliasSentencesMap (Proxy :: Proxy level)) m headId of
        Nothing ->
            koreFailWithLocations [headId] (noAlias headId)
        Just result ->
            return result



{-|'resolveSort' looks up a sort id in an 'IndexedModule',
also searching in the imported modules.
-}
resolveSort
    :: (MetaOrObject level, MonadError (Error e) m)
    => IndexedModule sortParam patternType declAtts axiomAtts
    -> Id level
    -> m (Attribute.Sort, SentenceSort level patternType)
resolveSort m sortId =
    case resolveThing (sortSentencesMap (Proxy :: Proxy level)) m sortId of
        Nothing ->
            koreFailWithLocations
                [sortId]
                ("Sort '" ++ getIdForError sortId ++  "' not declared.")
        Just sortDescription ->
            return sortDescription

resolveHook
    :: IndexedModule sortParam patternType declAtts axiomAtts
    -> Text
    -> Sort Object
    -> Either (Error e) (Id Object)
resolveHook indexedModule builtinName builtinSort =
    resolveHookHandler builtinName
    $ Set.filter relevant
    $ resolveHooks indexedModule builtinName
  where
    relevant name =
        involvesSort indexedModule builtinSort (SymbolOrAlias name [])

involvesSort
    :: IndexedModule sortParam patternType declAtts axiomAtts
    -> Sort Object
    -> SymbolOrAlias Object
    -> Bool
involvesSort indexedModule builtinSort sym =
    elem builtinSort $
    (\s -> applicationSortsResult s : applicationSortsOperands s) $
    getHeadApplicationSorts indexedModule sym

resolveHookHandler
    :: Text
    -> Set (Id Object)
    -> Either (Error e) (Id Object)
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
    :: IndexedModule sortParam patternType declAtts axiomAtts
    -> Text
    -> Set (Id Object)
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
    :: MetaOrObject level
    => IndexedModule sortParam patternType declAtts axiomAtts
    -- ^ indexed module
    -> Id level
    -- ^ sort identifier
    -> Either (Error e) (SentenceSort level patternType)
findIndexedSort indexedModule sort =
    fmap getIndexedSentence (resolveSort indexedModule sort)


{- Utilities -}

-- It would make sense to put this in a `where` clause; however,
-- the fully type annotation is required even there, and that makes
-- for too much clutter.
applyToHeadSentence
    :: (MetaOrObject level)
    => (forall ssoa .  SentenceSymbolOrAlias ssoa
       => [Sort level]
       -> ssoa level pat
       -> result)
    -> IndexedModule param pat declAtts axiomAtts
    -> SymbolOrAlias level
    -> result
applyToHeadSentence f =
     applyToResolution (\ params (_, sentence) -> f params sentence)

-- It would make sense to put this in a `where` clause; however,
-- the fully type annotation is required even there, and that makes
-- for too much clutter.
applyToAttributes
    :: MetaOrObject level
    => (declAtts -> result)
    -> IndexedModule sortParam patternType declAtts axiomAtts
    -- ^ module representing an indexed definition
    -> SymbolOrAlias level     -- ^the head we want to find sorts for
    -> result
applyToAttributes f =
    applyToResolution (\ _ (attrs, _) -> f attrs)


applyToResolution
    :: (HasCallStack, MetaOrObject level)
    => (forall ssoa .  SentenceSymbolOrAlias ssoa
        => [Sort level]
        -> (declAtts, ssoa level pat)
        -> result)
    -> IndexedModule param pat declAtts axiomAtts
    -> SymbolOrAlias level
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
