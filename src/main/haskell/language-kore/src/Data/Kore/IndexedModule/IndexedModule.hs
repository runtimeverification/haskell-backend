{-|
Module      : Data.Kore.IndexedModule.IndexedModule
Description : Indexed representation for a module.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.IndexedModule.IndexedModule
    ( ImplicitIndexedModule (ImplicitIndexedModule)
    , indexedModuleWithMetaSorts
    , IndexedModule
        -- the IndexedModule data constructor not included in the list on
        -- purpose.
        (indexedModuleName, indexedModuleMetaAliasSentences
        , indexedModuleObjectAliasSentences, indexedModuleMetaSymbolSentences
        , indexedModuleObjectSymbolSentences
        , indexedModuleObjectSortDescriptions
        , indexedModuleMetaSortDescriptions, indexedModuleAxioms
        , indexedModuleAttributes, indexedModuleImports
        , indexedModuleRawSentences
        )
    , indexModuleIfNeeded
    , resolveThing
    , SortDescription
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Error

import           Control.Monad        (foldM)
import qualified Data.Map             as Map
import qualified Data.Set             as Set

type SortDescription = SentenceSort Attributes

{-|'IndexedModule' represents an AST 'Module' somewhat optimized for resolving
IDs.

It contains mappings from IDs to the sentence that declares them
(or to the 'SortDescription' for sorts). Note that only symbols defined
in the current module are included.

It also contains the imported modules as 'IndexedModule's and all the other
module data in raw-ish form.

All 'IndexedModule' instances should either be returned by
'indexedModuleWithMetaSorts' or they should start from an instance created by
'indexedModuleWithDefaultImports'.
-}
data IndexedModule = IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleMetaAliasSentences
        :: !(Map.Map (Id Meta) (KoreSentenceAlias Meta))
    , indexedModuleObjectAliasSentences
        :: !(Map.Map (Id Object) (KoreSentenceAlias Object))
    , indexedModuleMetaSymbolSentences
        :: !(Map.Map (Id Meta) (KoreSentenceSymbol Meta))
    , indexedModuleObjectSymbolSentences
        :: !(Map.Map (Id Object) (KoreSentenceSymbol Object))
    , indexedModuleObjectSortDescriptions
        :: !(Map.Map (Id Object) (SortDescription Object))
    , indexedModuleMetaSortDescriptions
        :: !(Map.Map (Id Meta) (SortDescription Meta))
    , indexedModuleAxioms        :: ![KoreSentenceAxiom]
    , indexedModuleAttributes    :: !Attributes
    , indexedModuleImports       :: ![IndexedModule]
    , indexedModuleRawSentences  :: ![Sentence]
    }

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule = ImplicitIndexedModule IndexedModule

emptyIndexedModule :: ModuleName -> IndexedModule
emptyIndexedModule name =
    IndexedModule
        { indexedModuleName = name
        , indexedModuleMetaAliasSentences = Map.empty
        , indexedModuleObjectAliasSentences = Map.empty
        , indexedModuleMetaSymbolSentences = Map.empty
        , indexedModuleObjectSymbolSentences = Map.empty
        , indexedModuleObjectSortDescriptions = Map.empty
        , indexedModuleMetaSortDescriptions = Map.empty
        , indexedModuleAxioms = []
        , indexedModuleAttributes = Attributes []
        , indexedModuleImports = []
        , indexedModuleRawSentences = []
        }

{-|'indexedModuleWithDefaultImports' provides an 'IndexedModule' with the given
name and containing the implicit definitions module.
-}
indexedModuleWithDefaultImports
    :: ModuleName -> ImplicitIndexedModule -> IndexedModule
indexedModuleWithDefaultImports name (ImplicitIndexedModule implicitModule) =
    (emptyIndexedModule name)
        { indexedModuleImports = [implicitModule] }

{-|'indexedModuleWithMetaSorts' provides an 'IndexedModule' with the implicit
Kore definitions.
-}
indexedModuleWithMetaSorts
    :: ModuleName -> (ImplicitIndexedModule, Set.Set String)
indexedModuleWithMetaSorts name =
    ( ImplicitIndexedModule (emptyIndexedModule name)
        { indexedModuleMetaSortDescriptions = metaSortDescriptions }
    , Set.insert
        (show StringSort)
        (Set.map getId (Map.keysSet metaSortDescriptions))
    )

metaSortDescriptions :: Map.Map (Id Meta) (SortDescription Meta)
metaSortDescriptions = Map.fromList (map metaSortDescription metaSortsList)

metaSortDescription :: MetaSortType -> (Id Meta, SortDescription Meta)
metaSortDescription sortType =
    ( sortId
    , SentenceSort
        { sentenceSortName = sortId
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    )
  where
    sortId = Id (show sortType)

{-|'indexModuleIfNeeded' transforms a 'Module' into an 'IndexedModule', unless
the module is already in the 'IndexedModule' map.
-}
indexModuleIfNeeded
    :: ImplicitIndexedModule
    -- ^ Module containing the implicit Kore definitions
    -> Map.Map ModuleName Module
    -- ^ Map containing all defined modules, used for resolving imports.
    -> Map.Map ModuleName IndexedModule
    -- ^ Map containing all modules that were already indexed.
    -> Module
    -- ^ Module to be indexed
    -> Either
        (Error a)
        (Map.Map ModuleName IndexedModule)
    -- ^ If the module was indexed succesfully, the map returned on 'Right'
    -- contains everything that the provided 'IndexedModule' map contained,
    -- plus the current module, plus all the modules that were indexed when
    -- resolving imports.
indexModuleIfNeeded
    implicitModule nameToModule indexedModules koreModule
  =
    fst <$>
        internalIndexModuleIfNeeded
            implicitModule Set.empty nameToModule indexedModules koreModule

internalIndexModuleIfNeeded
    :: ImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName Module
    -> Map.Map ModuleName IndexedModule
    -> Module
    -> Either
        (Error a)
        (Map.Map ModuleName IndexedModule, IndexedModule)
internalIndexModuleIfNeeded
    implicitModule importingModules nameToModule indexedModules koreModule
  =
    withContext
        ("module '" ++ getModuleName koreModuleName ++ "'")
        (do
            koreFailWhen
                (koreModuleName `Set.member` importingModules)
                "Circular module import dependency."
            case Map.lookup koreModuleName indexedModules of
                Just indexedModule -> return (indexedModules, indexedModule)
                Nothing -> do
                    (newIndex, newModule) <- foldM
                        (indexModuleSentence
                            implicitModule
                            importingModulesWithCurrentOne
                            nameToModule)
                        indexedModulesAndStartingIndexedModule
                        (moduleSentences koreModule)
                    return
                        ( Map.insert koreModuleName newModule newIndex
                        , newModule
                        )
        )
  where
    indexedModulesAndStartingIndexedModule =
        ( indexedModules
        , (indexedModuleWithDefaultImports
                (moduleName koreModule) implicitModule)
            { indexedModuleAttributes =
                moduleAttributes koreModule
            , indexedModuleRawSentences =
                moduleSentences koreModule
            }
        )
    koreModuleName = moduleName koreModule
    importingModulesWithCurrentOne = Set.insert koreModuleName importingModules

indexModuleSentence
    :: ImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName Module
    -> (Map.Map ModuleName IndexedModule, IndexedModule)
    -> Sentence
    -> Either
        (Error a)
        (Map.Map ModuleName IndexedModule, IndexedModule)
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
    )
    (MetaSentenceAliasSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleMetaAliasSentences =
                Map.insert
                    (aliasConstructor (sentenceAliasAlias sentence))
                    sentence
                    sentences
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectAliasSentences = sentences }
    )
    (ObjectSentenceAliasSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectAliasSentences =
                Map.insert
                    (aliasConstructor (sentenceAliasAlias sentence))
                    sentence
                    sentences
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleMetaSymbolSentences = sentences }
    )
    (MetaSentenceSymbolSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleMetaSymbolSentences =
                Map.insert
                    (symbolConstructor (sentenceSymbolSymbol sentence))
                    sentence
                    sentences
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectSymbolSentences = sentences }
    )
    (ObjectSentenceSymbolSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectSymbolSentences =
                Map.insert
                    (symbolConstructor (sentenceSymbolSymbol sentence))
                    sentence
                    sentences
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectSortDescriptions = descriptions }
    )
    (SentenceSortSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectSortDescriptions =
                Map.insert
                    (sentenceSortName sentence)
                    sentence
                    descriptions
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule { indexedModuleAxioms = sentences }
    )
    (SentenceAxiomSentence sentence)
  =
    return
        ( indexedModules
        , indexedModule { indexedModuleAxioms = sentence : sentences }
        )
indexModuleSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule @ IndexedModule { indexedModuleImports = indexedImports }
    )
    ( SentenceImportSentence SentenceImport
        { sentenceImportModuleName = importedModuleName }
    )
  = do
    (newIndexedModules, importedModule) <-
        indexImportedModule
            implicitModule
            importingModules
            nameToModule
            indexedModules
            importedModuleName
    return
        ( newIndexedModules
        , indexedModule
            { indexedModuleImports = importedModule : indexedImports }
        )

indexImportedModule
    :: ImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName Module
    -> Map.Map ModuleName IndexedModule
    -> ModuleName
    -> Either
        (Error a)
        (Map.Map ModuleName IndexedModule, IndexedModule)
indexImportedModule
    implicitModule
    importingModules
    nameToModule
    indexedModules
    importedModuleName
  = do
    koreModule <-
        case Map.lookup importedModuleName nameToModule of
            Nothing ->
                koreFail
                    (  "Module '"
                    ++ getModuleName importedModuleName
                    ++ "' imported but not found."
                    )
            Just m -> return m
    internalIndexModuleIfNeeded
        implicitModule
        importingModules
        nameToModule
        indexedModules
        koreModule

{-|'resolveThing' looks up an id in an 'IndexedModule', also searching in the
imported modules.
-}
resolveThing
    :: (IndexedModule -> Map.Map (Id level) (thing level))
    -- ^ extracts the map into which to look up the id
    -> IndexedModule
    -> Id level
    -> Maybe (thing level)
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
    :: (Maybe (thing level), Set.Set ModuleName)
    -> (IndexedModule -> Map.Map (Id level) (thing level))
    -> IndexedModule
    -> Id level
    -> (Maybe (thing level), Set.Set ModuleName)
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
        Just thing -> (Just thing, searchedModules)
        Nothing ->
            foldr
                (\m partialResult -> resolveThingInternal
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
