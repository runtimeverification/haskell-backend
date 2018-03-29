{-# LANGUAGE GADTs #-}
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
        ( indexedModuleName, indexedModuleMetaAliasSentences
        , indexedModuleObjectAliasSentences, indexedModuleMetaSymbolSentences
        , indexedModuleObjectSymbolSentences
        , indexedModuleObjectSortDescriptions
        , indexedModuleMetaSortDescriptions, indexedModuleAxioms
        , indexedModuleAttributes, indexedModuleImports
        )
    , KoreIndexedModule
    , indexedModuleRawSentences
    , indexModuleIfNeeded
    , metaNameForObjectSort
    , resolveThing
    , SortDescription
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts

import           Control.Monad                    (foldM)
import qualified Data.Map                         as Map
import qualified Data.Set                         as Set

type SortDescription level = SentenceSort level FixedPattern Variable

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
data IndexedModule sortParam pat variable = IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleMetaAliasSentences
        :: !(Map.Map (Id Meta) (SentenceAlias Meta pat variable))
    , indexedModuleObjectAliasSentences
        :: !(Map.Map (Id Object) (SentenceAlias Object pat variable))
    , indexedModuleMetaSymbolSentences
        :: !(Map.Map (Id Meta) (SentenceSymbol Meta pat variable))
    , indexedModuleObjectSymbolSentences
        :: !(Map.Map (Id Object) (SentenceSymbol Object pat variable))
    , indexedModuleObjectSortDescriptions
        :: !(Map.Map (Id Object) (SentenceSort Object pat variable))
    , indexedModuleMetaSortDescriptions
        :: !(Map.Map (Id Meta) (SentenceSort Meta pat variable))
    , indexedModuleAxioms     :: ![SentenceAxiom sortParam pat variable]
    , indexedModuleAttributes :: !(Attributes pat variable)
    , indexedModuleImports
        :: ![(Attributes pat variable, IndexedModule sortParam pat variable)]
    }

type KoreIndexedModule =
    IndexedModule UnifiedSortVariable FixedPattern Variable

indexedModuleRawSentences  :: KoreIndexedModule -> [KoreSentence]
indexedModuleRawSentences im =
    map (MetaSentence .  SentenceAliasSentence)
        (Map.elems (indexedModuleMetaAliasSentences im))
    ++
    map (ObjectSentence . SentenceAliasSentence)
        (Map.elems (indexedModuleObjectAliasSentences im))
    ++
    map (MetaSentence . SentenceSymbolSentence)
        (Map.elems (indexedModuleMetaSymbolSentences im))
    ++
    map (ObjectSentence . SentenceSymbolSentence)
        (Map.elems (indexedModuleObjectSymbolSentences im))
    ++
    map (ObjectSentence . SentenceSortSentence)
        (Map.elems (indexedModuleObjectSortDescriptions im))
    ++
    map (MetaSentence . SentenceAxiomSentence) (indexedModuleAxioms im)
    ++
    [ MetaSentence
        (SentenceImportSentence
            (SentenceImport (indexedModuleName m) attributes)
         )
    | (attributes, m) <- indexedModuleImports im
    ]

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule sortParam pat variable =
    ImplicitIndexedModule (IndexedModule sortParam pat variable)

type KoreImplicitIndexedModule =
    ImplicitIndexedModule UnifiedSortVariable FixedPattern Variable

emptyIndexedModule :: ModuleName -> IndexedModule sortParam pat variable
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
        }

{-|'indexedModuleWithDefaultImports' provides an 'IndexedModule' with the given
name and containing the implicit definitions module.
-}
indexedModuleWithDefaultImports
    :: ModuleName
    -> ImplicitIndexedModule sortParam pat variable
    -> IndexedModule sortParam pat variable
indexedModuleWithDefaultImports name (ImplicitIndexedModule implicitModule) =
    (emptyIndexedModule name)
        { indexedModuleImports = [(Attributes [], implicitModule)] }

{-|'indexedModuleWithMetaSorts' provides an 'IndexedModule' with the implicit
Kore definitions.
-}
indexedModuleWithMetaSorts
    :: ModuleName
    -> (ImplicitIndexedModule sortParam pat variable, Set.Set String)
indexedModuleWithMetaSorts name =
    ( ImplicitIndexedModule (emptyIndexedModule name)
        { indexedModuleMetaSortDescriptions = msd }
    , Set.insert
        (show StringSort)
        (Set.map getId (Map.keysSet msd))
    )
  where
    msd = metaSortDescriptions

metaSortDescriptions :: Map.Map (Id Meta) (SentenceSort Meta pat variable)
metaSortDescriptions = Map.fromList (map metaSortDescription metaSortsList)

metaSortDescription :: MetaSortType -> (Id Meta, SentenceSort Meta pat variable)
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
    :: KoreImplicitIndexedModule
    -- ^ Module containing the implicit Kore definitions
    -> Map.Map ModuleName KoreModule
    -- ^ Map containing all defined modules, used for resolving imports.
    -> Map.Map ModuleName KoreIndexedModule
    -- ^ Map containing all modules that were already indexed.
    -> KoreModule
    -- ^ Module to be indexed
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule)
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
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> Map.Map ModuleName KoreIndexedModule
    -> KoreModule
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
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
            }
        )
    koreModuleName = moduleName koreModule
    importingModulesWithCurrentOne = Set.insert koreModuleName importingModules

indexModuleSentence
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
    -> KoreSentence
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
    )
    (MetaSentence (SentenceAliasSentence sentence))
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
    (ObjectSentence (SentenceAliasSentence sentence))
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
    (MetaSentence (SentenceSymbolSentence sentence))
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
    (ObjectSentence (SentenceSymbolSentence sentence))
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
    implicitModule
    importingModules
    nameToModule
    indexedStuff
    (ObjectSentence (SentenceSortSentence sentence))
  = do
    (indexedModules, indexedModule) <-
        indexModuleSentence
            implicitModule
            importingModules
            nameToModule
            indexedStuff
            (MetaSentence
                (SentenceSymbolSentence SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor =
                            Id
                                (metaNameForObjectSort
                                    (getId (sentenceSortName sentence))
                                )
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts =
                        map (const sortMetaSort)
                            (sentenceSortParameters sentence)
                    , sentenceSymbolResultSort = sortMetaSort
                    , sentenceSymbolAttributes = Attributes []
                    }
                )
            )

    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectSortDescriptions =
                Map.insert
                    (sentenceSortName sentence)
                    sentence
                    (indexedModuleObjectSortDescriptions indexedModule)
            }
        )
indexModuleSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule { indexedModuleAxioms = sentences }
    )
    (MetaSentence (SentenceAxiomSentence sentence))
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
    (MetaSentence
        (SentenceImportSentence SentenceImport
            { sentenceImportModuleName = importedModuleName
            , sentenceImportAttributes = attributes
            }
        )
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
            { indexedModuleImports =
                (attributes, importedModule) : indexedImports
            }
        )

indexImportedModule
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> Map.Map ModuleName KoreIndexedModule
    -> ModuleName
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
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
        Just thing -> (Just thing, searchedModules)
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

metaNameForObjectSort :: String -> String
metaNameForObjectSort name = "#`" ++ name
