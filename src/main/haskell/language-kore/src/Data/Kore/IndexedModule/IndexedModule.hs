{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

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
    , indexImplicitModule
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
    , KoreImplicitIndexedModule
    , KoreIndexedModule
    , indexedModuleRawSentences
    , indexModuleIfNeeded
    , metaNameForObjectSort
    , SortDescription
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.Sentence
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts

import           Control.Arrow                    ((&&&))
import           Control.Monad                    (foldM)
import qualified Data.Map                         as Map
import qualified Data.Set                         as Set

import           Data.Fix                         (Fix)

type SortDescription level = SentenceSort level UnifiedPattern Variable

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
    , indexedModuleAttributes :: !(Attributes)
    , indexedModuleImports
        :: ![(Attributes, IndexedModule sortParam pat variable)]
    , indexedModuleHookedIdentifiers
        :: !(Set.Set (Id Object))
    }

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show sortParam
    , Show (variable Meta)
    , Show (variable Object)
    ) => Show (IndexedModule sortParam pat variable)

type KoreIndexedModule =
    IndexedModule UnifiedSortVariable UnifiedPattern Variable

indexedModuleRawSentences  :: KoreIndexedModule -> [KoreSentence]
indexedModuleRawSentences im =
    map asSentence
        (Map.elems (indexedModuleMetaAliasSentences im))
    ++
    map asSentence
        (Map.elems (indexedModuleObjectAliasSentences im))
    ++
    map asSentence
        (Map.elems (indexedModuleMetaSymbolSentences im))
    ++
    map hookSymbolIfNeeded
        (Map.toList (indexedModuleObjectSymbolSentences im))
    ++
    map hookSortIfNeeded
        (Map.toList (indexedModuleObjectSortDescriptions im))
    ++
    map asSentence (indexedModuleAxioms im)
    ++
    [ constructUnifiedSentence SentenceImportSentence
      (SentenceImport (indexedModuleName m) attributes)
    | (attributes, m) <- indexedModuleImports im
    ]
  where
    hookedIds :: Set.Set (Id Object)
    hookedIds = indexedModuleHookedIdentifiers im
    hookSortIfNeeded :: (Id Object, SortDescription Object) -> KoreSentence
    hookSortIfNeeded (x, sortDescription)
        | x `Set.member` hookedIds =
            asSentence (SentenceHookedSort sortDescription)
        | otherwise = asSentence sortDescription
    hookSymbolIfNeeded
        :: (Id Object, KoreSentenceSymbol Object) -> KoreSentence
    hookSymbolIfNeeded (x, symbolSentence)
        | x `Set.member` hookedIds =
            asSentence (SentenceHookedSymbol symbolSentence)
        | otherwise = asSentence symbolSentence

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule sortParam pat variable =
    ImplicitIndexedModule (IndexedModule sortParam pat variable)

type KoreImplicitIndexedModule =
    ImplicitIndexedModule UnifiedSortVariable UnifiedPattern Variable

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
        , indexedModuleHookedIdentifiers = Set.empty
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
    ->  ( ImplicitIndexedModule sortParam pat variable
        , Map.Map String AstLocation
        )
indexedModuleWithMetaSorts name =
    ( ImplicitIndexedModule (emptyIndexedModule name)
        { indexedModuleMetaSortDescriptions = msd }
    , Map.insert
        (show StringSort)
        AstLocationImplicit
        (Map.fromList
            (map
                (getId &&& idLocation)
                (Set.toList (Map.keysSet msd))
            )
        )
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
    sortId = Id
        { getId = show sortType
        , idLocation = AstLocationImplicit
        }

{-|'indexImplicitModule' indexes a module containing implicit definitions, adds
it to the map of defined modules and returns the new map together with the
indexed module.

It imports the module provided as an argument, which means that it contains all
the symbols defined directly or indirectly in it. This makes it suitable for
creating a chain of implicit modules, each including its predecessor, with
the top one containing the symbols defined in all of them.
-}
indexImplicitModule
    :: (Map.Map ModuleName KoreIndexedModule, KoreImplicitIndexedModule)
    -> KoreModule
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreImplicitIndexedModule)
indexImplicitModule (indexedModules, lastIndexedModule) rawModule = do
    newModules <-
        indexModuleIfNeeded
            lastIndexedModule
            Map.empty
            indexedModules
            rawModule
    case Map.lookup (moduleName rawModule) newModules of
        Just m -> return (newModules, ImplicitIndexedModule m)
        Nothing ->
            koreFail
                (  "InternalError: indexed module not found: '"
                ++ getModuleName (moduleName rawModule)
                ++ "'"
                )


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
                        (indexModuleKoreSentence
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

indexModuleKoreSentence
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
    -> KoreSentence
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
indexModuleKoreSentence a b c d =
    applyUnifiedSentence
        (indexModuleMetaSentence a b c d)
        (indexModuleObjectSentence a b c d)

indexModuleMetaSentence
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
    -> Sentence Meta UnifiedSortVariable UnifiedPattern Variable
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
    )
    (SentenceAliasSentence sentence)
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
indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleMetaSymbolSentences = sentences }
    )
    (SentenceSymbolSentence sentence)
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
indexModuleMetaSentence
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
indexModuleMetaSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule @ IndexedModule { indexedModuleImports = indexedImports }
    )
    (SentenceImportSentence SentenceImport
        { sentenceImportModuleName = importedModuleName
        , sentenceImportAttributes = attributes
        }
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


indexModuleObjectSentence
    :: KoreImplicitIndexedModule
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
    -> Sentence Object UnifiedSortVariable UnifiedPattern Variable
    -> Either
        (Error a)
        (Map.Map ModuleName KoreIndexedModule, KoreIndexedModule)
indexModuleObjectSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectAliasSentences = sentences }
    )
    (SentenceAliasSentence sentence)
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
indexModuleObjectSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectSymbolSentences = sentences }
    )
    (SentenceSymbolSentence sentence)
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
indexModuleObjectSentence
    implicitModule
    importingModules
    nameToModule
    indexedStuff
    (SentenceSortSentence sentence)
  = do
    let sortId = sentenceSortName sentence
    (indexedModules, indexedModule) <-
        indexModuleMetaSentence
            implicitModule
            importingModules
            nameToModule
            indexedStuff
            (SentenceSymbolSentence
                SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id
                            { getId = metaNameForObjectSort (getId sortId)
                            , idLocation = AstLocationLifted (idLocation sortId)
                            }
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts =
                        map (const sortMetaSort)
                            (sentenceSortParameters sentence)
                    , sentenceSymbolResultSort = sortMetaSort
                    , sentenceSymbolAttributes = Attributes []
                    }
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
indexModuleObjectSentence
    implicitModule
    importingModules
    nameToModule
    indexedStuff
    (SentenceHookSentence (SentenceHookedSort sentence))
  = do
    let sortId = sentenceSortName sentence
    (indexedModules, indexedModule) <-
        indexModuleObjectSentence implicitModule importingModules nameToModule
            indexedStuff (SentenceSortSentence sentence)
    return
        ( indexedModules
        , indexedModule
            { indexedModuleHookedIdentifiers =
                Set.insert sortId (indexedModuleHookedIdentifiers indexedModule)

            }
        )
indexModuleObjectSentence
    _ _ _
    ( indexedModules
    , indexedModule @ IndexedModule
        { indexedModuleObjectSymbolSentences = sentences
        , indexedModuleHookedIdentifiers = hookedIds
        }
    )
    (SentenceHookSentence (SentenceHookedSymbol sentence))
    =
    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectSymbolSentences =
                Map.insert
                    symbolId
                    sentence
                    sentences
            , indexedModuleHookedIdentifiers = Set.insert symbolId hookedIds
            }
        )
  where
    symbolId = symbolConstructor (sentenceSymbolSymbol sentence)

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

metaNameForObjectSort :: String -> String
metaNameForObjectSort name = "#`" ++ name
