{-|
Module      : Kore.IndexedModule.IndexedModule
Description : Indexed representation for a module.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.IndexedModule.IndexedModule
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
    , getIndexedSentence
    ) where

import           Control.Arrow
                 ( (&&&) )
import           Control.Monad
                 ( foldM )
import           Data.Default
import           Data.Functor.Classes
import           Data.Functor.Foldable
                 ( Fix )
import qualified Data.Map as Map
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.Attribute.Parser
       ( ParseAttributes, parseAttributes )
import Kore.Error
import Kore.Implicit.ImplicitSorts

type SortDescription level = SentenceSort level UnifiedPattern Variable

data IndexModuleError

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
data IndexedModule sortParam pat variable atts =
    IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleMetaAliasSentences
        :: !(Map.Map (Id Meta) (atts, SentenceAlias Meta pat variable))
    , indexedModuleObjectAliasSentences
        :: !(Map.Map (Id Object) (atts, SentenceAlias Object pat variable))
    , indexedModuleMetaSymbolSentences
        :: !(Map.Map (Id Meta) (atts, SentenceSymbol Meta pat variable))
    , indexedModuleObjectSymbolSentences
        :: !(Map.Map (Id Object) (atts, SentenceSymbol Object pat variable))
    , indexedModuleObjectSortDescriptions
        :: !(Map.Map (Id Object) (atts, SentenceSort Object pat variable))
    , indexedModuleMetaSortDescriptions
        :: !(Map.Map (Id Meta) (atts, SentenceSort Meta pat variable))
    , indexedModuleAxioms
        :: ![(atts, SentenceAxiom sortParam pat variable)]
    , indexedModuleAttributes :: !(atts, Attributes)
    , indexedModuleImports
        :: ![( atts
             , Attributes
             , IndexedModule sortParam pat variable atts
             )
            ]
    , indexedModuleHookedIdentifiers
        :: !(Set.Set (Id Object))
    }

-- |Convenient notation for retrieving a sentence from a
-- @(attributes,sentence)@ pair format.
getIndexedSentence :: (atts, sentence) -> sentence
getIndexedSentence = snd

deriving instance
    ( Show1 (pat variable), Show (pat variable (Fix (pat variable)))
    , Show sortParam
    , Show (variable Meta)
    , Show (variable Object)
    , Show parsedAttributes
    ) => Show (IndexedModule sortParam pat variable parsedAttributes)

type KoreIndexedModule =
    IndexedModule UnifiedSortVariable UnifiedPattern Variable

indexedModuleRawSentences  :: KoreIndexedModule atts -> [KoreSentence]
indexedModuleRawSentences im =
    map (asSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaAliasSentences im))
    ++
    map (asSentence . getIndexedSentence)
        (Map.elems (indexedModuleObjectAliasSentences im))
    ++
    map (asSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaSymbolSentences im))
    ++
    map (asSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaSortDescriptions im))
    ++
    map hookSymbolIfNeeded
        (Map.toList (indexedModuleObjectSymbolSentences im))
    ++
    map hookSortIfNeeded
        (Map.toList (indexedModuleObjectSortDescriptions im))
    ++
    map (asSentence . getIndexedSentence) (indexedModuleAxioms im)
    ++
    [ constructUnifiedSentence SentenceImportSentence
      (SentenceImport (indexedModuleName m) attributes)
    | (_, attributes, m) <- indexedModuleImports im
    ]
  where
    hookedIds :: Set.Set (Id Object)
    hookedIds = indexedModuleHookedIdentifiers im
    hookSortIfNeeded
        :: (Id Object, (atts, SortDescription Object)) -> KoreSentence
    hookSortIfNeeded (x, (_, sortDescription))
        | x `Set.member` hookedIds =
            asSentence (SentenceHookedSort sortDescription)
        | otherwise = asSentence sortDescription
    hookSymbolIfNeeded
        :: (Id Object, (atts, KoreSentenceSymbol Object)) -> KoreSentence
    hookSymbolIfNeeded (x, (_, symbolSentence))
        | x `Set.member` hookedIds =
            asSentence (SentenceHookedSymbol symbolSentence)
        | otherwise = asSentence symbolSentence

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule sortParam pat variable atts =
    ImplicitIndexedModule
        (IndexedModule sortParam pat variable atts)

type KoreImplicitIndexedModule =
    ImplicitIndexedModule UnifiedSortVariable UnifiedPattern Variable

emptyIndexedModule
    :: Default parsedAttributes
    => ModuleName -> IndexedModule sortParam pat variable parsedAttributes
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
    , indexedModuleAttributes = (def, Attributes [])
    , indexedModuleImports = []
    , indexedModuleHookedIdentifiers = Set.empty
    }

{-|'indexedModuleWithDefaultImports' provides an 'IndexedModule' with the given
name and containing the implicit definitions module.
-}
indexedModuleWithDefaultImports
    :: Default atts
    => ModuleName
    -> ImplicitIndexedModule sortParam pat variable atts
    -> IndexedModule sortParam pat variable atts
indexedModuleWithDefaultImports name (ImplicitIndexedModule implicitModule) =
    (emptyIndexedModule name)
        { indexedModuleImports = [(def, Attributes [], implicitModule)] }

{-|'indexedModuleWithMetaSorts' provides an 'IndexedModule' with the implicit
Kore definitions.
-}
indexedModuleWithMetaSorts
    :: Default atts
    => ModuleName
    ->  ( ImplicitIndexedModule sortParam pat variable atts
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

metaSortDescriptions
    :: Default atts => Map.Map (Id Meta) (atts, SentenceSort Meta pat variable)
metaSortDescriptions = Map.fromList (map metaSortDescription metaSortsList)

metaSortDescription
    :: Default atts
    => MetaSortType -> (Id Meta, (atts, SentenceSort Meta pat variable))
metaSortDescription sortType =
    ( sortId
    , ( def
      , SentenceSort
        { sentenceSortName = sortId
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
      )
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
    :: ParseAttributes atts
    => ( Map.Map ModuleName (KoreIndexedModule atts)
       , KoreImplicitIndexedModule atts)
    -> KoreModule
    -> Either
        (Error IndexModuleError)
        ( Map.Map ModuleName (KoreIndexedModule atts)
        , KoreImplicitIndexedModule atts)
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
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -- ^ Module containing the implicit Kore definitions
    -> Map.Map ModuleName KoreModule
    -- ^ Map containing all defined modules, used for resolving imports.
    -> Map.Map ModuleName (KoreIndexedModule atts)
    -- ^ Map containing all modules that were already indexed.
    -> KoreModule
    -- ^ Module to be indexed
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts))
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
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> Map.Map ModuleName (KoreIndexedModule atts)
    -> KoreModule
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
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
                    parsedModuleAtts <- parseAttributesInModule moduleAtts
                    let
                        indexedModulesAndStartingIndexedModule =
                            ( indexedModules
                            , (indexedModuleWithDefaultImports
                                    (moduleName koreModule) implicitModule)
                                { indexedModuleAttributes =
                                    (parsedModuleAtts, moduleAtts)
                                }
                            )
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
    moduleAtts = moduleAttributes koreModule
    koreModuleName = moduleName koreModule
    importingModulesWithCurrentOne = Set.insert koreModuleName importingModules

indexModuleKoreSentence
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
    -> KoreSentence
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
indexModuleKoreSentence a b c d =
    applyUnifiedSentence
        (indexModuleMetaSentence a b c d)
        (indexModuleObjectSentence a b c d)

indexModuleMetaSentence
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
    -> Sentence Meta UnifiedSortVariable UnifiedPattern Variable
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
    )
    (SentenceAliasSentence sentence@SentenceAlias
        { sentenceAliasAlias, sentenceAliasAttributes })
  =
    do
        atts <- parseAttributesInModule sentenceAliasAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleMetaAliasSentences =
                    Map.insert
                        (aliasConstructor sentenceAliasAlias)
                        (atts, sentence)
                        sentences
                }
            )
indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleMetaSymbolSentences = sentences }
    )
    (SentenceSymbolSentence sentence@SentenceSymbol
        { sentenceSymbolSymbol, sentenceSymbolAttributes })
  =
    do
        atts <- parseAttributesInModule sentenceSymbolAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleMetaSymbolSentences =
                    Map.insert
                        (symbolConstructor sentenceSymbolSymbol)
                        (atts, sentence)
                        sentences
                }
            )

indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule@IndexedModule { indexedModuleAxioms = sentences }
    )
    (SentenceAxiomSentence sentence@SentenceAxiom
        { sentenceAxiomAttributes })
  =
    do
        atts <- parseAttributesInModule sentenceAxiomAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleAxioms = (atts, sentence) : sentences }
            )

indexModuleMetaSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule@IndexedModule { indexedModuleImports = indexedImports }
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
    atts <- parseAttributesInModule attributes
    return
        ( newIndexedModules
        , indexedModule
            { indexedModuleImports =
                (atts, attributes, importedModule) : indexedImports
            }
        )

indexModuleMetaSentence
    _ _ _
    ( indexedModules
    , indexedModule
    )
    ( SentenceSortSentence sentence )
  =
    do
        atts <- parseAttributesInModule (sentenceSortAttributes sentence)
        return
            ( indexedModules
            , indexedModule
              { indexedModuleMetaSortDescriptions =
                  Map.insert
                  (sentenceSortName sentence)
                  (atts, sentence)
                  (indexedModuleMetaSortDescriptions indexedModule)
              }
            )

indexModuleObjectSentence
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
    -> Sentence Object UnifiedSortVariable UnifiedPattern Variable
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
indexModuleObjectSentence
    _ _ _
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleObjectAliasSentences = sentences }
    )
    (SentenceAliasSentence sentence@SentenceAlias
        { sentenceAliasAlias, sentenceAliasAttributes })
  =
    do
        atts <- parseAttributesInModule sentenceAliasAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleObjectAliasSentences =
                    Map.insert
                        (aliasConstructor sentenceAliasAlias)
                        (atts, sentence)
                        sentences
                }
            )
indexModuleObjectSentence
    _ _ _
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleObjectSymbolSentences = sentences }
    )
    (SentenceSymbolSentence sentence@SentenceSymbol
        { sentenceSymbolSymbol, sentenceSymbolAttributes })
  =
    do
        atts <- parseAttributesInModule sentenceSymbolAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleObjectSymbolSentences =
                    Map.insert
                        (symbolConstructor sentenceSymbolSymbol)
                        (atts, sentence)
                        sentences
                }
            )
indexModuleObjectSentence
    implicitModule
    importingModules
    nameToModule
    indexedStuff
    (SentenceSortSentence sentence@SentenceSort
        { sentenceSortName
        , sentenceSortParameters
        , sentenceSortAttributes
        })
  = do
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
                            { getId = metaNameForObjectSort (getId sentenceSortName)
                            , idLocation = AstLocationLifted (idLocation sentenceSortName)
                            }
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts =
                        map (const sortMetaSort) sentenceSortParameters
                    , sentenceSymbolResultSort = sortMetaSort
                    , sentenceSymbolAttributes = Attributes []
                    }
            )

    atts <- parseAttributesInModule sentenceSortAttributes
    return
        ( indexedModules
        , indexedModule
            { indexedModuleObjectSortDescriptions =
                Map.insert
                    sentenceSortName
                    (atts, sentence)
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
    , indexedModule@IndexedModule
        { indexedModuleObjectSymbolSentences = sentences
        , indexedModuleHookedIdentifiers = hookedIds
        }
    )
    (SentenceHookSentence (SentenceHookedSymbol sentence@SentenceSymbol
        { sentenceSymbolAttributes }))
    =
      do
          atts <- parseAttributesInModule sentenceSymbolAttributes
          return
              ( indexedModules
              , indexedModule
                  { indexedModuleObjectSymbolSentences =
                      Map.insert symbolId (atts, sentence) sentences
                  , indexedModuleHookedIdentifiers =
                      Set.insert symbolId hookedIds
                  }
              )
  where
    symbolId = symbolConstructor (sentenceSymbolSymbol sentence)

indexImportedModule
    :: ParseAttributes atts
    => KoreImplicitIndexedModule atts
    -> Set.Set ModuleName
    -> Map.Map ModuleName KoreModule
    -> Map.Map ModuleName (KoreIndexedModule atts)
    -> ModuleName
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName (KoreIndexedModule atts), KoreIndexedModule atts)
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

{- | Parse attributes in the context of indexing a module.

'AttributeParserError's are cast to 'IndexModuleError'.

See also: 'parseAttributes'
-}
parseAttributesInModule
    :: ParseAttributes a
    => Attributes
    -> Either (Error IndexModuleError) a
parseAttributesInModule = castError . parseAttributes
