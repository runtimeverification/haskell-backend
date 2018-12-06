{-|
Module      : Kore.IndexedModule.IndexedModule
Description : Indexed representation for a module.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.IndexedModule.IndexedModule
    ( ImplicitIndexedModule (ImplicitIndexedModule)
    , IndexedModule
        -- the IndexedModule data constructor not included in the list on
        -- purpose.
        ( indexedModuleName, indexedModuleMetaAliasSentences
        , indexedModuleObjectAliasSentences, indexedModuleMetaSymbolSentences
        , indexedModuleObjectSymbolSentences
        , indexedModuleObjectSortDescriptions
        , indexedModuleMetaSortDescriptions
        , indexedModuleAxioms, indexedModuleClaims
        , indexedModuleAttributes, indexedModuleImports
        , indexedModuleHooks
        )
    , KoreImplicitIndexedModule
    , KoreIndexedModule
    , VerifiedModule
    , mapIndexedModulePatterns
    , indexedModuleRawSentences
    , indexModuleIfNeeded
    , metaNameForObjectSort
    , SortDescription
    , getIndexedSentence
    , hookedObjectSymbolSentences
    , indexedModuleSubsorts
    , indexedModulesInScope
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Control.Monad
                 ( foldM )
import           Control.Monad.State.Strict
                 ( execState )
import qualified Control.Monad.State.Strict as Monad.State
import           Data.Default
import qualified Data.Foldable as Foldable
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.Sentence
import           Kore.Attribute.Hook
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Attribute.Subsort
import           Kore.Error
import           Kore.Implicit.ImplicitSorts

type SortDescription level dom =
    SentenceSort level (KorePattern dom Variable (Unified Annotation.Null))

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
data IndexedModule param pat atts =
    IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleMetaAliasSentences
        :: !(Map.Map (Id Meta) (atts, SentenceAlias Meta pat))
    , indexedModuleObjectAliasSentences
        :: !(Map.Map (Id Object) (atts, SentenceAlias Object pat))
    , indexedModuleMetaSymbolSentences
        :: !(Map.Map (Id Meta) (atts, SentenceSymbol Meta pat))
    , indexedModuleObjectSymbolSentences
        :: !(Map.Map (Id Object) (atts, SentenceSymbol Object pat))
    , indexedModuleObjectSortDescriptions
        :: !(Map.Map (Id Object) (atts, SentenceSort Object pat))
    , indexedModuleMetaSortDescriptions
        :: !(Map.Map (Id Meta) (atts, SentenceSort Meta pat))
    , indexedModuleAxioms
        :: ![(atts, SentenceAxiom param pat)]
    , indexedModuleClaims
        :: ![(atts, SentenceAxiom param pat)]
    , indexedModuleAttributes :: !(atts, Attributes)
    , indexedModuleImports
        :: ![( atts
             , Attributes
             , IndexedModule param pat atts
             )
            ]
    , indexedModuleHookedIdentifiers
        :: !(Set.Set (Id Object))
        -- ^ set of hooked identifiers

    -- TODO (thomas.tuegel): Having multiple identifiers hooked to the same
    -- builtin is not actually valid, but the index must admit invalid data
    -- because verification only happens after.
    , indexedModuleHooks
        :: !(Map.Map Text [Id Object])
        -- ^ map from builtin domain (symbol and sort) identifiers to the hooked
        -- identifiers
    }
    deriving (Functor, Generic, Show)

instance
    ( NFData sortParam
    , NFData patternType
    , NFData attributes
    ) =>
    NFData (IndexedModule sortParam patternType attributes)

-- |Convenient notation for retrieving a sentence from a
-- @(attributes,sentence)@ pair format.
getIndexedSentence :: (atts, sentence) -> sentence
getIndexedSentence = snd

mapIndexedModulePatterns
    :: (patternType1 -> patternType2)
    -> IndexedModule sortParam patternType1 attributes
    -> IndexedModule sortParam patternType2 attributes
mapIndexedModulePatterns mapping indexedModule =
    indexedModule
        { indexedModuleMetaAliasSentences =
            fmap (fmap mapping) <$> indexedModuleMetaAliasSentences
        , indexedModuleObjectAliasSentences =
            fmap (fmap mapping) <$> indexedModuleObjectAliasSentences
        , indexedModuleMetaSymbolSentences =
            fmap (fmap mapping) <$> indexedModuleMetaSymbolSentences
        , indexedModuleObjectSymbolSentences =
            fmap (fmap mapping) <$> indexedModuleObjectSymbolSentences
        , indexedModuleMetaSortDescriptions =
            fmap (fmap mapping) <$> indexedModuleMetaSortDescriptions
        , indexedModuleObjectSortDescriptions =
            fmap (fmap mapping) <$> indexedModuleObjectSortDescriptions
        , indexedModuleAxioms =
            fmap (fmap mapping) <$> indexedModuleAxioms
        , indexedModuleClaims =
            fmap (fmap mapping) <$> indexedModuleClaims
        , indexedModuleImports =
            mapIndexedModuleImports <$> indexedModuleImports
        }
  where
    IndexedModule { indexedModuleMetaAliasSentences } = indexedModule
    IndexedModule { indexedModuleObjectAliasSentences } = indexedModule
    IndexedModule { indexedModuleMetaSymbolSentences } = indexedModule
    IndexedModule { indexedModuleObjectSymbolSentences } = indexedModule
    IndexedModule { indexedModuleMetaSortDescriptions } = indexedModule
    IndexedModule { indexedModuleObjectSortDescriptions } = indexedModule
    IndexedModule { indexedModuleAxioms } = indexedModule
    IndexedModule { indexedModuleClaims } = indexedModule
    IndexedModule { indexedModuleImports } = indexedModule
    mapIndexedModuleImports (attrs, attributes, indexedModule') =
        ( attrs
        , attributes
        , mapIndexedModulePatterns mapping indexedModule'
        )

type KoreIndexedModule =
    IndexedModule UnifiedSortVariable CommonKorePattern

type VerifiedModule =
    IndexedModule UnifiedSortVariable VerifiedKorePattern

indexedModuleRawSentences
    :: IndexedModule param pat atts -> [UnifiedSentence param pat]
indexedModuleRawSentences im =
    map (constructUnifiedSentence SentenceAliasSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaAliasSentences im))
    ++
    map (constructUnifiedSentence SentenceAliasSentence . getIndexedSentence)
        (Map.elems (indexedModuleObjectAliasSentences im))
    ++
    map (constructUnifiedSentence SentenceSymbolSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaSymbolSentences im))
    ++
    map (constructUnifiedSentence SentenceSortSentence . getIndexedSentence)
        (Map.elems (indexedModuleMetaSortDescriptions im))
    ++
    map hookSymbolIfNeeded
        (Map.toList (indexedModuleObjectSymbolSentences im))
    ++
    map hookSortIfNeeded
        (Map.toList (indexedModuleObjectSortDescriptions im))
    ++
    map
        (constructUnifiedSentence SentenceAxiomSentence . getIndexedSentence)
        (indexedModuleAxioms im)
    ++
    map
        (constructUnifiedSentence SentenceClaimSentence . getIndexedSentence)
        (indexedModuleClaims im)
    ++
    [ constructUnifiedSentence SentenceImportSentence
      (SentenceImport (indexedModuleName m) attributes)
    | (_, attributes, m) <- indexedModuleImports im
    ]
  where
    hookedIds :: Set.Set (Id Object)
    hookedIds = indexedModuleHookedIdentifiers im
    hookSortIfNeeded (x, (_, sortDescription))
        | x `Set.member` hookedIds =
            constructUnifiedSentence
                SentenceHookSentence
                (SentenceHookedSort sortDescription)
        | otherwise =
            constructUnifiedSentence SentenceSortSentence sortDescription
    hookSymbolIfNeeded (x, (_, symbolSentence))
        | x `Set.member` hookedIds =
            constructUnifiedSentence
                SentenceHookSentence
                (SentenceHookedSymbol symbolSentence)
        | otherwise =
            constructUnifiedSentence SentenceSymbolSentence symbolSentence

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule param pat atts =
    ImplicitIndexedModule (IndexedModule param pat atts)

type KoreImplicitIndexedModule =
    ImplicitIndexedModule
        UnifiedSortVariable
        CommonKorePattern

emptyIndexedModule
    :: Default parsedAttributes
    => ModuleName
    -> IndexedModule param pat parsedAttributes
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
    , indexedModuleClaims = []
    , indexedModuleAttributes = (def, Attributes [])
    , indexedModuleImports = []
    , indexedModuleHookedIdentifiers = Set.empty
    , indexedModuleHooks = Map.empty
    }

{-|'indexedModuleWithDefaultImports' provides an 'IndexedModule' with the given
name and containing the implicit definitions module.
-}
indexedModuleWithDefaultImports
    :: Default attributes
    => ModuleName
    -> Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> IndexedModule sortParam patternType attributes
indexedModuleWithDefaultImports name defaultImport =
    (emptyIndexedModule name)
        { indexedModuleImports =
            case defaultImport of
                Just (ImplicitIndexedModule implicitModule) ->
                    [(def, Attributes [], implicitModule)]
                Nothing ->
                    []
        }


{-|'indexModuleIfNeeded' transforms a 'Module' into an 'IndexedModule', unless
the module is already in the 'IndexedModule' map.
-}
indexModuleIfNeeded
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -- ^ Module containing the implicit Kore definitions
    -> Map.Map ModuleName (Module sentence)
    -- ^ Map containing all defined modules, used for resolving imports.
    -> Map.Map ModuleName indexed
    -- ^ Map containing all modules that were already indexed.
    -> Module sentence
    -- ^ Module to be indexed
    -> Either
        (Error IndexModuleError)
        (Map.Map ModuleName indexed)
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
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> Map.Map ModuleName indexed
    -> Module sentence
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
internalIndexModuleIfNeeded
    implicitModule importingModules nameToModule indexedModules koreModule
  =
    withContext
        ("module '" ++ getModuleNameForError koreModuleName ++ "'")
        (do
            koreFailWhen
                (koreModuleName `Set.member` importingModules)
                "Circular module import dependency."
            case Map.lookup koreModuleName indexedModules of
                Just indexedModule -> return (indexedModules, indexedModule)
                Nothing -> do
                    parsedModuleAtts <- parseAttributes moduleAtts
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
                    -- Parse subsorts to fail now if subsort attributes are
                    -- malformed, so indexedModuleSubsorts can appear total
                    -- TODO: consider making subsorts an IndexedModule field
                    _ <- internalIndexedModuleSubsorts newModule
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
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> sentence
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexModuleKoreSentence a b c d =
    applyUnifiedSentence
        (indexModuleMetaSentence a b c d)
        (indexModuleObjectSentence a b c d)

indexModuleMetaSentence
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> Sentence Meta sortParam patternType
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexModuleMetaSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleMetaAliasSentences
        , indexedModuleMetaSymbolSentences
        , indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleImports
        , indexedModuleMetaSortDescriptions
        }
    )
    sentence
  =
    withSentenceContext sentence indexModuleMetaSentence0
  where
    indexModuleMetaSentence0 =
        case sentence of
            SentenceAliasSentence s  -> indexSentenceAlias s
            SentenceSymbolSentence s -> indexSentenceSymbol s
            SentenceAxiomSentence s  -> indexSentenceAxiom s
            SentenceClaimSentence s  -> indexSentenceClaim s
            SentenceImportSentence s -> indexSentenceImport s
            SentenceSortSentence s   -> indexSentenceSort s

    indexSentenceAlias
        _sentence@SentenceAlias
            { sentenceAliasAlias = Alias { aliasConstructor }
            , sentenceAliasAttributes
            }
      = do
        atts <- parseAttributes sentenceAliasAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleMetaAliasSentences =
                    Map.insert aliasConstructor (atts, _sentence)
                        indexedModuleMetaAliasSentences
                }
            )

    indexSentenceSymbol
        _sentence@SentenceSymbol
            { sentenceSymbolSymbol = Symbol { symbolConstructor }
            , sentenceSymbolAttributes
            }
      = do
        atts <- parseAttributes sentenceSymbolAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleMetaSymbolSentences =
                    Map.insert
                        symbolConstructor
                        (atts, _sentence)
                        indexedModuleMetaSymbolSentences
                }
            )

    indexSentenceAxiom
        _sentence@SentenceAxiom { sentenceAxiomAttributes }
      = do
        atts <- parseAttributes sentenceAxiomAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleAxioms =
                    (atts, _sentence) : indexedModuleAxioms
                }
            )

    indexSentenceClaim
        _sentence@SentenceAxiom { sentenceAxiomAttributes }
      = do
        atts <- parseAttributes sentenceAxiomAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleClaims =
                    (atts, _sentence) : indexedModuleClaims
                }
            )

    indexSentenceImport
        SentenceImport
            { sentenceImportModuleName = importedModuleName
            , sentenceImportAttributes = attributes
            }
      = do
        (newIndexedModules, importedModule) <-
            indexImportedModule
                implicitModule
                importingModules
                nameToModule
                indexedModules
                importedModuleName
        atts <- parseAttributes attributes
        return
            ( newIndexedModules
            , indexedModule
                { indexedModuleImports =
                    (:) (atts, attributes, importedModule)
                        indexedModuleImports
                }
            )

    indexSentenceSort
        _sentence@SentenceSort
            { sentenceSortAttributes
            , sentenceSortName
            }
      = do
        atts <- parseAttributes sentenceSortAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleMetaSortDescriptions =
                    Map.insert sentenceSortName (atts, _sentence)
                        indexedModuleMetaSortDescriptions
                }
            )

indexModuleObjectSentence
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> Sentence Object sortParam patternType
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexModuleObjectSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleObjectAliasSentences
        , indexedModuleObjectSymbolSentences
        , indexedModuleObjectSortDescriptions
        , indexedModuleHookedIdentifiers
        , indexedModuleHooks
        }
    )
    _sentence
  =
    withSentenceContext _sentence indexModuleObjectSentence0
  where
    indexModuleObjectSentence0 =
        case _sentence of
            SentenceAliasSentence s -> indexSentenceAlias s
            SentenceSymbolSentence s -> indexSentenceSymbol s
            SentenceSortSentence s -> indexSentenceSort s
            SentenceHookSentence s -> indexSentenceHook s

    indexSentenceAlias
        _sentence@SentenceAlias
            { sentenceAliasAlias = Alias { aliasConstructor }
            , sentenceAliasAttributes
            }
      = do
        atts <- parseAttributes sentenceAliasAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleObjectAliasSentences =
                    Map.insert aliasConstructor (atts, _sentence)
                        indexedModuleObjectAliasSentences
                }
            )

    indexSentenceSymbol
        _sentence@SentenceSymbol
            { sentenceSymbolSymbol = Symbol { symbolConstructor }
            , sentenceSymbolAttributes
            }
      = do
        atts <- parseAttributes sentenceSymbolAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleObjectSymbolSentences =
                    Map.insert symbolConstructor (atts, _sentence)
                        indexedModuleObjectSymbolSentences
                }
            )

    indexSentenceSort
        _sentence@SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }
      = do
        (indexedModules', indexedModule') <-
            indexModuleMetaSentence
                implicitModule
                importingModules
                nameToModule
                (indexedModules, indexedModule)
                (SentenceSymbolSentence
                    SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id
                                { getId =
                                    (Text.pack . metaNameForObjectSort . Text.unpack)
                                        (getId sentenceSortName)
                                , idLocation =
                                    AstLocationLifted
                                        (idLocation sentenceSortName)
                                }
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts =
                            map (const sortMetaSort) sentenceSortParameters
                        , sentenceSymbolResultSort = sortMetaSort
                        , sentenceSymbolAttributes = Attributes []
                        }
                )
        atts <- parseAttributes sentenceSortAttributes
        return
            ( indexedModules'
            , indexedModule'
                { indexedModuleObjectSortDescriptions =
                    Map.insert sentenceSortName (atts, _sentence)
                        indexedModuleObjectSortDescriptions
                }
            )

    indexSentenceHook
        (SentenceHookedSort _sentence@SentenceSort
            { sentenceSortName
            , sentenceSortAttributes
            }
        )
      = do
        (indexedModules', indexedModule') <-
            indexModuleObjectSentence
                implicitModule
                importingModules
                nameToModule
                (indexedModules, indexedModule)
                (SentenceSortSentence _sentence)
        hook <- getHookAttribute sentenceSortAttributes
        return
            ( indexedModules'
            , indexedModule'
                { indexedModuleHookedIdentifiers =
                    Set.insert sentenceSortName indexedModuleHookedIdentifiers
                , indexedModuleHooks =
                    Map.alter
                        (Just . maybe [sentenceSortName] (sentenceSortName :))
                        hook
                        indexedModuleHooks
                }
            )

    indexSentenceHook
        (SentenceHookedSymbol _sentence@SentenceSymbol
            { sentenceSymbolAttributes
            , sentenceSymbolSymbol = Symbol { symbolConstructor }
            }
        )
      = do
        atts <- parseAttributes sentenceSymbolAttributes
        hook <- getHookAttribute sentenceSymbolAttributes
        return
            ( indexedModules
            , indexedModule
                { indexedModuleObjectSymbolSentences =
                    Map.insert symbolConstructor (atts, _sentence)
                        indexedModuleObjectSymbolSentences
                , indexedModuleHookedIdentifiers =
                    Set.insert symbolConstructor indexedModuleHookedIdentifiers
                , indexedModuleHooks =
                    Map.alter
                        (Just . maybe [symbolConstructor] (symbolConstructor :))
                        hook
                        indexedModuleHooks
                }
            )

indexImportedModule
    ::  ( ParseAttributes attributes
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType attributes
        )
    => Maybe (ImplicitIndexedModule sortParam patternType attributes)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> Map.Map ModuleName indexed
    -> ModuleName
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexImportedModule
    implicitModule
    importingModules
    nameToModule
    indexedModules
    importedModuleName
  = do
    case Map.lookup importedModuleName indexedModules of
        Just indexedModule -> return (indexedModules, indexedModule)
        Nothing -> do
            koreModule <-
                case Map.lookup importedModuleName nameToModule of
                    Nothing ->
                        koreFail
                            (  "Module '"
                            ++ getModuleNameForError importedModuleName
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
parseAttributes
    :: ParseAttributes a
    => Attributes
    -> Either (Error IndexModuleError) a
parseAttributes =
    Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

{- | Retrieve those object-level symbol sentences that are hooked.

 -}
hookedObjectSymbolSentences
    :: IndexedModule sorts pat atts
    -> Map.Map (Id Object) (atts, SentenceSymbol Object pat)
hookedObjectSymbolSentences
    IndexedModule
        { indexedModuleObjectSymbolSentences
        , indexedModuleHookedIdentifiers
        }
  =
    Map.restrictKeys
        indexedModuleObjectSymbolSentences
        indexedModuleHookedIdentifiers

indexedModuleSubsorts
    :: IndexedModule param pat atts
    -> [Subsort]
indexedModuleSubsorts imod =
    case internalIndexedModuleSubsorts imod of
        Right subsorts -> subsorts
        Left err -> error $ "IndexedModule should already have checked"
            ++ "form of subsort attributes, but parsing failed\n:"
            ++ show err

internalIndexedModuleSubsorts
    :: IndexedModule param pat atts
    -> Either (Error IndexModuleError) [Subsort]
internalIndexedModuleSubsorts imod = do
    let
        attributes =
            [ sentenceAxiomAttributes
            | (_, SentenceAxiom { sentenceAxiomAttributes })
                <- indexedModuleAxioms imod
            ]
    Subsorts subsorts <-
        Attribute.Parser.liftParser
        $ Foldable.foldrM Attribute.Parser.parseAttributesWith def attributes
    return subsorts

{- | Determine all indexed modules in scope from the given module.

@indexedModulesInScope@ resolves all imported modules recursively so that
traversing the 'Map' is equivalent to traversing all the (transitively) imported
modules once.

 -}
indexedModulesInScope
    :: IndexedModule param pat atts
    -> Map ModuleName (IndexedModule param pat atts)
indexedModulesInScope =
    \imod -> execState (resolveModule imod) Map.empty
  where
    unlessM condM action = do
        cond <- condM
        if cond then return () else action

    alreadyResolved name =
        Monad.State.gets (Map.member name)

    {- | Resolve one indexed module

    If the module is not already part of the result, insert it and resolve its
    imports. If the module is already part of the result, skip it.

     -}
    resolveModule imod =
        unlessM (alreadyResolved name) $ do
            -- resolve the module: insert it into the map
            Monad.State.modify' (Map.insert name imod)
            -- resolve this modules imports
            mapM_ resolveImport (indexedModuleImports imod)
      where
        name = indexedModuleName imod

    resolveImport (_, _, imod) = resolveModule imod
