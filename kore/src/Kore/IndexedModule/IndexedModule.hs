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
        ( indexedModuleName, indexedModuleAliasSentences
        , indexedModuleSymbolSentences
        , indexedModuleSortDescriptions
        , indexedModuleAxioms, indexedModuleClaims
        , indexedModuleAttributes, indexedModuleImports
        , indexedModuleHooks
        )
    , KoreImplicitIndexedModule
    , KoreIndexedModule
    , VerifiedModule
    , makeIndexedModuleAttributesNull
    , mapIndexedModulePatterns
    , indexedModuleRawSentences
    , indexModuleIfNeeded
    , metaNameForObjectSort
    , SortDescription
    , getIndexedSentence
    , hookedObjectSymbolSentences
    , indexedModuleSubsorts
    , indexedModulesInScope
    , toVerifiedPureModule
    , toVerifiedPureDefinition
    , recursiveIndexedModuleSortDescriptions
    , recursiveIndexedModuleAxioms
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Control.Monad
                 ( foldM )
import           Control.Monad.State.Strict
                 ( execState )
import qualified Control.Monad.State.Strict as Monad.State
import           Data.Bifunctor
import           Data.Default as Default
import qualified Data.Foldable as Foldable
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.Attribute.Hook
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Sort as Attribute
import           Kore.Attribute.Subsort
import           Kore.Error

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
-- TODO (thomas.tuegel): Consider splitting IndexedModule into separate sort,
-- symbol, and axiom indices.
data IndexedModule param pat declAtts axiomAtts =
    IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleAliasSentences
        :: !(Map.Map (Id Object) (declAtts, SentenceAlias Object pat))
    , indexedModuleSymbolSentences
        :: !(Map.Map (Id Object) (declAtts, SentenceSymbol Object pat))
    , indexedModuleSortDescriptions
        :: !(Map.Map (Id Object) (Attribute.Sort, SentenceSort Object pat))
    , indexedModuleAxioms :: ![(axiomAtts, SentenceAxiom param pat)]
    , indexedModuleClaims :: ![(axiomAtts, SentenceAxiom param pat)]
    , indexedModuleAttributes :: !(declAtts, Attributes)
    , indexedModuleImports
        :: ![( declAtts
             , Attributes
             , IndexedModule param pat declAtts axiomAtts
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
    deriving (Generic, Show)

recursiveIndexedModuleSortDescriptions
    :: forall param pat declAtts axiomAtts
    .  IndexedModule param pat declAtts axiomAtts
    -> Map.Map (Id Object) (Attribute.Sort, SentenceSort Object pat)
recursiveIndexedModuleSortDescriptions =
    recursiveIndexedModuleStuff indexedModuleSortDescriptions

recursiveIndexedModuleAxioms
    :: forall param pat declAtts axiomAtts
    .  IndexedModule param pat declAtts axiomAtts
    -> [(axiomAtts, SentenceAxiom param pat)]
recursiveIndexedModuleAxioms = recursiveIndexedModuleStuff indexedModuleAxioms

recursiveIndexedModuleStuff
    :: forall param pat declAtts axiomAtts stuff
    .  (Monoid stuff)
    => (IndexedModule param pat declAtts axiomAtts -> stuff)
    -> IndexedModule param pat declAtts axiomAtts
    -> stuff
recursiveIndexedModuleStuff stuffExtractor m =
    Foldable.fold
        (stuffExtractor m : subModuleStuffs)
  where
    subModuleStuffs :: [stuff]
    subModuleStuffs =
        map subModuleStuff (indexedModuleImports m)
    subModuleStuff
        ::  ( declAtts
            , Attributes
            , IndexedModule param pat declAtts axiomAtts
            )
        -> stuff
    subModuleStuff (_, _, subMod) =
        recursiveIndexedModuleStuff stuffExtractor subMod

-- |Strip module of its parsed attributes, replacing them with 'Attribute.Null'
makeIndexedModuleAttributesNull
    :: IndexedModule sortParam patternType1 declAttributes axiomAttributes
    -> IndexedModule sortParam patternType1 Attribute.Null Attribute.Null
makeIndexedModuleAttributesNull
    IndexedModule
    { indexedModuleName = name
    , indexedModuleAliasSentences = aliases
    , indexedModuleSymbolSentences = symbols
    , indexedModuleSortDescriptions = sorts
    , indexedModuleAxioms = axioms
    , indexedModuleClaims = claims
    , indexedModuleAttributes = attributes
    , indexedModuleImports = imports
    , indexedModuleHookedIdentifiers = hookIds
    , indexedModuleHooks = hooks
    }
  = IndexedModule
    { indexedModuleName = name
    , indexedModuleAliasSentences = Map.map (first aNull) aliases
    , indexedModuleSymbolSentences = Map.map (first aNull) symbols
    , indexedModuleSortDescriptions = sorts
    , indexedModuleAxioms = map (first aNull) axioms
    , indexedModuleClaims = map (first aNull) claims
    , indexedModuleAttributes = first aNull attributes
    , indexedModuleImports =
        map
            (\(_, atts, m)->
                (Attribute.Null, atts, makeIndexedModuleAttributesNull m))
            imports
    , indexedModuleHookedIdentifiers = hookIds
    , indexedModuleHooks = hooks
    }
  where
    aNull = const Attribute.Null



instance
    ( NFData sortParam
    , NFData patternType
    , NFData declAttributes
    , NFData axiomAttributes
    ) =>
    NFData (IndexedModule sortParam patternType declAttributes axiomAttributes)

-- |Convenient notation for retrieving a sentence from a
-- @(attributes,sentence)@ pair format.
getIndexedSentence :: (atts, sentence) -> sentence
getIndexedSentence = snd

mapIndexedModulePatterns
    :: (patternType1 -> patternType2)
    -> IndexedModule sortParam patternType1 declAttributes axiomAttributes
    -> IndexedModule sortParam patternType2 declAttributes axiomAttributes
mapIndexedModulePatterns mapping indexedModule =
    indexedModule
        { indexedModuleAliasSentences =
            fmap (fmap mapping) <$> indexedModuleAliasSentences
        , indexedModuleSymbolSentences =
            fmap (fmap mapping) <$> indexedModuleSymbolSentences
        , indexedModuleSortDescriptions =
            fmap (fmap mapping) <$> indexedModuleSortDescriptions
        , indexedModuleAxioms =
            fmap (fmap mapping) <$> indexedModuleAxioms
        , indexedModuleClaims =
            fmap (fmap mapping) <$> indexedModuleClaims
        , indexedModuleImports =
            mapIndexedModuleImports <$> indexedModuleImports
        }
  where
    IndexedModule { indexedModuleAliasSentences } = indexedModule
    IndexedModule { indexedModuleSymbolSentences } = indexedModule
    IndexedModule { indexedModuleSortDescriptions } = indexedModule
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

{- | Convert a 'VerifiedModule' back into a 'Module'.

The original module attributes /are/ preserved.

 -}
toVerifiedPureModule
    :: VerifiedModule declAtts axiomAtts
    -> VerifiedPureModule Object
toVerifiedPureModule module' =
    Module
        { moduleName = indexedModuleName module'
        , moduleSentences =
            sentenceKoreToPure <$> indexedModuleRawSentences module'
        , moduleAttributes = snd (indexedModuleAttributes module')
        }

{- | Convert any collection of 'VerifiedModule's back into a 'Definition'.

The definition attributes are lost in the process of indexing the original
definition.

Although all 'IndexedModule's refer to the implicit Kore module, it is not
included in the output of this function because it is /implicit/.

See also: 'toVerifiedPureModule'

 -}
toVerifiedPureDefinition
    :: Foldable t
    => t (VerifiedModule declAtts axiomAtts)
    -> VerifiedPureDefinition Object
toVerifiedPureDefinition idx =
    Definition
        { definitionAttributes = Default.def
        , definitionModules =
            toVerifiedPureModule
            <$> filter notImplicitKoreModule (Foldable.toList idx)
        }
  where
    notImplicitKoreModule verifiedModule =
        indexedModuleName verifiedModule /= "kore"

indexedModuleRawSentences
    :: IndexedModule param pat atts atts' -> [UnifiedSentence param pat]
indexedModuleRawSentences im =
    map (constructUnifiedSentence SentenceAliasSentence . getIndexedSentence)
        (Map.elems (indexedModuleAliasSentences im))
    ++
    map hookSymbolIfNeeded
        (Map.toList (indexedModuleSymbolSentences im))
    ++
    map hookSortIfNeeded
        (Map.toList (indexedModuleSortDescriptions im))
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
newtype ImplicitIndexedModule param pat declAtts axiomAtts =
    ImplicitIndexedModule (IndexedModule param pat declAtts axiomAtts)
    deriving (Show)

type KoreImplicitIndexedModule =
    ImplicitIndexedModule
        UnifiedSortVariable
        CommonKorePattern

emptyIndexedModule
    ::  ( Default parsedDeclAttributes
        , Default parsedAxiomAttributes
        )
    => ModuleName
    -> IndexedModule param pat parsedDeclAttributes parsedAxiomAttributes
emptyIndexedModule name =
    IndexedModule
    { indexedModuleName = name
    , indexedModuleAliasSentences = Map.empty
    , indexedModuleSymbolSentences = Map.empty
    , indexedModuleSortDescriptions = Map.empty
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
    ::  ( Default declAttrs
        , Default axiomAttrs
        )
    => ModuleName
    -> Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
    -> IndexedModule sortParam patternType declAttrs axiomAttrs
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
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
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
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
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
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> sentence
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexModuleKoreSentence a b c d =
    applyUnifiedSentence
        (indexModuleSentence a b c d)
        (indexModuleSentence a b c d)

indexModuleSentence
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> Sentence Object sortParam patternType
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed, indexed)
indexModuleSentence
    implicitModule
    importingModules
    nameToModule
    ( indexedModules
    , indexedModule@IndexedModule
        { indexedModuleAliasSentences
        , indexedModuleSymbolSentences
        , indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleImports
        , indexedModuleSortDescriptions
        , indexedModuleHookedIdentifiers
        , indexedModuleHooks
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
            SentenceHookSentence s   -> indexSentenceHook s

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
                { indexedModuleAliasSentences =
                    Map.insert aliasConstructor (atts, _sentence)
                        indexedModuleAliasSentences
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
                { indexedModuleSymbolSentences =
                    Map.insert
                        symbolConstructor
                        (atts, _sentence)
                        indexedModuleSymbolSentences
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
                { indexedModuleSortDescriptions =
                    Map.insert sentenceSortName (atts, _sentence)
                        indexedModuleSortDescriptions
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
            indexModuleSentence
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
                { indexedModuleSymbolSentences =
                    Map.insert symbolConstructor (atts, _sentence)
                        indexedModuleSymbolSentences
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
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , sentence ~ UnifiedSentence sortParam patternType
        , indexed ~ IndexedModule sortParam patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule sortParam patternType declAttrs axiomAttrs)
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
    :: IndexedModule sorts pat declAtts axiomAtts
    -> Map.Map (Id Object) (declAtts, SentenceSymbol Object pat)
hookedObjectSymbolSentences
    IndexedModule
        { indexedModuleSymbolSentences
        , indexedModuleHookedIdentifiers
        }
  =
    Map.restrictKeys
        indexedModuleSymbolSentences
        indexedModuleHookedIdentifiers

indexedModuleSubsorts
    :: IndexedModule param pat declAtts axiomAtts
    -> [Subsort]
indexedModuleSubsorts imod =
    case internalIndexedModuleSubsorts imod of
        Right subsorts -> subsorts
        Left err -> error $ "IndexedModule should already have checked"
            ++ " form of subsort attributes, but parsing failed\n:"
            ++ show err

internalIndexedModuleSubsorts
    :: IndexedModule param pat declAtts axiomAtts
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
    :: IndexedModule param pat declAtts axiomAtts
    -> Map ModuleName (IndexedModule param pat declAtts axiomAtts)
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
