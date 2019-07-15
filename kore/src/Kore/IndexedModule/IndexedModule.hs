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
    , IndexModuleError
    , KoreImplicitIndexedModule
    , KoreIndexedModule
    , VerifiedModule
    , eraseAttributes
    , eraseAxiomAttributes
    , erasePatterns
    , mapPatterns
    , indexedModuleRawSentences
    , indexModuleIfNeeded
    , SortDescription
    , getIndexedSentence
    , hookedObjectSymbolSentences
    , indexedModuleSubsorts
    , indexedModulesInScope
    , toVerifiedModule
    , toVerifiedDefinition
    , recursiveIndexedModuleAxioms
    , recursiveIndexedModuleSortDescriptions
    , recursiveIndexedModuleSymbolSentences
    -- * Implicit Kore
    , implicitModuleName
    , implicitNames
    , implicitSortNames
    , implicitIndexedModule
    , implicitModules
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( foldM )
import           Control.Monad.State.Strict
                 ( execState )
import qualified Control.Monad.State.Strict as Monad.State
import           Data.Default as Default
import qualified Data.Foldable as Foldable
import           Data.Function
import qualified Data.List as List
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Error
import           Kore.Attribute.Hook
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Sort as Attribute
                 ( Sort )
import           Kore.Attribute.Subsort
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import           Kore.Error
import           Kore.Parser
                 ( ParsedPattern )
import           Kore.Syntax
import           Kore.Syntax.Definition
import qualified Kore.Verified as Verified

type SortDescription = SentenceSort (Pattern Variable Attribute.Null)

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
data IndexedModule pat declAtts axiomAtts =
    IndexedModule
    { indexedModuleName          :: !ModuleName
    , indexedModuleAliasSentences
        :: !(Map.Map Id (declAtts, SentenceAlias pat))
    , indexedModuleSymbolSentences
        :: !(Map.Map Id (declAtts, SentenceSymbol pat))
    , indexedModuleSortDescriptions
        :: !(Map.Map Id (Attribute.Sort, SentenceSort pat))
    , indexedModuleAxioms :: ![(axiomAtts, SentenceAxiom pat)]
    , indexedModuleClaims :: ![(axiomAtts, SentenceClaim pat)]
    , indexedModuleAttributes :: !(declAtts, Attributes)
    , indexedModuleImports
        :: ![( declAtts
             , Attributes
             , IndexedModule pat declAtts axiomAtts
             )
            ]
    , indexedModuleHookedIdentifiers
        :: !(Set.Set Id)
        -- ^ set of hooked identifiers

    -- TODO (thomas.tuegel): Having multiple identifiers hooked to the same
    -- builtin is not actually valid, but the index must admit invalid data
    -- because verification only happens after.
    , indexedModuleHooks
        :: !(Map.Map Text [Id])
        -- ^ map from builtin domain (symbol and sort) identifiers to the hooked
        -- identifiers
    }
    deriving (Generic, Show)

recursiveIndexedModuleSortDescriptions
    :: forall pat declAtts axiomAtts
    .  IndexedModule pat declAtts axiomAtts
    -> Map.Map Id (Attribute.Sort, SentenceSort pat)
recursiveIndexedModuleSortDescriptions =
    recursiveIndexedModuleStuff indexedModuleSortDescriptions

recursiveIndexedModuleSymbolSentences
    :: forall pat axiomAtts
    .  IndexedModule pat Attribute.Symbol axiomAtts
    -> Map.Map Id (Attribute.Symbol, SentenceSymbol pat)
recursiveIndexedModuleSymbolSentences =
    recursiveIndexedModuleStuff indexedModuleSymbolSentences

recursiveIndexedModuleAxioms
    :: forall pat declAtts axiomAtts
    .  IndexedModule pat declAtts axiomAtts
    -> [(axiomAtts, SentenceAxiom pat)]
recursiveIndexedModuleAxioms = recursiveIndexedModuleStuff indexedModuleAxioms

recursiveIndexedModuleStuff
    :: forall pat declAtts axiomAtts stuff
    .  (Monoid stuff)
    => (IndexedModule pat declAtts axiomAtts -> stuff)
    -> IndexedModule pat declAtts axiomAtts
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
            , IndexedModule pat declAtts axiomAtts
            )
        -> stuff
    subModuleStuff (_, _, subMod) =
        recursiveIndexedModuleStuff stuffExtractor subMod

-- | Strip module of its parsed attributes, replacing them with 'Attribute.Null'
eraseAxiomAttributes
    :: IndexedModule patternType1 declAttributes axiomAttributes
    -> IndexedModule patternType1 declAttributes Attribute.Null
eraseAxiomAttributes
    indexedModule@IndexedModule
        { indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleImports
        }
  =
    indexedModule
        { indexedModuleAxioms =
            indexedModuleAxioms
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleClaims =
            indexedModuleClaims
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleImports =
            indexedModuleImports
            & Lens.over (Lens.mapped . Lens._3) eraseAxiomAttributes
        }

-- | Strip module of its parsed attributes, replacing them with 'Attribute.Null'
eraseAttributes
    :: IndexedModule patternType1 declAttributes axiomAttributes
    -> IndexedModule patternType1 Attribute.Null Attribute.Null
eraseAttributes
    indexedModule@IndexedModule
        { indexedModuleAliasSentences
        , indexedModuleSymbolSentences
        , indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleAttributes
        , indexedModuleImports
        }
  =
    indexedModule
        { indexedModuleAliasSentences =
            indexedModuleAliasSentences
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleSymbolSentences =
            indexedModuleSymbolSentences
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleAxioms =
            indexedModuleAxioms
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleClaims =
            indexedModuleClaims
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
        , indexedModuleAttributes =
            indexedModuleAttributes
            & Lens.set Lens._1 Attribute.Null
        , indexedModuleImports =
            indexedModuleImports
            & Lens.set (Lens.mapped . Lens._1) Attribute.Null
            & Lens.over (Lens.mapped . Lens._3) eraseAttributes
        }

instance
    ( NFData patternType , NFData declAttributes , NFData axiomAttributes ) =>
    NFData (IndexedModule patternType declAttributes axiomAttributes)

-- |Convenient notation for retrieving a sentence from a
-- @(attributes,sentence)@ pair format.
getIndexedSentence :: (atts, sentence) -> sentence
getIndexedSentence = snd

{- | Erase the patterns carried by an 'IndexedModule'.

The alias declarations are preserved, but the right-hand side of each alias is
erased. The axiom and claim declarations are erased entirely.

This is useful because pattern verification needs to know about declared sorts,
symbols, and aliases, but it does not need to know anything about patterns.

 -}
erasePatterns
    :: IndexedModule patternType1 declAttributes axiomAttributes
    -> IndexedModule ()           declAttributes axiomAttributes
erasePatterns indexedModule =
    indexedModule
        { indexedModuleAliasSentences =
            Lens.set (Lens.mapped . Lens._2 . Lens.mapped) ()
            $ indexedModuleAliasSentences indexedModule
        , indexedModuleSymbolSentences =
            Lens.set (Lens.mapped . Lens._2 . Lens.mapped) ()
            $ indexedModuleSymbolSentences indexedModule
        , indexedModuleSortDescriptions =
            Lens.set (Lens.mapped . Lens._2 . Lens.mapped) ()
            $ indexedModuleSortDescriptions indexedModule
        , indexedModuleAxioms = []
        , indexedModuleClaims = []
        , indexedModuleImports =
            Lens.over (Lens.mapped . Lens._3) erasePatterns
            $ indexedModuleImports indexedModule
        }

mapPatterns
    :: (patternType1 -> patternType2)
    -> IndexedModule patternType1 declAttributes axiomAttributes
    -> IndexedModule patternType2 declAttributes axiomAttributes
mapPatterns mapping indexedModule =
    indexedModule
        { indexedModuleAliasSentences =
            (fmap . fmap . fmap) mapping indexedModuleAliasSentences
        , indexedModuleSymbolSentences =
            (fmap . fmap . fmap) mapping indexedModuleSymbolSentences
        , indexedModuleSortDescriptions =
            (fmap . fmap . fmap) mapping indexedModuleSortDescriptions
        , indexedModuleAxioms =
            (fmap . fmap . fmap) mapping indexedModuleAxioms
        , indexedModuleClaims =
            (fmap . fmap . fmap) mapping indexedModuleClaims
        , indexedModuleImports =
            indexedModuleImports
            & Lens.over (Lens.mapped . Lens._3) (mapPatterns mapping)
        }
  where
    IndexedModule { indexedModuleAliasSentences } = indexedModule
    IndexedModule { indexedModuleSymbolSentences } = indexedModule
    IndexedModule { indexedModuleSortDescriptions } = indexedModule
    IndexedModule { indexedModuleAxioms } = indexedModule
    IndexedModule { indexedModuleClaims } = indexedModule
    IndexedModule { indexedModuleImports } = indexedModule

type KoreIndexedModule = IndexedModule ParsedPattern

type VerifiedModule = IndexedModule Verified.Pattern

{- | Convert a 'VerifiedModule' back into a 'Module'.

The original module attributes /are/ preserved.

 -}
toVerifiedModule
    :: VerifiedModule declAtts axiomAtts
    -> Module Verified.Sentence
toVerifiedModule module' =
    Module
        { moduleName = indexedModuleName module'
        , moduleSentences = indexedModuleRawSentences module'
        , moduleAttributes = snd (indexedModuleAttributes module')
        }

{- | Convert any collection of 'VerifiedModule's back into a 'Definition'.

The definition attributes are lost in the process of indexing the original
definition.

Although all 'IndexedModule's refer to the implicit Kore module, it is not
included in the output of this function because it is /implicit/.

See also: 'toVerifiedPureModule'

 -}
toVerifiedDefinition
    :: Foldable t
    => t (VerifiedModule declAtts axiomAtts)
    -> Definition Verified.Sentence
toVerifiedDefinition idx =
    Definition
        { definitionAttributes = Default.def
        , definitionModules =
            toVerifiedModule
            <$> filter notImplicitKoreModule (Foldable.toList idx)
        }
  where
    notImplicitKoreModule verifiedModule =
        indexedModuleName verifiedModule /= "kore"

indexedModuleRawSentences
    :: IndexedModule pat atts atts' -> [Sentence pat]
indexedModuleRawSentences im =
    map (SentenceAliasSentence . getIndexedSentence)
        (Map.elems (indexedModuleAliasSentences im))
    ++
    map hookSymbolIfNeeded
        (Map.toList (indexedModuleSymbolSentences im))
    ++
    map hookSortIfNeeded
        (Map.toList (indexedModuleSortDescriptions im))
    ++
    map
        (SentenceAxiomSentence . getIndexedSentence)
        (indexedModuleAxioms im)
    ++
    map
        (SentenceClaimSentence . getIndexedSentence)
        (indexedModuleClaims im)
    ++
    [ SentenceImportSentence
      (SentenceImport (indexedModuleName m) attributes)
    | (_, attributes, m) <- indexedModuleImports im
    ]
  where
    hookedIds :: Set.Set Id
    hookedIds = indexedModuleHookedIdentifiers im
    hookSortIfNeeded (x, (_, sortDescription))
        | x `Set.member` hookedIds =
            SentenceHookSentence (SentenceHookedSort sortDescription)
        | otherwise =
            SentenceSortSentence sortDescription
    hookSymbolIfNeeded (x, (_, symbolSentence))
        | x `Set.member` hookedIds =
            SentenceHookSentence (SentenceHookedSymbol symbolSentence)
        | otherwise =
            SentenceSymbolSentence symbolSentence

{-|'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule pat declAtts axiomAtts =
    ImplicitIndexedModule (IndexedModule pat declAtts axiomAtts)
    deriving (Show)

type KoreImplicitIndexedModule = ImplicitIndexedModule ParsedPattern

emptyIndexedModule
    ::  ( Default parsedDeclAttributes
        , Default parsedAxiomAttributes
        )
    => ModuleName
    -> IndexedModule pat parsedDeclAttributes parsedAxiomAttributes
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
    -> Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs)
    -> IndexedModule patternType declAttrs axiomAttrs
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
        , Ord sentence
        , sentence ~ Sentence patternType
        , indexed ~ IndexedModule patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs)
    -- ^ Module containing the implicit Kore definitions
    -> Map.Map ModuleName (Module sentence)
    -- ^ Map containing all defined modules, used for resolving imports.
    -> Map.Map ModuleName indexed
    -- ^ Map containing all modules that were already indexed.
    -> Module sentence
    -- ^ Module to be indexed
    -> Either (Error IndexModuleError) (Map.Map ModuleName indexed)
    -- ^ If the module was indexed succesfully, the map returned on 'Right'
    -- contains everything that the provided 'IndexedModule' map contained,
    -- plus the current module, plus all the modules that were indexed when
    -- resolving imports.
indexModuleIfNeeded implicitModule nameToModule indexedModules koreModule =
    fst <$>
        internalIndexModuleIfNeeded
            implicitModule Set.empty nameToModule indexedModules koreModule

internalIndexModuleIfNeeded
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , Ord sentence
        , sentence ~ Sentence patternType
        , indexed ~ IndexedModule patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs)
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
                    (newIndex, newModule) <-
                        foldM
                            (indexModuleSentence
                                implicitModule
                                importingModulesWithCurrentOne
                                nameToModule
                            )
                            indexedModulesAndStartingIndexedModule
                            (List.sort $ moduleSentences koreModule)
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

indexModuleSentence
    ::  ( ParseAttributes declAttrs
        , ParseAttributes axiomAttrs
        , Ord sentence
        , sentence ~ Sentence patternType
        , indexed ~ IndexedModule patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs)
    -> Set.Set ModuleName
    -> Map.Map ModuleName (Module sentence)
    -> (Map.Map ModuleName indexed, indexed)
    -> Sentence patternType
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
        _sentence@(SentenceClaim SentenceAxiom { sentenceAxiomAttributes })
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
        , Ord sentence
        , sentence ~ Sentence patternType
        , indexed ~ IndexedModule patternType declAttrs axiomAttrs
        )
    => Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs)
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

{- | Parse attributes in the context of indexing a module.

'AttributeParserError's are cast to 'IndexModuleError'.

See also: 'parseAttributes'
-}
parseAttributes
    :: ParseAttributes a
    => Attributes
    -> Either (Error IndexModuleError) a
parseAttributes = Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

{- | Retrieve those object-level symbol sentences that are hooked.

 -}
hookedObjectSymbolSentences
    :: IndexedModule pat declAtts axiomAtts
    -> Map.Map Id (declAtts, SentenceSymbol pat)
hookedObjectSymbolSentences
    IndexedModule
        { indexedModuleSymbolSentences
        , indexedModuleHookedIdentifiers
        }
  =
    Map.restrictKeys
        indexedModuleSymbolSentences
        indexedModuleHookedIdentifiers

indexedModuleSubsorts :: IndexedModule pat declAtts axiomAtts -> [Subsort]
indexedModuleSubsorts imod =
    case internalIndexedModuleSubsorts imod of
        Right subsorts -> subsorts
        Left err -> error $ "IndexedModule should already have checked"
            ++ " form of subsort attributes, but parsing failed\n:"
            ++ show err

internalIndexedModuleSubsorts
    :: IndexedModule pat declAtts axiomAtts
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
    :: IndexedModule pat declAtts axiomAtts
    -> Map ModuleName (IndexedModule pat declAtts axiomAtts)
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

implicitModules
    :: (Default declAttrs, Default axiomAttrs)
    => Map ModuleName (IndexedModule patternType declAttrs axiomAttrs)
implicitModules = Map.singleton implicitModuleName implicitIndexedModule

-- | The name of the module containing the implicit Kore declarations.
implicitModuleName :: ModuleName
implicitModuleName = ModuleName "kore"

-- | The 'IndexedModule' that indexes the implicit Kore declarations.
implicitIndexedModule
    :: (Default declAttrs, Default axiomAttrs)
    => IndexedModule patternType declAttrs axiomAttrs
implicitIndexedModule =
    (emptyIndexedModule implicitModuleName)
        { indexedModuleSortDescriptions =
            Map.fromSet makeSortIndex implicitSortNames
        }
  where
    makeSortIndex sortId = (Default.def, declareSort sortId)
    declareSort sortId =
        SentenceSort
            { sentenceSortName = sortId
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

implicitNames :: Map Text AstLocation
implicitNames =
    Map.mapKeys getId
    $ Map.fromSet idLocation
    $ Set.insert predicateSortId implicitSortNames

implicitSortNames :: Set Id
implicitSortNames = Set.fromList [charMetaSortId, stringMetaSortId]
