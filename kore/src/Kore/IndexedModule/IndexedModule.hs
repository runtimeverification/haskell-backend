{- |
Module      : Kore.IndexedModule.IndexedModule
Description : Indexed representation for a module.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.IndexedModule.IndexedModule (
    ImplicitIndexedModule (ImplicitIndexedModule),
    IndexedModule (
        -- the IndexedModule data constructor not included in the list on
        -- purpose.
        indexedModuleName,
        indexedModuleAliasSentences,
        indexedModuleSymbolSentences,
        indexedModuleSortDescriptions,
        indexedModuleAxioms,
        indexedModuleClaims,
        indexedModuleAttributes,
        indexedModuleImports,
        indexedModuleHooks
    ),
    IndexModuleError,
    KoreImplicitIndexedModule,
    KoreIndexedModule,
    VerifiedModule,
    indexedModuleWithDefaultImports,
    eraseAttributes,
    eraseAxiomAttributes,
    erasePatterns,
    emptyIndexedModule,
    mapPatterns,
    indexedModuleRawSentences,
    SortDescription,
    getIndexedSentence,
    hookedObjectSymbolSentences,
    indexedModuleSubsorts,
    internalIndexedModuleSubsorts,
    indexedModulesInScope,
    toModule,
    toVerifiedModule,
    toVerifiedDefinition,
    recursiveIndexedModuleAxioms,
    recursiveIndexedModuleSortDescriptions,
    recursiveIndexedModuleSymbolSentences,

    -- * Implicit Kore
    implicitModuleName,
    implicitNames,
    implicitSortNames,
    implicitIndexedModule,
    implicitModules,
) where

import Control.Lens qualified as Lens
import Control.Monad.Extra (
    unlessM,
 )
import Control.Monad.State.Strict (
    execState,
 )
import Control.Monad.State.Strict qualified as Monad.State
import Data.Default as Default
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import GHC.Generics (
    Generic,
 )
import Kore.Attribute.Axiom qualified as Attribute
import Kore.Attribute.Null qualified as Attribute
import Kore.Attribute.Parser qualified as Attribute.Parser
import Kore.Attribute.Sort qualified as Attribute (
    Sort,
 )
import Kore.Attribute.Subsort
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Error
import Kore.Internal.Symbol qualified as Internal.Symbol
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Verified qualified as Verified
import Prelude.Kore

type SortDescription = SentenceSort

data IndexModuleError

{- |'IndexedModule' represents an AST 'Module' somewhat optimized for resolving
IDs.

It contains mappings from IDs to the sentence that declares them
(or to the 'SortDescription' for sorts). Note that only symbols defined
in the current module are included.

It also contains the imported modules as 'IndexedModule's and all the other
module data in raw-ish form.

All 'IndexedModule' instances should be returned by
'indexedModuleWithDefaultImports'.
-}

-- TODO (thomas.tuegel): Consider splitting IndexedModule into separate sort,
-- symbol, and axiom indices.
data IndexedModule pat declAtts axiomAtts = IndexedModule
    { indexedModuleName :: !ModuleName
    , indexedModuleAliasSentences ::
        !(Map.Map Id (declAtts, SentenceAlias pat))
    , indexedModuleSymbolSentences ::
        !(Map.Map Id (declAtts, SentenceSymbol))
    , indexedModuleSortDescriptions ::
        !(Map.Map Id (Attribute.Sort, SentenceSort))
    , indexedModuleAxioms :: ![(axiomAtts, SentenceAxiom pat)]
    , indexedModuleClaims :: ![(axiomAtts, SentenceClaim pat)]
    , indexedModuleAttributes :: !(declAtts, Attributes)
    , indexedModuleImports ::
        ![ ( declAtts
           , Attributes
           , IndexedModule pat declAtts axiomAtts
           )
         ]
    , -- | set of hooked identifiers
      indexedModuleHookedIdentifiers ::
        !(Set.Set Id)
    , -- TODO (thomas.tuegel): Having multiple identifiers hooked to the same
      -- builtin is not actually valid, but the index must admit invalid data
      -- because verification only happens after.

      -- | map from builtin domain (symbol and sort) identifiers to the hooked
      -- identifiers
      indexedModuleHooks ::
        !(Map.Map Text [Id])
    }
    deriving stock (Generic, Show, Functor, Foldable, Traversable)

recursiveIndexedModuleSortDescriptions ::
    forall pat declAtts axiomAtts.
    IndexedModule pat declAtts axiomAtts ->
    Map.Map Id (Attribute.Sort, SentenceSort)
recursiveIndexedModuleSortDescriptions =
    recursiveIndexedModuleStuff indexedModuleSortDescriptions

recursiveIndexedModuleSymbolSentences ::
    forall pat axiomAtts.
    IndexedModule pat Attribute.Symbol axiomAtts ->
    Map.Map Id (Attribute.Symbol, SentenceSymbol)
recursiveIndexedModuleSymbolSentences =
    recursiveIndexedModuleStuff indexedModuleSymbolSentences

recursiveIndexedModuleAxioms ::
    forall pat declAtts axiomAtts.
    IndexedModule pat declAtts axiomAtts ->
    [(axiomAtts, SentenceAxiom pat)]
recursiveIndexedModuleAxioms = recursiveIndexedModuleStuff indexedModuleAxioms

recursiveIndexedModuleStuff ::
    forall pat declAtts axiomAtts stuff.
    (Monoid stuff) =>
    (IndexedModule pat declAtts axiomAtts -> stuff) ->
    IndexedModule pat declAtts axiomAtts ->
    stuff
recursiveIndexedModuleStuff stuffExtractor m =
    fold (stuffExtractor m : subModuleStuffs)
  where
    subModuleStuffs :: [stuff]
    subModuleStuffs =
        map subModuleStuff (indexedModuleImports m)
    subModuleStuff ::
        ( declAtts
        , Attributes
        , IndexedModule pat declAtts axiomAtts
        ) ->
        stuff
    subModuleStuff (_, _, subMod) =
        recursiveIndexedModuleStuff stuffExtractor subMod

-- | Strip module of its parsed attributes, replacing them with 'Attribute.Null'
eraseAxiomAttributes ::
    IndexedModule patternType1 declAttributes axiomAttributes ->
    IndexedModule patternType1 declAttributes Attribute.Null
eraseAxiomAttributes
    indexedModule@IndexedModule
        { indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleImports
        } =
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
eraseAttributes ::
    IndexedModule patternType1 declAttributes axiomAttributes ->
    IndexedModule patternType1 Attribute.Null Attribute.Null
eraseAttributes
    indexedModule@IndexedModule
        { indexedModuleAliasSentences
        , indexedModuleSymbolSentences
        , indexedModuleAxioms
        , indexedModuleClaims
        , indexedModuleAttributes
        , indexedModuleImports
        } =
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
    (NFData patternType, NFData declAttributes, NFData axiomAttributes) =>
    NFData (IndexedModule patternType declAttributes axiomAttributes)

{- |Convenient notation for retrieving a sentence from a
 @(attributes,sentence)@ pair format.
-}
getIndexedSentence :: (atts, sentence) -> sentence
getIndexedSentence = snd

{- | Erase the patterns carried by an 'IndexedModule'.

The alias declarations are preserved, but the right-hand side of each alias is
erased. The axiom and claim declarations are erased entirely.

This is useful because pattern verification needs to know about declared sorts,
symbols, and aliases, but it does not need to know anything about patterns.
-}
erasePatterns ::
    IndexedModule patternType1 declAttributes axiomAttributes ->
    IndexedModule () declAttributes axiomAttributes
erasePatterns indexedModule =
    indexedModule
        { indexedModuleAliasSentences =
            Lens.set (Lens.mapped . Lens._2 . Lens.mapped) () $
                indexedModuleAliasSentences indexedModule
        , indexedModuleAxioms = []
        , indexedModuleClaims = []
        , indexedModuleImports =
            Lens.over (Lens.mapped . Lens._3) erasePatterns $
                indexedModuleImports indexedModule
        }

mapPatterns ::
    (patternType1 -> patternType2) ->
    IndexedModule patternType1 declAttributes axiomAttributes ->
    IndexedModule patternType2 declAttributes axiomAttributes
mapPatterns mapping indexedModule =
    indexedModule
        { indexedModuleAliasSentences =
            (fmap . fmap . fmap) mapping indexedModuleAliasSentences
        , indexedModuleAxioms =
            (fmap . fmap . fmap) mapping indexedModuleAxioms
        , indexedModuleClaims =
            (fmap . fmap . fmap) mapping indexedModuleClaims
        , indexedModuleImports =
            indexedModuleImports
                & Lens.over (Lens.mapped . Lens._3) (mapPatterns mapping)
        }
  where
    IndexedModule{indexedModuleAliasSentences} = indexedModule
    IndexedModule{indexedModuleAxioms} = indexedModule
    IndexedModule{indexedModuleClaims} = indexedModule
    IndexedModule{indexedModuleImports} = indexedModule

type KoreIndexedModule = IndexedModule ParsedPattern

type VerifiedModule declAtts =
    IndexedModule
        Verified.Pattern
        declAtts
        (Attribute.Axiom Internal.Symbol.Symbol VariableName)

{- | Convert a 'IndexedModule' back into a 'Module'.

The original module attributes /are/ preserved.
-}
toModule ::
    IndexedModule patternType declAtts axiomAtts ->
    Module (Sentence patternType)
toModule module' =
    Module
        { moduleName = indexedModuleName module'
        , moduleSentences = indexedModuleRawSentences module'
        , moduleAttributes = snd (indexedModuleAttributes module')
        }

{- | Convert a 'VerifiedModule' back into a 'Module'.

The original module attributes /are/ preserved.
-}
toVerifiedModule ::
    VerifiedModule declAtts ->
    Module Verified.Sentence
toVerifiedModule = toModule

{- | Convert any collection of 'VerifiedModule's back into a 'Definition'.

The definition attributes are lost in the process of indexing the original
definition.

Although all 'IndexedModule's refer to the implicit Kore module, it is not
included in the output of this function because it is /implicit/.

See also: 'toVerifiedPureModule'
-}
toVerifiedDefinition ::
    Foldable t =>
    t (VerifiedModule declAtts) ->
    Definition Verified.Sentence
toVerifiedDefinition idx =
    Definition
        { definitionAttributes = Default.def
        , definitionModules =
            toVerifiedModule
                <$> filter notImplicitKoreModule (toList idx)
        }
  where
    notImplicitKoreModule verifiedModule =
        indexedModuleName verifiedModule /= "kore"

indexedModuleRawSentences ::
    IndexedModule pat atts atts' -> [Sentence pat]
indexedModuleRawSentences im =
    map
        (SentenceAliasSentence . getIndexedSentence)
        (Map.elems (indexedModuleAliasSentences im))
        ++ map
            hookSymbolIfNeeded
            (Map.toList (indexedModuleSymbolSentences im))
        ++ map
            hookSortIfNeeded
            (Map.toList (indexedModuleSortDescriptions im))
        ++ map
            (SentenceAxiomSentence . getIndexedSentence)
            (indexedModuleAxioms im)
        ++ map
            (SentenceClaimSentence . getIndexedSentence)
            (indexedModuleClaims im)
        ++ [ SentenceImportSentence
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

{- |'ImplicitIndexedModule' is the type for the 'IndexedModule' containing
things that are implicitly defined.
-}
newtype ImplicitIndexedModule pat declAtts axiomAtts
    = ImplicitIndexedModule (IndexedModule pat declAtts axiomAtts)
    deriving stock (Show)

type KoreImplicitIndexedModule = ImplicitIndexedModule ParsedPattern

emptyIndexedModule ::
    Default parsedDeclAttributes =>
    ModuleName ->
    IndexedModule pat parsedDeclAttributes parsedAxiomAttributes
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

{- |'indexedModuleWithDefaultImports' provides an 'IndexedModule' with the given
name and containing the implicit definitions module.
-}
indexedModuleWithDefaultImports ::
    Default declAttrs =>
    ModuleName ->
    Maybe (ImplicitIndexedModule patternType declAttrs axiomAttrs) ->
    IndexedModule patternType declAttrs axiomAttrs
indexedModuleWithDefaultImports name defaultImport =
    (emptyIndexedModule name)
        { indexedModuleImports =
            case defaultImport of
                Just (ImplicitIndexedModule implicitModule) ->
                    [(def, Attributes [], implicitModule)]
                Nothing ->
                    []
        }

-- | Retrieve those object-level symbol sentences that are hooked.
hookedObjectSymbolSentences ::
    IndexedModule pat declAtts axiomAtts ->
    Map.Map Id (declAtts, SentenceSymbol)
hookedObjectSymbolSentences
    IndexedModule
        { indexedModuleSymbolSentences
        , indexedModuleHookedIdentifiers
        } =
        Map.restrictKeys
            indexedModuleSymbolSentences
            indexedModuleHookedIdentifiers

indexedModuleSubsorts :: IndexedModule pat declAtts axiomAtts -> [Subsort]
indexedModuleSubsorts imod =
    case internalIndexedModuleSubsorts imod of
        Right subsorts -> subsorts
        Left err ->
            error $
                "IndexedModule should already have checked"
                    ++ " form of subsort attributes, but parsing failed\n:"
                    ++ show err

internalIndexedModuleSubsorts ::
    MonadError (Error e) error =>
    IndexedModule pat declAtts axiomAtts ->
    error [Subsort]
internalIndexedModuleSubsorts imod = do
    let attributes =
            [ sentenceAxiomAttributes
            | (_, SentenceAxiom{sentenceAxiomAttributes}) <-
                indexedModuleAxioms imod
            ]
    Subsorts subsorts <-
        Attribute.Parser.liftParser $
            foldrM Attribute.Parser.parseAttributesWith def attributes
    return subsorts

{- | Determine all indexed modules in scope from the given module.

@indexedModulesInScope@ resolves all imported modules recursively so that
traversing the 'Map' is equivalent to traversing all the (transitively) imported
modules once.
-}
indexedModulesInScope ::
    IndexedModule pat declAtts axiomAtts ->
    Map ModuleName (IndexedModule pat declAtts axiomAtts)
indexedModulesInScope =
    \imod -> execState (resolveModule imod) Map.empty
  where
    alreadyResolved name =
        Monad.State.gets (Map.member name)
    resolveModule imod =
        unlessM (alreadyResolved name) $ do
            -- resolve the module: insert it into the map
            Monad.State.modify' (Map.insert name imod)
            -- resolve this modules imports
            mapM_ resolveImport (indexedModuleImports imod)
      where
        name = indexedModuleName imod

    resolveImport (_, _, imod) = resolveModule imod

implicitModules ::
    Default declAttrs =>
    Map ModuleName (IndexedModule patternType declAttrs axiomAttrs)
implicitModules = Map.singleton implicitModuleName implicitIndexedModule

-- | The name of the module containing the implicit Kore declarations.
implicitModuleName :: ModuleName
implicitModuleName = ModuleName "kore"

-- | The 'IndexedModule' that indexes the implicit Kore declarations.
implicitIndexedModule ::
    Default declAttrs =>
    IndexedModule patternType declAttrs axiomAttrs
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
    Map.mapKeys getId $
        Map.fromSet idLocation $
            Set.insert predicateSortId implicitSortNames

implicitSortNames :: Set Id
implicitSortNames = Set.fromList [stringMetaSortId]
