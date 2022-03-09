{- |
Module      : Kore.Validate.SentenceVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sentence'.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Validate.SentenceVerifier (
    verifyUniqueNames,
    SentenceVerifier,
    runSentenceVerifier,
    verifySorts,
    verifyHookedSorts,
    verifySymbols,
    verifyHookedSymbols,
    verifyAxioms,
    verifyClaims,
    verifyNonHooks,
    verifyAliasSentence,
    parseAndVerifyAxiomAttributes,
) where

import Control.Lens qualified as Lens
import Control.Monad (
    foldM,
 )
import Control.Monad.Reader qualified as Reader
import Control.Monad.State.Strict (
    StateT,
    runStateT,
 )
import Control.Monad.State.Strict qualified as State
import Data.Generics.Product.Fields
import Data.Map.Strict qualified as Map
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Kore.AST.Error
import Kore.Attribute.Axiom qualified as Attribute (
    Axiom,
    parseAxiomAttributes,
 )
import Kore.Attribute.Hook qualified as Attribute
import Kore.Attribute.Parser (
    ParseAttributes,
 )
import Kore.Attribute.Parser qualified as Attribute.Parser
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Attribute.Sort qualified as Attribute (
    Sort,
 )
import Kore.Attribute.Sort qualified as Attribute.Sort
import Kore.Attribute.Sort.HasDomainValues qualified as Attribute.HasDomainValues
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Attribute.Symbol qualified as Attribute.Symbol
import Kore.Builtin qualified as Builtin
import Kore.Equation.Validate
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers as Resolvers
import Kore.Internal.Symbol qualified as Symbol
import Kore.Internal.TermLike.TermLike (
    freeVariables,
 )
import Kore.Reachability (
    SomeClaim,
    extractClaim,
    lensClaimPattern,
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern,
    freeVariablesLeft,
    freeVariablesRight,
 )
import Kore.Sort
import Kore.Syntax.Definition
import Kore.Syntax.Variable
import Kore.Validate.AttributesVerifier
import Kore.Validate.Error
import Kore.Validate.PatternVerifier as PatternVerifier
import Kore.Validate.SortVerifier
import Kore.Validate.Verifier
import Kore.Verified qualified as Verified
import Prelude.Kore

{- |'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames ::
    [Sentence pat] ->
    -- | Names that are already defined.
    Map.Map Text AstLocation ->
    -- | On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
    Either (Error VerifyError) (Map.Map Text AstLocation)
verifyUniqueNames sentences existingNames =
    foldM verifyUniqueId existingNames definedNames
  where
    definedNames =
        concatMap definedNamesForSentence sentences

data UnparameterizedId = UnparameterizedId
    { unparameterizedIdName :: Text
    , unparameterizedIdLocation :: AstLocation
    }
    deriving stock (Show)

toUnparameterizedId :: Id -> UnparameterizedId
toUnparameterizedId Id{getId = name, idLocation = location} =
    UnparameterizedId
        { unparameterizedIdName = name
        , unparameterizedIdLocation = location
        }

verifyUniqueId ::
    Map.Map Text AstLocation ->
    UnparameterizedId ->
    Either (Error VerifyError) (Map.Map Text AstLocation)
verifyUniqueId existing (UnparameterizedId name location) =
    case Map.lookup name existing of
        Just location' ->
            koreFailWithLocations
                [location, location']
                ("Duplicated name: " <> name <> ".")
        _ -> Right (Map.insert name location existing)

definedNamesForSentence :: Sentence pat -> [UnparameterizedId]
definedNamesForSentence (SentenceAliasSentence sentenceAlias) =
    [toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias)]
definedNamesForSentence (SentenceSymbolSentence sentenceSymbol) =
    [toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol)]
definedNamesForSentence (SentenceImportSentence _) = []
definedNamesForSentence (SentenceAxiomSentence _) = []
definedNamesForSentence (SentenceClaimSentence _) = []
definedNamesForSentence (SentenceSortSentence sentenceSort) =
    [toUnparameterizedId (sentenceSortName sentenceSort)]
definedNamesForSentence (SentenceHookSentence (SentenceHookedSort sentence)) =
    definedNamesForSentence (SentenceSortSentence sentence)
definedNamesForSentence (SentenceHookSentence (SentenceHookedSymbol sentence)) =
    definedNamesForSentence (SentenceSymbolSentence sentence)

type SentenceVerifier = StateT VerifiedModule' Verifier

-- | Look up a sort declaration.
findSort :: Id -> SentenceVerifier SentenceSort
findSort identifier = do
    verifiedModule <- State.get
    findIndexedSort (indexedModuleSyntax verifiedModule) identifier

askVerifierContext :: SentenceVerifier VerifierContext
askVerifierContext = Reader.ask

-- | Construct a 'PatternVerifier.Context' in the current 'SentenceContext'.
askPatternContext ::
    -- | Declared sort variables
    Set SortVariable ->
    SentenceVerifier PatternVerifier.Context
askPatternContext variables = do
    verifiedModule <- State.get
    VerifierContext{builtinVerifiers} <- askVerifierContext
    let context =
            PatternVerifier.verifiedModuleContext (indexedModuleSyntax verifiedModule)
                & PatternVerifier.withBuiltinVerifiers builtinVerifiers
                & Lens.set (field @"declaredSortVariables") variables
    return context

{- | Find the attributes for the named sort.

It is an error to use this before 'verifySorts'.
-}
lookupSortAttributes :: Id -> SentenceVerifier Attribute.Sort
lookupSortAttributes name = do
    verifiedModule <- State.get
    (attrs, _) <- Resolvers.resolveSort (indexedModuleSyntax verifiedModule) name
    return attrs

runSentenceVerifier ::
    SentenceVerifier a ->
    VerifiedModule' ->
    Verifier (a, VerifiedModule')
runSentenceVerifier sentenceVerifier verifiedModule =
    runStateT sentenceVerifier verifiedModule

verifyHookedSorts :: [ParsedSentence] -> SentenceVerifier ()
verifyHookedSorts =
    traverse_ verifyHookedSortSentence
        . mapMaybe projectSentenceHookedSort

verifyHookedSortSentence :: SentenceSort -> SentenceVerifier ()
verifyHookedSortSentence sentence =
    withSentenceHookContext (SentenceHookedSort sentence) $ do
        let SentenceSort{sentenceSortAttributes} = sentence
        hook <-
            verifySortHookAttribute
                sentenceSortAttributes
        let SentenceSort{sentenceSortName = name} = sentence
        attrs <- lookupSortAttributes name
        VerifierContext{builtinVerifiers} <- Reader.ask
        verifiedModule <- State.get
        Builtin.sortDeclVerifier
            builtinVerifiers
            hook
            verifiedModule
            sentence
            attrs
            & either throwError return
        State.modify' $ addIndexedModuleHook name hook

verifyHookedSymbols ::
    [ParsedSentence] ->
    SentenceVerifier ()
verifyHookedSymbols =
    traverse_ verifyHookedSymbolSentence
        . mapMaybe projectSentenceHookedSymbol

verifyHookedSymbolSentence :: SentenceSymbol -> SentenceVerifier ()
verifyHookedSymbolSentence sentence =
    withSentenceHookContext (SentenceHookedSymbol sentence) $ do
        let SentenceSymbol{sentenceSymbolAttributes} = sentence
        hook <- verifySymbolHookAttribute sentenceSymbolAttributes
        VerifierContext{builtinVerifiers} <- Reader.ask
        verifiedModule <- State.get
        Builtin.runSymbolVerifier
            (Builtin.symbolVerifier builtinVerifiers hook)
            (findIndexedSort (indexedModuleSyntax verifiedModule))
            sentence
            & either throwError return
        let Symbol{symbolConstructor = name} = sentenceSymbolSymbol sentence
        State.modify' $ addIndexedModuleHook name hook

addIndexedModuleHook ::
    Id ->
    Attribute.Hook ->
    VerifiedModule' ->
    VerifiedModule'
addIndexedModuleHook name hook =
    Lens.over (field @"indexedModuleSyntax" . field @"indexedModuleHookedIdentifiers") (Set.insert name)
        . Lens.over (field @"indexedModuleHooks") addHook
  where
    addHook
        | Just hookId <- Attribute.getHook hook =
            Map.alter (Just . maybe [name] (name :)) hookId
        | otherwise = id

verifySymbols :: [ParsedSentence] -> SentenceVerifier ()
verifySymbols = traverse_ verifySymbolSentence . mapMaybe project
  where
    project sentence =
        projectSentenceSymbol sentence <|> projectSentenceHookedSymbol sentence

verifySymbolSentence ::
    SentenceSymbol ->
    SentenceVerifier Verified.SentenceSymbol
verifySymbolSentence sentence =
    withSentenceSymbolContext sentence $ do
        let sortParams = (symbolParams . sentenceSymbolSymbol) sentence
        variables <- buildDeclaredSortVariables sortParams
        let sorts = sentenceSymbolSorts sentence
        mapM_ (verifySort findSort variables) sorts
        let resultSort = sentenceSymbolResultSort sentence
        verifySort findSort variables resultSort
        attrs <- parseAttributes' $ sentenceSymbolAttributes sentence
        let isConstructor =
                Attribute.Symbol.isConstructor
                    . Attribute.Symbol.constructor
                    $ attrs
        when isConstructor (verifyConstructor sentence)
        State.modify' $ addSymbol sentence attrs
        return sentence
  where
    addSymbol verified attrs =
        Lens.over
            (field @"indexedModuleSyntax" . field @"indexedModuleSymbolSentences")
            (Map.insert name (attrs, verified))
      where
        Symbol{symbolConstructor = name} = sentenceSymbolSymbol verified

verifyConstructor ::
    Verified.SentenceSymbol ->
    SentenceVerifier ()
verifyConstructor verified = do
    resultSortId <-
        case resultSort of
            SortVariableSort _ ->
                koreFail (noConstructorWithVariableSort symbolName)
            SortActualSort _ ->
                return (getSortId resultSort)
    attrs <- lookupSortAttributes resultSortId
    let isHookedSort =
            isJust
                . Attribute.getHook
                . Attribute.Sort.hook
                $ attrs
        hasDomainValues =
            Attribute.HasDomainValues.getHasDomainValues
                . Attribute.Sort.hasDomainValues
                $ attrs
    koreFailWhen
        isHookedSort
        (noConstructorInHookedSort symbolName resultSort)
    koreFailWhen
        hasDomainValues
        (noConstructorWithDomainValues symbolName resultSort)
  where
    symbolName = (symbolConstructor . sentenceSymbolSymbol) verified
    resultSort = sentenceSymbolResultSort verified

verifyAliasSentence ::
    ParsedSentenceAlias ->
    SentenceVerifier Verified.SentenceAlias
verifyAliasSentence sentence = do
    variables <- buildDeclaredSortVariables sortParams
    mapM_ (verifySort findSort variables) sentenceAliasSorts
    verifySort findSort variables sentenceAliasResultSort
    context <- askPatternContext variables
    either throwError return . runPatternVerifier context $ do
        (declaredVariables, verifiedLeftPattern) <-
            verifyAliasLeftPattern alias sentenceAliasSorts leftPattern
        verifiedRightPattern <-
            withDeclaredVariables declaredVariables $
                verifyPattern (Just expectedSort) rightPattern
        return
            sentence
                { sentenceAliasLeftPattern = verifiedLeftPattern
                , sentenceAliasRightPattern = verifiedRightPattern
                }
  where
    SentenceAlias{sentenceAliasAlias = alias} = sentence
    SentenceAlias{sentenceAliasLeftPattern = leftPattern} = sentence
    SentenceAlias{sentenceAliasRightPattern = rightPattern} = sentence
    SentenceAlias{sentenceAliasSorts} = sentence
    SentenceAlias{sentenceAliasResultSort} = sentence
    sortParams = (aliasParams . sentenceAliasAlias) sentence
    expectedSort = sentenceAliasResultSort

verifyAxioms :: [ParsedSentence] -> SentenceVerifier ()
verifyAxioms =
    traverse_ verifyAxiomSentence
        . mapMaybe projectSentenceAxiom

verifyAxiomSentence :: SentenceAxiom ParsedPattern -> SentenceVerifier ()
verifyAxiomSentence sentence =
    withSentenceAxiomContext sentence $ do
        verifiedModule' <- State.get
        verified <- verifyAxiomSentenceWorker sentence
        attrs <-
            parseAndVerifyAxiomAttributes
                verifiedModule'
                (freeVariables sentence)
                (sentenceAxiomAttributes sentence)
        validateAxiom attrs verified
        State.modify $ addAxiom verified attrs
  where
    addAxiom verified attrs =
        Lens.over
            (field @"indexedModuleAxioms")
            ((attrs, verified) :)

verifyAxiomSentenceWorker ::
    ParsedSentenceAxiom ->
    SentenceVerifier Verified.SentenceAxiom
verifyAxiomSentenceWorker sentence = do
    let sortParams = sentenceAxiomParameters sentence
    variables <- buildDeclaredSortVariables sortParams
    context <- askPatternContext variables
    field @"sentenceAxiomPattern" (verifyStandalonePattern Nothing) sentence
        & runPatternVerifier context
        & either throwError return

verifyClaims ::
    [ParsedSentence] ->
    SentenceVerifier ()
verifyClaims =
    traverse_ verifyClaimSentence
        . mapMaybe projectSentenceClaim

verifyClaimSentence :: SentenceClaim ParsedPattern -> SentenceVerifier ()
verifyClaimSentence sentence =
    withSentenceClaimContext sentence $ do
        verifiedModule' <- State.get
        verified <- verifyAxiomSentenceWorker (getSentenceClaim sentence)
        attrs <-
            parseAndVerifyAxiomAttributes
                verifiedModule'
                (freeVariables sentence)
                (sentenceClaimAttributes sentence)
        when (rejectClaim attrs verified) $
            koreFail
                "Found claim with universally-quantified variables\
                \ appearing only on the right-hand side"
        State.modify' $ addClaim (SentenceClaim verified) attrs
  where
    addClaim verified attrs =
        Lens.over
            (field @"indexedModuleClaims")
            ((attrs, verified) :)
    rejectClaim attrs verified =
        do
            someClaim <- extractClaim @SomeClaim (attrs, SentenceClaim verified)
            let claimPattern = Lens.view lensClaimPattern someClaim
            pure (rejectClaimPattern claimPattern)
            & fromMaybe False
    rejectClaimPattern :: ClaimPattern -> Bool
    rejectClaimPattern claimPattern =
        not $ Set.isSubsetOf freeRightVars freeLeftVars
      where
        freeRightVars =
            freeVariablesRight claimPattern & FreeVariables.toSet
        freeLeftVars =
            freeVariablesLeft claimPattern & FreeVariables.toSet

verifySorts :: [ParsedSentence] -> SentenceVerifier ()
verifySorts = traverse_ verifySortSentence . mapMaybe project
  where
    project sentence =
        projectSentenceSort sentence <|> projectSentenceHookedSort sentence

verifySortSentence ::
    SentenceSort ->
    SentenceVerifier Verified.SentenceSort
verifySortSentence sentence =
    withSentenceSortContext sentence $ do
        _ <- buildDeclaredSortVariables $ sentenceSortParameters sentence
        attrs <- parseAttributes' $ sentenceSortAttributes sentence
        State.modify' $ addSort sentence attrs
        return sentence
  where
    addSort verified attrs =
        Lens.over
            (field @"indexedModuleSyntax" . field @"indexedModuleSortDescriptions")
            (Map.insert (sentenceSortName verified) (attrs, verified))

verifyNonHooks ::
    [ParsedSentence] ->
    SentenceVerifier ()
verifyNonHooks sentences =
    traverse_ verifyNonHookSentence nonHookSentences
  where
    nonHookSentences = mapMaybe project sentences
    project (SentenceHookSentence _) = Nothing
    project sentence = Just sentence

verifyNonHookSentence :: ParsedSentence -> SentenceVerifier ()
verifyNonHookSentence sentence =
    withSentenceContext sentence $
        verifyNoHookAttribute $ sentenceAttributes sentence

buildDeclaredSortVariables ::
    MonadError (Error e) error =>
    [SortVariable] ->
    error (Set.Set SortVariable)
buildDeclaredSortVariables [] = return Set.empty
buildDeclaredSortVariables (unifiedVariable : list) = do
    variables <- buildDeclaredSortVariables list
    koreFailWithLocationsWhen
        (unifiedVariable `Set.member` variables)
        [unifiedVariable]
        ( "Duplicated sort variable: "
            <> extractVariableName unifiedVariable
            <> "."
        )
    return (Set.insert unifiedVariable variables)
  where
    extractVariableName variable = getId (getSortVariable variable)

parseAttributes' ::
    forall attrs error e.
    (MonadError (Error e) error, ParseAttributes attrs) =>
    Attributes ->
    error attrs
parseAttributes' =
    Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

parseAndVerifyAxiomAttributes ::
    MonadError (Error VerifyError) error =>
    IndexedModule Verified.Pattern Attribute.Symbol attrs ->
    FreeVariables VariableName ->
    Attributes ->
    error (Attribute.Axiom Symbol.Symbol VariableName)
parseAndVerifyAxiomAttributes indexModule freeVars attrs =
    parseAxiomAttributes' attrs >>= verifyAxiomAttributes indexModule
  where
    parseAxiomAttributes' =
        Attribute.Parser.liftParser . Attribute.parseAxiomAttributes freeVars
