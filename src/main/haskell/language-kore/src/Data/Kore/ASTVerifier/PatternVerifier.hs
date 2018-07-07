{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.ASTVerifier.PatternVerifier
Description : Tools for verifying the wellformedness of a Kore 'Pattern'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.PatternVerifier
    ( verifyPattern
    , verifyAliasLeftPattern
    , verifyStandalonePattern
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Error
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTHelpers
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.Resolvers
import           Data.Kore.Unparser.Unparse
import           Data.Kore.Variables.Free              (freeVariables)

import           Control.Monad                         (foldM, zipWithM_)
import qualified Data.Map                              as Map
import qualified Data.Set                              as Set

data DeclaredVariables = DeclaredVariables
    { objectDeclaredVariables :: !(Map.Map (Id Object) (Variable Object))
    , metaDeclaredVariables   :: !(Map.Map (Id Meta) (Variable Meta))
    }

emptyDeclaredVariables :: DeclaredVariables
emptyDeclaredVariables = DeclaredVariables
    { objectDeclaredVariables = Map.empty
    , metaDeclaredVariables = Map.empty
    }

data VerifyHelpers level = VerifyHelpers
    { verifyHelpersFindSort
        :: !(Id level -> Either (Error VerifyError) (SortDescription level))
    , verifyHelpersLookupAliasDeclaration
        :: !(Id level -> Either (Error VerifyError) (KoreSentenceAlias level))
    , verifyHelpersLookupSymbolDeclaration
        :: !(Id level -> Either (Error VerifyError) (KoreSentenceSymbol level))
    , verifyHelpersFindDeclaredVariables
        :: !(Id level -> Maybe (Variable level))
    }

metaVerifyHelpers :: KoreIndexedModule -> DeclaredVariables -> VerifyHelpers Meta
metaVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort = resolveSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            resolveAlias indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            resolveSymbol indexedModule
        , verifyHelpersFindDeclaredVariables =
            flip Map.lookup (metaDeclaredVariables declaredVariables)
        }

objectVerifyHelpers
    :: KoreIndexedModule -> DeclaredVariables -> VerifyHelpers Object
objectVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort = resolveSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            resolveAlias indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            resolveSymbol indexedModule
        , verifyHelpersFindDeclaredVariables =
            flip Map.lookup (objectDeclaredVariables declaredVariables)
        }

addDeclaredVariable
    :: Unified Variable -> DeclaredVariables -> DeclaredVariables
addDeclaredVariable
    (UnifiedMeta variable)
    variables@DeclaredVariables{ metaDeclaredVariables = variablesDict }
  =
    variables
        { metaDeclaredVariables =
            Map.insert (variableName variable) variable variablesDict
        }
addDeclaredVariable
    (UnifiedObject variable)
    variables@DeclaredVariables{ objectDeclaredVariables = variablesDict }
  =
    variables
        { objectDeclaredVariables =
            Map.insert (variableName variable) variable variablesDict
        }

verifyAliasLeftPattern
    :: CommonKorePattern
    -> Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> KoreIndexedModule
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables which are visible in this pattern.
    -> Either (Error VerifyError) VerifySuccess
verifyAliasLeftPattern = verifyPattern
    -- TODO: check that the left pattern is the alias symbol applied to
    -- non-repeating variables

verifyStandalonePattern
    :: KoreIndexedModule
    -> CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
verifyStandalonePattern indexedModule korePattern =
    verifyPattern korePattern Nothing indexedModule Set.empty

{-|'verifyPattern' verifies the welformedness of a Kore 'CommonKorePattern'. -}
verifyPattern
    :: CommonKorePattern
    -> Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> KoreIndexedModule
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables which are visible in this pattern.
    -> Either (Error VerifyError) VerifySuccess
verifyPattern unifiedPattern maybeExpectedSort indexedModule sortVariables = do
    freeVariables1 <- verifyFreeVariables unifiedPattern
    internalVerifyPattern
        unifiedPattern
        maybeExpectedSort
        indexedModule
        sortVariables
        freeVariables1

internalVerifyPattern
    :: CommonKorePattern
    -> Maybe UnifiedSort
    -> KoreIndexedModule
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) VerifySuccess
internalVerifyPattern
    korePattern
    mUnifiedSort
    indexedModule
    sortParamsSet
    declaredVariables
  =
    applyKorePattern
        (internalVerifyMetaPattern
            mUnifiedSort
            indexedModule
            sortParamsSet
            declaredVariables
        )
        (internalVerifyObjectPattern
            mUnifiedSort
            indexedModule
            sortParamsSet
            declaredVariables
        )
        korePattern

internalVerifyMetaPattern
    :: Maybe UnifiedSort
    -> KoreIndexedModule
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Pattern Meta Variable CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
internalVerifyMetaPattern
    maybeExpectedSort
    indexedModule
    sortVariables
    declaredVariables
    p
  =
    withLocationAndContext p (patternNameForContext p) (do
        sort <-
            verifyParameterizedPattern
                p
                indexedModule
                (metaVerifyHelpers indexedModule declaredVariables)
                sortVariables
                declaredVariables
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort
                    expectedSort
                    (UnifiedMeta sort)
            Nothing ->
                verifySuccess
    )

internalVerifyObjectPattern
    :: Maybe UnifiedSort
    -> KoreIndexedModule
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Pattern Object Variable CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
internalVerifyObjectPattern
    maybeExpectedSort
    indexedModule
    sortVariables
    declaredVariables
    p
  =
    withLocationAndContext p (patternNameForContext p) (do
        sort <- verifyParameterizedPattern
                    p
                    indexedModule
                    verifyHelpers
                    sortVariables
                    declaredVariables
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort
                    expectedSort
                    (UnifiedObject sort)
            Nothing ->
                verifySuccess
    )
  where
    verifyHelpers = objectVerifyHelpers indexedModule declaredVariables

newtype SortOrError level =
    SortOrError { getSortOrError :: Either (Error VerifyError) (Sort level) }

verifyParameterizedPattern
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyParameterizedPattern pat indexedModule helpers sortParams vars =
    getSortOrError
    $ applyPatternLeveledFunction
        PatternLeveledFunction
            { patternLeveledFunctionML = \p -> SortOrError $
                verifyMLPattern p indexedModule helpers sortParams vars
            , patternLeveledFunctionMLBinder = \p -> SortOrError $
                verifyBinder p indexedModule helpers sortParams vars
            , stringLeveledFunction = const (SortOrError verifyStringPattern)
            , charLeveledFunction = const (SortOrError verifyCharPattern)
            , applicationLeveledFunction = \p -> SortOrError $
                verifyApplication p indexedModule helpers sortParams vars
            , variableLeveledFunction = \p -> SortOrError $
                verifyVariableUsage p indexedModule helpers sortParams vars

            }
        pat

verifyMLPattern
    :: (MLPatternClass p, MetaOrObject level)
    => p level CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyMLPattern
    mlPattern
    indexedModule
    verifyHelpers
    declaredSortVariables
    declaredVariables
  = do
    mapM_
        (verifySort
            (verifyHelpersFindSort verifyHelpers)
            declaredSortVariables
        )
        (getPatternSorts mlPattern)
    verifyPatternsWithSorts
        operandSorts
        (getPatternChildren mlPattern)
        indexedModule
        declaredSortVariables
        declaredVariables
    return returnSort
  where
    returnSort = getMLPatternResultSort mlPattern
    operandSorts = getMLPatternOperandSorts mlPattern


verifyPatternsWithSorts
    :: [UnifiedSort]
    -> [CommonKorePattern]
    -> KoreIndexedModule
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) VerifySuccess
verifyPatternsWithSorts
    sorts
    operands
    indexedModule
    declaredSortVariables
    declaredVariables
  = do
    koreFailWhen (declaredOperandCount /= actualOperandCount)
        (  "Expected "
        ++ show declaredOperandCount
        ++ " operands, but got "
        ++ show actualOperandCount
        ++ "."
        )
    zipWithM_
        (\sort operand ->
            internalVerifyPattern
                operand
                (Just sort)
                indexedModule
                declaredSortVariables
                declaredVariables
        )
        sorts
        operands
    verifySuccess
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplication
    :: MetaOrObject level
    => Application level CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyApplication
    application
    indexedModule
    verifyHelpers
    declaredSortVariables
    declaredVariables
  = do
    applicationSorts <-
        verifySymbolOrAlias
            (applicationSymbolOrAlias application)
            verifyHelpers
            declaredSortVariables
    verifyPatternsWithSorts
        (map asUnified (applicationSortsOperands applicationSorts))
        (applicationChildren application)
        indexedModule
        declaredSortVariables
        declaredVariables
    return (applicationSortsResult applicationSorts)

verifyBinder
    :: (MLBinderPatternClass p, MetaOrObject level)
    => p level Variable CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyBinder
    binder
    indexedModule
    verifyHelpers
    declaredSortVariables
    declaredVariables
  = do
    verifyVariableDeclaration
        quantifiedVariable indexedModule declaredSortVariables
    verifySort
        (verifyHelpersFindSort verifyHelpers)
        declaredSortVariables
        binderSort
    internalVerifyPattern
        (getBinderPatternChild binder)
        (Just (asUnified binderSort))
        indexedModule
        declaredSortVariables
        (addDeclaredVariable (asUnified quantifiedVariable) declaredVariables)
    return binderSort
  where
    quantifiedVariable = getBinderPatternVariable binder
    binderSort = getBinderPatternSort binder

verifyVariableUsage
    :: (MetaOrObject level)
    => Variable level
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyVariableUsage variable _ verifyHelpers _ _ = do
    declaredVariable <-
        findVariableDeclaration
            (variableName variable) verifyHelpers
    koreFailWithLocationsWhen
        (variableSort variable /= variableSort declaredVariable)
        [ variable, declaredVariable ]
        "The declared sort is different."
    return (variableSort variable)

verifyStringPattern :: Either (Error VerifyError) (Sort Meta)
verifyStringPattern = Right charListMetaSort

verifyCharPattern :: Either (Error VerifyError) (Sort Meta)
verifyCharPattern = Right charMetaSort

verifyVariableDeclaration
    :: MetaOrObject level
    => Variable level
    -> KoreIndexedModule
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) VerifySuccess
verifyVariableDeclaration
    variable indexedModule declaredSortVariables
  = verifyVariableDeclarationUsing
        declaredSortVariables (resolveSort indexedModule) variable

verifyVariableDeclarationUsing
    :: MetaOrObject level
    => Set.Set UnifiedSortVariable
    -> (Id level -> Either (Error VerifyError) (SortDescription level))
    -> Variable level
    -> Either (Error VerifyError) VerifySuccess
verifyVariableDeclarationUsing declaredSortVariables f v =
    verifySort f
        declaredSortVariables
        (variableSort v)

findVariableDeclaration
    :: (MetaOrObject level)
    => Id level
    -> VerifyHelpers level
    -> Either (Error VerifyError) (Variable level)
findVariableDeclaration variableId verifyHelpers =
    case findVariables variableId of
        Nothing ->
            koreFailWithLocations
                [variableId]
                ("Unquantified variable: '" ++ getId variableId ++ "'.")
        Just variable -> Right variable
  where
    findVariables = verifyHelpersFindDeclaredVariables verifyHelpers

verifySymbolOrAlias
    :: MetaOrObject level
    => SymbolOrAlias level
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) (ApplicationSorts level)
verifySymbolOrAlias symbolOrAlias verifyHelpers declaredSortVariables =
    case (maybeSentenceSymbol, maybeSentenceAlias) of
        (Right sentenceSymbol, Left _) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceSymbol
                verifyHelpers
                declaredSortVariables
        (Left _, Right sentenceAlias) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceAlias
                verifyHelpers
                declaredSortVariables
        (Left err, Left _) -> Left err
        (Right _, Right _) -> error
            "The (Right, Right) match should be caught by the unique names check."
  where
    applicationId = symbolOrAliasConstructor symbolOrAlias
    symbolLookup = verifyHelpersLookupSymbolDeclaration verifyHelpers
    maybeSentenceSymbol = symbolLookup applicationId
    aliasLookup = verifyHelpersLookupAliasDeclaration verifyHelpers
    maybeSentenceAlias = aliasLookup applicationId

applicationSortsFromSymbolOrAliasSentence
    :: (MetaOrObject level, SentenceSymbolOrAlias sa)
    => SymbolOrAlias level
    -> sa level pat variable
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) (ApplicationSorts level)
applicationSortsFromSymbolOrAliasSentence
    symbolOrAlias sentence verifyHelpers declaredSortVariables
  = do
    mapM_
        ( verifySort
            (verifyHelpersFindSort verifyHelpers)
            declaredSortVariables
        )
        (symbolOrAliasParams symbolOrAlias)
    symbolOrAliasSorts (symbolOrAliasParams symbolOrAlias) sentence

verifySameSort
    :: Unified Sort
    -> Unified Sort
    -> Either (Error VerifyError) VerifySuccess
verifySameSort (UnifiedObject expectedSort) (UnifiedObject actualSort) = do
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedMeta actualSort) = do
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedObject actualSort) = do
    koreFailWithLocationsWhen
        (expectedSort /= patternMetaSort)
        [asUnified expectedSort, asUnified actualSort]
        (   "Expecting meta sort '"
            ++ unparseToString expectedSort
            ++ "' but got object sort '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedObject expectedSort) (UnifiedMeta actualSort) = do
    koreFailWithLocationsWhen
        (actualSort /= patternMetaSort)
        [asUnified expectedSort, asUnified actualSort]
        (   "Expecting object sort '"
            ++ unparseToString expectedSort
            ++ "' but got meta sort '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess

verifyFreeVariables
    :: CommonKorePattern -> Either (Error VerifyError) DeclaredVariables
verifyFreeVariables unifiedPattern =
    foldM
        addFreeVariable
        emptyDeclaredVariables
        (Set.toList (freeVariables unifiedPattern))

addFreeVariable
    :: DeclaredVariables
    -> Unified Variable
    -> Either (Error VerifyError) DeclaredVariables
addFreeVariable
    vars @ DeclaredVariables { metaDeclaredVariables = metaVars }
    (UnifiedMeta v)
  = do
    checkVariable v metaVars
    return vars
        { metaDeclaredVariables = Map.insert (variableName v) v metaVars }
addFreeVariable
    vars @ DeclaredVariables { objectDeclaredVariables = objectVars }
    (UnifiedObject v)
  = do
    checkVariable v objectVars
    return vars
        { objectDeclaredVariables = Map.insert (variableName v) v objectVars }

checkVariable
    :: Variable a
    -> Map.Map (Id a) (Variable a)
    -> Either (Error VerifyError) VerifySuccess
checkVariable var vars =
    case Map.lookup (variableName var) vars of
        Nothing -> verifySuccess
        Just v ->
            koreFailWithLocations
                [v, var]
                ("Inconsistent free variable usage: "
                ++ unparseToString v
                ++ " and "
                ++ unparseToString var
                ++ "."
                )

patternNameForContext :: Pattern level Variable p -> String
patternNameForContext (AndPattern _) = "\\and"
patternNameForContext (ApplicationPattern application) =
    "symbol or alias '"
    ++ getId (symbolOrAliasConstructor (applicationSymbolOrAlias application))
    ++ "'"
patternNameForContext (BottomPattern _) = "\\bottom"
patternNameForContext (CeilPattern _) = "\\ceil"
patternNameForContext (DomainValuePattern _) = "\\dv"
patternNameForContext (EqualsPattern _) = "\\equals"
patternNameForContext (ExistsPattern exists) =
    "\\exists '"
    ++ variableNameForContext (existsVariable exists)
    ++ "'"
patternNameForContext (FloorPattern _) = "\\floor"
patternNameForContext (ForallPattern forall) =
    "\\forall '"
    ++ variableNameForContext (forallVariable forall)
    ++ "'"
patternNameForContext (IffPattern _) = "\\iff"
patternNameForContext (ImpliesPattern _) = "\\implies"
patternNameForContext (InPattern _) = "\\in"
patternNameForContext (NextPattern _) = "\\next"
patternNameForContext (NotPattern _) = "\\not"
patternNameForContext (OrPattern _) = "\\or"
patternNameForContext (RewritesPattern _) = "\\rewrites"
patternNameForContext (StringLiteralPattern _) = "<string>"
patternNameForContext (CharLiteralPattern _) = "<char>"
patternNameForContext (TopPattern _) = "\\top"
patternNameForContext (VariablePattern variable) =
    "variable '" ++ variableNameForContext variable ++ "'"

variableNameForContext :: Variable level -> String
variableNameForContext variable = getId (variableName variable)
