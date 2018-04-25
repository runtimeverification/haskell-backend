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
module Data.Kore.ASTVerifier.PatternVerifier (verifyPattern) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.ASTHelpers
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.Resolvers
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.IndexedModule.IndexedModule
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
        :: !(Id level -> Maybe (KoreSentenceAlias level))
    , verifyHelpersLookupSymbolDeclaration
        :: !(Id level -> Maybe (KoreSentenceSymbol level))
    , verifyHelpersFindDeclaredVariables
        :: !(Id level -> Maybe (Variable level))
    }

metaVerifyHelpers :: KoreIndexedModule -> DeclaredVariables -> VerifyHelpers Meta
metaVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort = resolveMetaSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            resolveThing indexedModuleMetaAliasSentences indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            resolveThing indexedModuleMetaSymbolSentences indexedModule
        , verifyHelpersFindDeclaredVariables =
            flip Map.lookup (metaDeclaredVariables declaredVariables)
        }

objectVerifyHelpers
    :: KoreIndexedModule -> DeclaredVariables -> VerifyHelpers Object
objectVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort = resolveObjectSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            resolveThing indexedModuleObjectAliasSentences indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            resolveThing indexedModuleObjectSymbolSentences indexedModule
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
internalVerifyPattern korePattern a b c d =
    applyKorePattern
        (internalVerifyMetaPattern a b c d)
        (internalVerifyObjectPattern a b c d)
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
    _ _ _
    p@(StringLiteralPattern _)
  =
    withContext (patternNameForContext p) (do
        sort <- verifyStringPattern
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort
                    expectedSort
                    (UnifiedMeta sort)
            Nothing ->
                verifySuccess
    )
internalVerifyMetaPattern
    maybeExpectedSort
    _ _ _
    p@(CharLiteralPattern _)
  =
    withContext (patternNameForContext p) (do
        sort <- verifyCharPattern
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort expectedSort (UnifiedMeta sort)
            Nothing ->
                verifySuccess
    )
internalVerifyMetaPattern
    maybeExpectedSort
    indexedModule
    sortVariables
    declaredVariables
    p
  =
    withContext (patternNameForContext p) (do
        sort <-
            verifyParametrizedPattern
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
    withContext (patternNameForContext p) (do
        maybeSort <-
            verifyObjectPattern
                p indexedModule verifyHelpers sortVariables declaredVariables
        sort <-
            case maybeSort of
                Just s -> return s
                Nothing ->
                    verifyParametrizedPattern
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

verifyParametrizedPattern
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyParametrizedPattern (AndPattern p)         = verifyMLPattern p
verifyParametrizedPattern (ApplicationPattern p) = verifyApplication p
verifyParametrizedPattern (BottomPattern p)      = verifyMLPattern p
verifyParametrizedPattern (CeilPattern p)        = verifyMLPattern p
verifyParametrizedPattern (DomainValuePattern p) = verifyMLPattern p
verifyParametrizedPattern (EqualsPattern p)      = verifyMLPattern p
verifyParametrizedPattern (ExistsPattern p)      = verifyBinder p
verifyParametrizedPattern (FloorPattern p)       = verifyMLPattern p
verifyParametrizedPattern (ForallPattern p)      = verifyBinder p
verifyParametrizedPattern (IffPattern p)         = verifyMLPattern p
verifyParametrizedPattern (ImpliesPattern p)     = verifyMLPattern p
verifyParametrizedPattern (InPattern p)          = verifyMLPattern p
verifyParametrizedPattern (NotPattern p)         = verifyMLPattern p
verifyParametrizedPattern (OrPattern p)          = verifyMLPattern p
verifyParametrizedPattern (TopPattern p)         = verifyMLPattern p
verifyParametrizedPattern (VariablePattern p)    = verifyVariableUsage p

verifyObjectPattern
    :: Pattern Object v CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers Object
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Maybe (Sort Object))
verifyObjectPattern (NextPattern p)     = maybeVerifyMLPattern p
verifyObjectPattern (RewritesPattern p) = maybeVerifyMLPattern p
verifyObjectPattern _                   = rightNothing
  where
    rightNothing _ _ _ _ = Right Nothing

maybeVerifyMLPattern
    :: (MLPatternClass p, MetaOrObject level)
    => p level CommonKorePattern
    -> KoreIndexedModule
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Maybe (Sort level))
maybeVerifyMLPattern
    mlPattern
    indexedModule
    verifyHelpers
    declaredSortVariables
    declaredVariables
  =
    Just <$>
        verifyMLPattern
            mlPattern
            indexedModule
            verifyHelpers
            declaredSortVariables
            declaredVariables

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
    koreFailWhen
        (variableSort variable /= variableSort declaredVariable)
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
  = case isMetaOrObject variable of
        IsObject ->
            verifyVariableDeclarationUsing
                declaredSortVariables (resolveObjectSort indexedModule) variable
        IsMeta ->
            verifyVariableDeclarationUsing
                declaredSortVariables (resolveMetaSort indexedModule) variable

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
            koreFail ("Unquantified variable: '" ++ getId variableId ++ "'.")
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
        (Just sentenceSymbol, Nothing) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceSymbol
                verifyHelpers
                declaredSortVariables
        (Nothing, Just sentenceAlias) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceAlias
                verifyHelpers
                declaredSortVariables
        (Nothing, Nothing) ->
            koreFail ("Symbol '" ++ getId applicationId ++ "' not defined.")
        -- The (Just, Just) match should be caught by the unique names check.
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
    koreFailWhen
        (expectedSort /= actualSort)
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedMeta actualSort) = do
    koreFailWhen
        (expectedSort /= actualSort)
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedObject actualSort) = do
    koreFailWhen
        (expectedSort /= patternMetaSort)
        (   "Expecting meta sort '"
            ++ unparseToString expectedSort
            ++ "' but got object sort '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (UnifiedObject expectedSort) (UnifiedMeta actualSort) = do
    koreFailWhen
        (actualSort /= patternMetaSort)
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
            koreFail
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
