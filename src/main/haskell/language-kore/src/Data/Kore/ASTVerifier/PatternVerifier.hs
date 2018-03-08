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

import           Data.Kore.AST
import           Data.Kore.ASTHelpers
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.Resolvers
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Kore.ImplicitDefinitions
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.Unparser.Unparse

import           Control.Monad                         (zipWithM_)
import qualified Data.Map                              as Map
import qualified Data.Set                              as Set
import           Data.Typeable                         (Typeable)

data DeclaredVariables = DeclaredVariables
    { objectDeclaredVariables :: !(Map.Map (Id Object) (Variable Object))
    , metaDeclaredVariables   :: !(Map.Map (Id Meta) (Variable Meta))
    }

emptyDeclaredVariables :: DeclaredVariables
emptyDeclaredVariables = DeclaredVariables
    { objectDeclaredVariables = Map.empty
    , metaDeclaredVariables = Map.empty
    }

data VerifyHelpers a = VerifyHelpers
    { verifyHelpersFindSort
        :: !(Id a -> Either (Error VerifyError) (SortDescription a))
    , verifyHelpersLookupAliasDeclaration
        :: !(Id a -> Maybe (SentenceAlias a))
    , verifyHelpersLookupSymbolDeclaration
        :: !(Id a -> Maybe (SentenceSymbol a))
    , verifyHelpersFindDeclaredVariables
        :: !(Id a -> Maybe (Variable a))
    }

metaVerifyHelpers :: IndexedModule -> DeclaredVariables -> VerifyHelpers Meta
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
    :: IndexedModule -> DeclaredVariables -> VerifyHelpers Object
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
    :: UnifiedVariable Variable -> DeclaredVariables -> DeclaredVariables
addDeclaredVariable
    (MetaVariable variable)
    variables@DeclaredVariables{ metaDeclaredVariables = variablesDict }
  =
    variables
        { metaDeclaredVariables =
            Map.insert (variableName variable) variable variablesDict
        }
addDeclaredVariable
    (ObjectVariable variable)
    variables@DeclaredVariables{ objectDeclaredVariables = variablesDict }
  =
    variables
        { objectDeclaredVariables =
            Map.insert (variableName variable) variable variablesDict
        }

{-|'verifyPattern' verifies the welformedness of a Kore 'UnifiedPattern'. -}
verifyPattern
    :: UnifiedPattern
    -> Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> IndexedModule
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables which are visible in this pattern.
    -> Either (Error VerifyError) VerifySuccess
verifyPattern unifiedPattern maybeExpectedSort indexedModule sortVariables =
    internalVerifyPattern
        unifiedPattern
        maybeExpectedSort
        indexedModule
        sortVariables
        emptyDeclaredVariables

internalVerifyPattern
    :: UnifiedPattern
    -> Maybe UnifiedSort
    -> IndexedModule
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) VerifySuccess
internalVerifyPattern
    (MetaPattern p@(StringLiteralPattern _))
    maybeExpectedSort
    _ _ _
  =
    withContext (patternNameForContext p) (do
        sort <- verifyStringPattern
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort
                    expectedSort
                    (MetaSort sort)
            Nothing ->
                verifySuccess
    )
internalVerifyPattern
    (MetaPattern p@(CharLiteralPattern _))
    maybeExpectedSort
    _ _ _
  =
    withContext (patternNameForContext p) (do
        sort <- verifyCharPattern
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort expectedSort (MetaSort sort)
            Nothing ->
                verifySuccess
    )
internalVerifyPattern
    (MetaPattern p)
    maybeExpectedSort
    indexedModule
    sortVariables
    declaredVariables
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
                    (MetaSort sort)
            Nothing ->
                verifySuccess
    )
internalVerifyPattern
    (ObjectPattern p)
    maybeExpectedSort
    indexedModule
    sortVariables
    declaredVariables
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
                    (ObjectSort sort)
            Nothing ->
                verifySuccess
    )
  where
    verifyHelpers = objectVerifyHelpers indexedModule declaredVariables

verifyParametrizedPattern
    :: IsMeta a
    => Pattern a Variable UnifiedPattern
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort a)
verifyParametrizedPattern (AndPattern p)         = verifyMLPattern p
verifyParametrizedPattern (ApplicationPattern p) = verifyApplication p
verifyParametrizedPattern (BottomPattern p)      = verifyMLPattern p
verifyParametrizedPattern (CeilPattern p)        = verifyMLPattern p
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
    :: Pattern Object v UnifiedPattern
    -> IndexedModule
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
    :: (MLPatternClass p, IsMeta a)
    => p a UnifiedPattern
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Maybe (Sort a))
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
    :: (MLPatternClass p, IsMeta a)
    => p a UnifiedPattern
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort a)
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
    :: IsMeta a
    => [Sort a]
    -> [UnifiedPattern]
    -> IndexedModule
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
                (Just (asUnified sort))
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
    :: IsMeta a
    => Application a UnifiedPattern
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort a)
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
        (applicationSortsOperands applicationSorts)
        (applicationChildren application)
        indexedModule
        declaredSortVariables
        declaredVariables
    return (applicationSortsResult applicationSorts)

verifyBinder
    :: (MLBinderPatternClass p, IsMeta a)
    => p a Variable UnifiedPattern
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort a)
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
    :: (Ord a, Typeable a)
    => Variable a
    -> IndexedModule
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort a)
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
    :: IsMeta a
    => Variable a
    -> IndexedModule
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) VerifySuccess
verifyVariableDeclaration
    variable indexedModule declaredSortVariables
  =
    applyMetaObjectFunction
        variable
        (verifyUsing (resolveObjectSort indexedModule))
        (verifyUsing (resolveMetaSort indexedModule))
  where
    verifyUsing f v = verifySort f
        declaredSortVariables
        (variableSort v)

findVariableDeclaration
    :: (Ord a, Typeable a)
    => Id a
    -> VerifyHelpers a
    -> Either (Error VerifyError) (Variable a)
findVariableDeclaration variableId verifyHelpers =
    case findVariables variableId of
        Nothing ->
            koreFail ("Unquantified variable: '" ++ getId variableId ++ "'.")
        Just variable -> Right variable
  where
    findVariables = verifyHelpersFindDeclaredVariables verifyHelpers

verifySymbolOrAlias
    :: IsMeta a
    => SymbolOrAlias a
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) (ApplicationSorts a)
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
    :: (IsMeta a, SentenceSymbolOrAlias sa)
    => SymbolOrAlias a
    -> sa a
    -> VerifyHelpers a
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) (ApplicationSorts a)
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
    :: UnifiedSort
    -> UnifiedSort
    -> Either (Error VerifyError) VerifySuccess
verifySameSort (ObjectSort expectedSort) (ObjectSort actualSort) = do
    koreFailWhen
        (expectedSort /= actualSort)
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (MetaSort expectedSort) (MetaSort actualSort) = do
    koreFailWhen
        (expectedSort /= actualSort)
        (   "Expecting sort '"
            ++ unparseToString expectedSort
            ++ "' but got '"
            ++ unparseToString actualSort
            ++ "'."
        )
    verifySuccess
verifySameSort (MetaSort expectedSort) (ObjectSort actualSort) =
    koreFail
        (   "Expecting meta sort '"
            ++ unparseToString expectedSort
            ++ "' but got object sort '"
            ++ unparseToString actualSort
            ++ "'."
        )
verifySameSort (ObjectSort expectedSort) (MetaSort actualSort) =
    koreFail
        (   "Expecting object sort '"
            ++ unparseToString expectedSort
            ++ "' but got meta sort '"
            ++ unparseToString actualSort
            ++ "'."
        )

patternNameForContext :: Pattern a Variable p -> String
patternNameForContext (AndPattern _) = "\\and"
patternNameForContext (ApplicationPattern application) =
    "symbol or alias '"
    ++ getId (symbolOrAliasConstructor (applicationSymbolOrAlias application))
    ++ "'"
patternNameForContext (BottomPattern _) = "\\bottom"
patternNameForContext (CeilPattern _) = "\\ceil"
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

variableNameForContext :: Variable a -> String
variableNameForContext variable = getId (variableName variable)
