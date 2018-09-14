{-|
Module      : Kore.ASTVerifier.PatternVerifier
Description : Tools for verifying the wellformedness of a Kore 'Pattern'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.PatternVerifier
    ( verifyPattern
    , verifyAliasLeftPattern
    , verifyStandalonePattern
    ) where

import           Control.Monad
                 ( foldM, zipWithM_ )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( (<+>) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc.Render.String
                 ( renderString )

import           Kore.AST.Common
import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.MLPatterns
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.AST.Sentence
import           Kore.ASTHelpers
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Unparser
import           Kore.Variables.Free
                 ( freeVariables )

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

metaVerifyHelpers
    :: KoreIndexedModule atts -> DeclaredVariables -> VerifyHelpers Meta
metaVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort =
            fmap getIndexedSentence . resolveSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            fmap getIndexedSentence . resolveAlias indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            fmap getIndexedSentence . resolveSymbol indexedModule
        , verifyHelpersFindDeclaredVariables =
            flip Map.lookup (metaDeclaredVariables declaredVariables)
        }

objectVerifyHelpers
    :: KoreIndexedModule atts -> DeclaredVariables -> VerifyHelpers Object
objectVerifyHelpers indexedModule declaredVariables =
    VerifyHelpers
        { verifyHelpersFindSort =
            fmap getIndexedSentence . resolveSort indexedModule
        , verifyHelpersLookupAliasDeclaration =
            fmap getIndexedSentence . resolveAlias indexedModule
        , verifyHelpersLookupSymbolDeclaration =
            fmap getIndexedSentence . resolveSymbol indexedModule
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
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables which are visible in this pattern.
    -> Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
verifyAliasLeftPattern = verifyPattern
    -- TODO: check that the left pattern is the alias symbol applied to
    -- non-repeating variables

verifyStandalonePattern
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
verifyStandalonePattern builtinVerifier indexedModule =
    verifyPattern builtinVerifier indexedModule Set.empty Nothing

{-|'verifyPattern' verifies the welformedness of a Kore 'CommonKorePattern'. -}
verifyPattern
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables which are visible in this pattern.
    -> Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
verifyPattern
    builtinVerifier
    indexedModule
    sortVariables
    maybeExpectedSort
    unifiedPattern
  = do
    freeVariables1 <- verifyFreeVariables unifiedPattern
    internalVerifyPattern
        builtinVerifier
        indexedModule
        sortVariables
        freeVariables1
        maybeExpectedSort
        unifiedPattern

internalVerifyPattern
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Maybe UnifiedSort
    -> CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
internalVerifyPattern
    builtinVerifier
    indexedModule
    sortParamsSet
    declaredVariables
    mUnifiedSort
  =
    applyKorePattern
        (internalVerifyMetaPattern
            builtinVerifier
            indexedModule
            sortParamsSet
            declaredVariables
            mUnifiedSort
        )
        (internalVerifyObjectPattern
            builtinVerifier
            indexedModule
            sortParamsSet
            declaredVariables
            mUnifiedSort
        )

internalVerifyMetaPattern
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Maybe UnifiedSort
    -> Pattern Meta Variable CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
internalVerifyMetaPattern
    builtinVerifier
    indexedModule
    sortVariables
    declaredVariables
    maybeExpectedSort
    p
  =
    withLocationAndContext p (patternNameForContext p) (do
        sort <-
            verifyParameterizedPattern
                p
                builtinVerifier
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
    :: Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Maybe UnifiedSort
    -> Pattern Object Variable CommonKorePattern
    -> Either (Error VerifyError) VerifySuccess
internalVerifyObjectPattern
    builtinVerifier
    indexedModule
    sortVariables
    declaredVariables
    maybeExpectedSort
    p
  =
    withLocationAndContext p (patternNameForContext p)
    (do
        Builtin.runPatternVerifier builtinVerifier findSort p
        sort <- verifyParameterizedPattern
                    p
                    builtinVerifier
                    indexedModule
                    verifyHelpers
                    sortVariables
                    declaredVariables
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort expectedSort (UnifiedObject sort)
            Nothing ->
                verifySuccess
    )
  where
    findSort = fmap getIndexedSentence . resolveSort indexedModule
    verifyHelpers = objectVerifyHelpers indexedModule declaredVariables

newtype SortOrError level =
    SortOrError { getSortOrError :: Either (Error VerifyError) (Sort level) }

verifyParameterizedPattern
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyParameterizedPattern pat builtinVerifier indexedModule helpers sortParams vars =
    getSortOrError
    $ applyPatternLeveledFunction
        PatternLeveledFunction
            { patternLeveledFunctionML = \p -> SortOrError $
                verifyMLPattern p builtinVerifier indexedModule helpers sortParams vars
            , patternLeveledFunctionMLBinder = \p -> SortOrError $
                verifyBinder p builtinVerifier indexedModule helpers sortParams vars
            , stringLeveledFunction = const (SortOrError verifyStringPattern)
            , charLeveledFunction = const (SortOrError verifyCharPattern)
            , applicationLeveledFunction = \p -> SortOrError $
                verifyApplication p builtinVerifier indexedModule helpers sortParams vars
            , variableLeveledFunction = \p -> SortOrError $
                verifyVariableUsage p indexedModule helpers sortParams vars
            , domainValueLeveledFunction = \dv -> SortOrError $
                verifyDomainValue dv helpers sortParams

            }
        pat

verifyMLPattern
    :: (MLPatternClass p level, MetaOrObject level)
    => p level CommonKorePattern
    -> Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyMLPattern
    mlPattern
    builtinVerifier
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
        builtinVerifier
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
    -> Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) VerifySuccess
verifyPatternsWithSorts
    sorts
    operands
    builtinVerifier
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
        (\sort ->
            internalVerifyPattern
                builtinVerifier
                indexedModule
                declaredSortVariables
                declaredVariables
                (Just sort)
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
    -> Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyApplication
    application
    builtinVerifier
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
        builtinVerifier
        indexedModule
        declaredSortVariables
        declaredVariables
    return (applicationSortsResult applicationSorts)

verifyBinder
    :: (MLBinderPatternClass p, MetaOrObject level)
    => p level Variable CommonKorePattern
    -> Builtin.PatternVerifier
    -> KoreIndexedModule atts
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> DeclaredVariables
    -> Either (Error VerifyError) (Sort level)
verifyBinder
    binder
    builtinVerifier
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
        builtinVerifier
        indexedModule
        declaredSortVariables
        (addDeclaredVariable (asUnified quantifiedVariable) declaredVariables)
        (Just (asUnified binderSort))
        (getBinderPatternChild binder)
    return binderSort
  where
    quantifiedVariable = getBinderPatternVariable binder
    binderSort = getBinderPatternSort binder

verifyVariableUsage
    :: (MetaOrObject level)
    => Variable level
    -> KoreIndexedModule atts
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

verifyDomainValue
    :: (MetaOrObject level)
    => DomainValue Object (CommonPurePattern Meta)
    -> VerifyHelpers level
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) (Sort Object)
verifyDomainValue
    DomainValue
        { domainValueSort
        , domainValueChild
        }
    verifyHelpers
    declaredSortVariables
  =
    case isMetaOrObject verifyHelpers of
        IsMeta -> error "Domain Values are object-only. Should not happen."
        IsObject -> do
            verifySort
                (verifyHelpersFindSort verifyHelpers)
                declaredSortVariables
                domainValueSort
            case domainValueChild of
                BuiltinDomainPattern (StringLiteral_ _) -> return ()
                _ -> koreFail "Domain value argument must be a literal string."
            return domainValueSort

verifyStringPattern :: Either (Error VerifyError) (Sort Meta)
verifyStringPattern = Right charListMetaSort

verifyCharPattern :: Either (Error VerifyError) (Sort Meta)
verifyCharPattern = Right charMetaSort

verifyVariableDeclaration
    :: MetaOrObject level
    => Variable level
    -> KoreIndexedModule atts
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) VerifySuccess
verifyVariableDeclaration
    variable indexedModule declaredSortVariables
  = verifyVariableDeclarationUsing
        declaredSortVariables
        (fmap getIndexedSentence . resolveSort indexedModule)
        variable

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
        ((renderString . Pretty.layoutCompact)
         ("Expecting sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedMeta actualSort) = do
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
        ((renderString . Pretty.layoutCompact)
         ("Expecting sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
        )
    verifySuccess
verifySameSort (UnifiedMeta expectedSort) (UnifiedObject actualSort) = do
    koreFailWithLocationsWhen
        (expectedSort /= patternMetaSort)
        [asUnified expectedSort, asUnified actualSort]
        ((renderString . Pretty.layoutCompact)
         ("Expecting meta sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got object sort"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
        )
    verifySuccess
verifySameSort (UnifiedObject expectedSort) (UnifiedMeta actualSort) = do
    koreFailWithLocationsWhen
        (actualSort /= patternMetaSort)
        [asUnified expectedSort, asUnified actualSort]
        ((renderString . Pretty.layoutCompact)
         ("Expecting object sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got meta sort"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
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
    vars@DeclaredVariables { metaDeclaredVariables = metaVars }
    (UnifiedMeta v)
  = do
    checkVariable v metaVars
    return vars
        { metaDeclaredVariables = Map.insert (variableName v) v metaVars }
addFreeVariable
    vars@DeclaredVariables { objectDeclaredVariables = objectVars }
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
                ( (renderString . Pretty.layoutCompact)
                  ("Inconsistent free variable usage:"
                     <+> unparse v
                     <+> "and"
                     <+> unparse var
                     <> Pretty.dot
                  )
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
