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
    , PatternVerifier (..)
    , runPatternVerifier
    , Context (..)
    , DeclaredVariables (..), emptyDeclaredVariables
    ) where

import           Control.Monad
                 ( foldM, zipWithM_ )
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( (<+>) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc.Render.String
                 ( renderString )

import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.MLPatterns
import           Kore.AST.Sentence
import           Kore.ASTHelpers
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
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

data Context =
    Context
        { declaredVariables :: !DeclaredVariables
        , declaredSortVariables :: !(Set UnifiedSortVariable)
        -- ^ The sort variables in scope.
        , indexedModule :: !(KoreIndexedModule Attribute.Null)
        -- ^ The indexed Kore module containing all definitions in scope.
        , builtinPatternVerifier :: !Builtin.PatternVerifier
        }

newtype PatternVerifier a =
    PatternVerifier
        { getPatternVerifier :: ReaderT Context (Either (Error VerifyError)) a }
    deriving (Applicative, Functor, Monad)

deriving instance MonadReader Context PatternVerifier

deriving instance e ~ VerifyError => MonadError (Error e) PatternVerifier

runPatternVerifier
    :: Context
    -> PatternVerifier a
    -> Either (Error VerifyError) a
runPatternVerifier ctx PatternVerifier { getPatternVerifier } =
    runReaderT getPatternVerifier ctx

lookupSortDeclaration
    :: MetaOrObject level
    => Id level
    -> PatternVerifier (KoreSentenceSort level)
lookupSortDeclaration sortId = do
    Context { indexedModule } <- Reader.ask
    (_, sortDecl) <- resolveSort indexedModule sortId
    return sortDecl

lookupAliasDeclaration
    :: MetaOrObject level
    => Id level
    -> PatternVerifier (KoreSentenceAlias level)
lookupAliasDeclaration aliasId = do
    Context { indexedModule } <- Reader.ask
    (_, aliasDecl) <- resolveAlias indexedModule aliasId
    return aliasDecl

lookupSymbolDeclaration
    :: MetaOrObject level
    => Id level
    -> PatternVerifier (KoreSentenceSymbol level)
lookupSymbolDeclaration symbolId = do
    Context { indexedModule } <- Reader.ask
    (_, symbolDecl) <- resolveSymbol indexedModule symbolId
    return symbolDecl

lookupDeclaredVariable
    :: MetaOrObject level
    => Id level
    -> PatternVerifier (Variable level)
lookupDeclaredVariable varId = do
    Context { declaredVariables } <- Reader.ask
    case isMetaOrObject varId of
        IsMeta ->
            maybe errorUnquantified return
                $ Map.lookup varId metaDeclaredVariables
          where
            DeclaredVariables { metaDeclaredVariables } = declaredVariables
        IsObject ->
            maybe errorUnquantified return
                $ Map.lookup varId objectDeclaredVariables
          where
            DeclaredVariables { objectDeclaredVariables } = declaredVariables
  where
    errorUnquantified :: PatternVerifier (Variable level)
    errorUnquantified =
        koreFailWithLocations [varId]
            ("Unquantified variable: '" ++ getIdForError varId ++ "'.")

addDeclaredVariable
    :: MetaOrObject level
    => Variable level
    -> DeclaredVariables
    -> DeclaredVariables
addDeclaredVariable variable@Variable { variableName } =
    case isMetaOrObject variable of
        IsMeta ->
            \declared@DeclaredVariables { metaDeclaredVariables } ->
                declared
                    { metaDeclaredVariables =
                        Map.insert variableName variable metaDeclaredVariables
                    }
        IsObject ->
            \declared@DeclaredVariables { objectDeclaredVariables } ->
                declared
                    { objectDeclaredVariables =
                        Map.insert variableName variable objectDeclaredVariables
                    }

verifyAliasLeftPattern
    :: Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> PatternVerifier VerifySuccess
verifyAliasLeftPattern = verifyPattern
    -- TODO: check that the left pattern is the alias symbol applied to
    -- non-repeating variables

{-|'verifyPattern' verifies the welformedness of a Kore 'CommonKorePattern'. -}
verifyPattern
    :: Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> PatternVerifier VerifySuccess
verifyPattern maybeExpectedSort korePattern = do
    freeVariables1 <- verifyFreeVariables korePattern
    Reader.local
        (withFreeVariables freeVariables1)
        (internalVerifyPattern maybeExpectedSort korePattern)
  where
    withFreeVariables declaredVariables ctx@Context { } =
        ctx { declaredVariables }

internalVerifyPattern
    :: Maybe UnifiedSort
    -> CommonKorePattern
    -> PatternVerifier VerifySuccess
internalVerifyPattern mUnifiedSort (Recursive.project -> _ :< upat) =
    case upat of
        UnifiedMetaPattern mpat ->
            internalVerifyMetaPattern mUnifiedSort mpat
        UnifiedObjectPattern opat ->
            internalVerifyObjectPattern mUnifiedSort opat

internalVerifyMetaPattern
    :: Maybe UnifiedSort
    -> Pattern Meta Domain.Builtin Variable CommonKorePattern
    -> PatternVerifier VerifySuccess
internalVerifyMetaPattern maybeExpectedSort p =
    withLocationAndContext p (patternNameForContext p) (do
        sort <- verifyParameterizedPattern p
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort
                    expectedSort
                    (UnifiedMeta sort)
            Nothing ->
                verifySuccess
    )

verifyBuiltinPattern
    :: Pattern Object Domain.Builtin Variable CommonKorePattern
    -> PatternVerifier ()
verifyBuiltinPattern pat = do
    Context { builtinPatternVerifier } <- Reader.ask
    Builtin.runPatternVerifier builtinPatternVerifier lookupSortDeclaration pat

internalVerifyObjectPattern
    :: Maybe UnifiedSort
    -> Pattern Object Domain.Builtin Variable CommonKorePattern
    -> PatternVerifier VerifySuccess
internalVerifyObjectPattern maybeExpectedSort p =
    withLocationAndContext p (patternNameForContext p)
    (do
        verifyBuiltinPattern p
        sort <- verifyParameterizedPattern p
        case maybeExpectedSort of
            Just expectedSort ->
                verifySameSort expectedSort (UnifiedObject sort)
            Nothing ->
                verifySuccess
    )

newtype SortOrError level =
    SortOrError { getSortOrError :: PatternVerifier (Sort level) }

verifyParameterizedPattern
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable CommonKorePattern
    -> PatternVerifier (Sort level)
verifyParameterizedPattern pat =
    getSortOrError $ applyPatternLeveledFunction
        PatternLeveledFunction
            { patternLeveledFunctionML =
                \p -> SortOrError $ verifyMLPattern p
            , patternLeveledFunctionMLBinder =
                \p -> SortOrError $ verifyBinder p
            , stringLeveledFunction = const (SortOrError verifyStringPattern)
            , charLeveledFunction = const (SortOrError verifyCharPattern)
            , applicationLeveledFunction =
                \p -> SortOrError $ verifyApplication p
            , variableLeveledFunction =
                \p -> SortOrError $ verifyVariableUsage p
            , domainValueLeveledFunction =
                \dv -> SortOrError $ verifyDomainValue dv

            }
        pat

verifyMLPattern
    :: (MLPatternClass p level, MetaOrObject level)
    => p level CommonKorePattern
    -> PatternVerifier (Sort level)
verifyMLPattern mlPattern = do
    Context { declaredSortVariables } <- Reader.ask
    mapM_
        (verifySort
            lookupSortDeclaration
            declaredSortVariables
        )
        (getPatternSorts mlPattern)
    verifyPatternsWithSorts
        operandSorts
        (getPatternChildren mlPattern)
    return returnSort
  where
    returnSort = getMLPatternResultSort mlPattern
    operandSorts = getMLPatternOperandSorts mlPattern


verifyPatternsWithSorts
    :: [UnifiedSort]
    -> [CommonKorePattern]
    -> PatternVerifier VerifySuccess
verifyPatternsWithSorts sorts operands = do
    koreFailWhen (declaredOperandCount /= actualOperandCount)
        (  "Expected "
        ++ show declaredOperandCount
        ++ " operands, but got "
        ++ show actualOperandCount
        ++ "."
        )
    zipWithM_
        (\sort -> internalVerifyPattern (Just sort))
        sorts
        operands
    verifySuccess
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplication
    :: MetaOrObject level
    => Application level CommonKorePattern
    -> PatternVerifier (Sort level)
verifyApplication application = do
    applicationSorts <-
        verifySymbolOrAlias
            (applicationSymbolOrAlias application)
    verifyPatternsWithSorts
        (map asUnified (applicationSortsOperands applicationSorts))
        (applicationChildren application)
    return (applicationSortsResult applicationSorts)

verifyBinder
    :: (MLBinderPatternClass p, MetaOrObject level)
    => p level Variable CommonKorePattern
    -> PatternVerifier (Sort level)
verifyBinder binder = do
    verifyVariableDeclaration quantifiedVariable
    Context { declaredSortVariables } <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        binderSort
    Reader.local withQuantifiedVariable
        (internalVerifyPattern
            (Just (asUnified binderSort))
            (getBinderPatternChild binder)
        )
    return binderSort
  where
    quantifiedVariable = getBinderPatternVariable binder
    binderSort = getBinderPatternSort binder
    withQuantifiedVariable ctx@Context { declaredVariables } =
        ctx
            { declaredVariables =
                addDeclaredVariable
                    quantifiedVariable
                    declaredVariables
            }

verifyVariableUsage
    :: (MetaOrObject level)
    => Variable level
    -> PatternVerifier (Sort level)
verifyVariableUsage variable = do
    declaredVariable <- lookupDeclaredVariable (variableName variable)
    koreFailWithLocationsWhen
        (variableSort variable /= variableSort declaredVariable)
        [ variable, declaredVariable ]
        "The declared sort is different."
    return (variableSort variable)

verifyDomainValue
    :: DomainValue Object Domain.Builtin CommonKorePattern
    -> PatternVerifier (Sort Object)
verifyDomainValue DomainValue { domainValueSort, domainValueChild } = do
    Context { declaredSortVariables } <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        domainValueSort
    case domainValueChild of
        Domain.BuiltinPattern (StringLiteral_ _) -> return ()
        _ -> koreFail "Domain value argument must be a literal string."
    return domainValueSort

verifyStringPattern :: PatternVerifier (Sort Meta)
verifyStringPattern = return charListMetaSort

verifyCharPattern :: PatternVerifier (Sort Meta)
verifyCharPattern = return charMetaSort

verifyVariableDeclaration
    :: MetaOrObject level
    => Variable level
    -> PatternVerifier VerifySuccess
verifyVariableDeclaration Variable { variableSort } = do
    Context { declaredSortVariables } <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        variableSort

verifySymbolOrAlias
    :: MetaOrObject level
    => SymbolOrAlias level
    -> PatternVerifier (ApplicationSorts level)
verifySymbolOrAlias symbolOrAlias = do
    trySymbol <- catchError (Right <$> lookupSymbol) (return . Left)
    tryAlias <- catchError (Right <$> lookupAlias) (return . Left)
    case (trySymbol, tryAlias) of
        (Right sentenceSymbol, Left _) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceSymbol
        (Left _, Right sentenceAlias) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceAlias
        (Left err, Left _) -> throwError err
        (Right _, Right _) -> error
            "The (Right, Right) match should be caught by the unique names check."
  where
    lookupSymbol = lookupSymbolDeclaration applicationId
    lookupAlias = lookupAliasDeclaration applicationId
    applicationId = symbolOrAliasConstructor symbolOrAlias

applicationSortsFromSymbolOrAliasSentence
    :: (MetaOrObject level, SentenceSymbolOrAlias sa)
    => SymbolOrAlias level
    -> sa level pat dom variable
    -> PatternVerifier (ApplicationSorts level)
applicationSortsFromSymbolOrAliasSentence symbolOrAlias sentence = do
    Context { declaredSortVariables } <- Reader.ask
    mapM_
        ( verifySort
            lookupSortDeclaration
            declaredSortVariables
        )
        (symbolOrAliasParams symbolOrAlias)
    symbolOrAliasSorts (symbolOrAliasParams symbolOrAlias) sentence

verifySameSort
    :: Unified Sort
    -> Unified Sort
    -> PatternVerifier VerifySuccess
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
    :: CommonKorePattern
    -> PatternVerifier DeclaredVariables
verifyFreeVariables unifiedPattern =
    foldM
        addFreeVariable
        emptyDeclaredVariables
        (Set.toList (freeVariables unifiedPattern))

addFreeVariable
    :: DeclaredVariables
    -> Unified Variable
    -> PatternVerifier DeclaredVariables
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
    -> PatternVerifier VerifySuccess
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

patternNameForContext :: Pattern level dom Variable p -> String
patternNameForContext (AndPattern _) = "\\and"
patternNameForContext (ApplicationPattern application) =
    "symbol or alias '"
    ++ getIdForError
        (symbolOrAliasConstructor (applicationSymbolOrAlias application))
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
variableNameForContext variable = getIdForError (variableName variable)
