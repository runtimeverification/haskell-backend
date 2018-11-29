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

import           Control.Comonad
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import           Data.Functor.Const
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
    -> PatternVerifier VerifiedKorePattern
verifyAliasLeftPattern = verifyPattern
    -- TODO: check that the left pattern is the alias symbol applied to
    -- non-repeating variables

{-|'verifyPattern' verifies the welformedness of a Kore 'CommonKorePattern'. -}
verifyPattern
    :: Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> PatternVerifier VerifiedKorePattern
verifyPattern maybeExpectedSort korePattern = do
    freeVariables1 <- verifyFreeVariables korePattern
    Reader.local
        (withFreeVariables freeVariables1)
        verifyPatternWorker
  where
    withFreeVariables declaredVariables ctx@Context { } =
        ctx { declaredVariables }
    verifyPatternWorker =
        Recursive.fold (verifyUnifiedPattern maybeExpectedSort) korePattern

verifyUnifiedPattern
    :: Maybe UnifiedSort
    -> Base CommonKorePattern (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier VerifiedKorePattern
verifyUnifiedPattern expectedSort (_ :< pat) =
    case pat of
        UnifiedMetaPattern mpat -> do
            valid :< vpat <- verifyMetaPattern mpat
            assertExpectedSort expectedSort valid
            return (Recursive.embed $ valid :< UnifiedMetaPattern vpat)
        UnifiedObjectPattern opat -> do
            valid :< vpat <- verifyObjectPattern opat
            assertExpectedSort expectedSort valid
            return (Recursive.embed $ valid :< UnifiedObjectPattern vpat)

verifyMetaPattern
    :: base ~ Pattern Meta Domain.Builtin Variable
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyMetaPattern pat =
    withLocationAndContext pat patternName $ do
        verifyPatternHead pat
  where
    patternName = patternNameForContext pat

verifyObjectPattern
    :: base ~ Pattern Object Domain.Builtin Variable
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyObjectPattern pat =
    withLocationAndContext pat patternName $ do
        -- Builtin domains only occur in object-level patterns.
        -- The builtin pattern verifiers only look at the pattern head,
        -- so we erase the child verifiers.
        verifyBuiltinPattern (mempty <$ pat)
        verifyPatternHead pat
  where
    patternName = patternNameForContext pat

verifyPatternHead
    :: (MetaOrObject level, base ~ Pattern level Domain.Builtin Variable)
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyPatternHead =
    \case
        AndPattern and' ->
            transCofreeF AndPattern <$> verifyAnd and'
        ApplicationPattern app ->
            transCofreeF ApplicationPattern <$> verifyApplication app
        BottomPattern bottom ->
            transCofreeF BottomPattern <$> verifyBottom bottom
        CeilPattern ceil' ->
            transCofreeF CeilPattern <$> verifyCeil ceil'
        DomainValuePattern dv ->
            transCofreeF DomainValuePattern <$> verifyDomainValue dv
        EqualsPattern equals' ->
            transCofreeF EqualsPattern <$> verifyEquals equals'
        ExistsPattern exists ->
            transCofreeF ExistsPattern <$> verifyExists exists
        FloorPattern floor' ->
            transCofreeF FloorPattern <$> verifyFloor floor'
        ForallPattern forall' ->
            transCofreeF ForallPattern <$> verifyForall forall'
        IffPattern iff ->
            transCofreeF IffPattern <$> verifyIff iff
        ImpliesPattern implies ->
            transCofreeF ImpliesPattern <$> verifyImplies implies
        InPattern in' ->
            transCofreeF InPattern <$> verifyIn in'
        NextPattern next ->
            transCofreeF NextPattern <$> verifyNext next
        NotPattern not' ->
            transCofreeF NotPattern <$> verifyNot not'
        OrPattern or' ->
            transCofreeF OrPattern <$> verifyOr or'
        RewritesPattern rewrites ->
            transCofreeF RewritesPattern <$> verifyRewrites rewrites
        StringLiteralPattern str ->
            transCofreeF (StringLiteralPattern . getConst)
                <$> verifyStringLiteral str
        CharLiteralPattern char ->
            transCofreeF (CharLiteralPattern . getConst)
                <$> verifyCharLiteral char
        TopPattern top ->
            transCofreeF TopPattern <$> verifyTop top
        VariablePattern var ->
            transCofreeF (VariablePattern . getConst)
                <$> verifyVariable var
  where
    transCofreeF fg (a :< fb) = a :< fg fb

verifyPatternSort :: MetaOrObject level => Sort level -> PatternVerifier ()
verifyPatternSort patternSort = do
    Context { declaredSortVariables } <- Reader.ask
    _ <- verifySort lookupSortDeclaration declaredSortVariables patternSort
    return ()

verifyOperands
    :: (MetaOrObject level, Traversable operator)
    => (forall a. operator a -> Sort level)
    -> operator (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF operator (Unified Valid) VerifiedKorePattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just (asUnified patternSort)
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (extract child)
            return child
    verified <- traverse verifyChildWithSort operator
    return (asUnified Valid { patternSort } :< verified)
{-# INLINE verifyOperands #-}

verifyAnd
    :: (logical ~ And level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyAnd = verifyOperands andSort

verifyOr
    :: (logical ~ Or level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyOr = verifyOperands orSort

verifyIff
    :: (logical ~ Iff level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyIff = verifyOperands iffSort

verifyImplies
    :: (logical ~ Implies level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyImplies = verifyOperands impliesSort

verifyBottom
    :: (logical ~ Bottom level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyBottom = verifyOperands bottomSort

verifyTop
    :: (logical ~ Top level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyTop = verifyOperands topSort

verifyNot
    :: (logical ~ Not level, MetaOrObject level)
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyNot = verifyOperands notSort

verifyRewrites
    :: logical ~ Rewrites Object
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical (Unified Valid) VerifiedKorePattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate
    :: (MetaOrObject level, Traversable predicate)
    => (forall a. predicate a -> Sort level)  -- ^ Operand sort
    -> (forall a. predicate a -> Sort level)  -- ^ Result sort
    -> predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate (Unified Valid) VerifiedKorePattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    _ :< verified <- verifyOperands operandSort predicate
    return (asUnified Valid { patternSort } :< verified)
{-# INLINE verifyPredicate #-}

verifyCeil
    :: (predicate ~ Ceil level, MetaOrObject level)
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate (Unified Valid) VerifiedKorePattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor
    :: (predicate ~ Floor level, MetaOrObject level)
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate (Unified Valid) VerifiedKorePattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals
    :: (predicate ~ Equals level, MetaOrObject level)
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate (Unified Valid) VerifiedKorePattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn
    :: (predicate ~ In level, MetaOrObject level)
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate (Unified Valid) VerifiedKorePattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext
    :: operator ~ Next Object
    => operator (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF operator (Unified Valid) VerifiedKorePattern)
verifyNext = verifyOperands nextSort

verifyBuiltinPattern
    :: Pattern Object Domain.Builtin Variable ()
    -> PatternVerifier ()
verifyBuiltinPattern pat = do
    Context { builtinPatternVerifier } <- Reader.ask
    Builtin.runPatternVerifier builtinPatternVerifier lookupSortDeclaration pat

verifyPatternsWithSorts
    :: [UnifiedSort]
    -> [PatternVerifier VerifiedKorePattern]
    -> PatternVerifier [VerifiedKorePattern]
verifyPatternsWithSorts sorts operands = do
    koreFailWhen (declaredOperandCount /= actualOperandCount)
        (  "Expected "
        ++ show declaredOperandCount
        ++ " operands, but got "
        ++ show actualOperandCount
        ++ "."
        )
    Monad.zipWithM
        (\sort verify -> do
            verified <- verify
            assertExpectedSort (Just sort) (extract verified)
            return verified
        )
        sorts
        operands
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplication
    :: (MetaOrObject level, base ~ Application level)
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyApplication application = do
    applicationSorts <- verifySymbolOrAlias applicationSymbolOrAlias
    let ApplicationSorts { applicationSortsOperands } = applicationSorts
        operandSorts = asUnified <$> applicationSortsOperands
    verifiedChildren <- verifyPatternsWithSorts operandSorts applicationChildren
    let patternSort = applicationSortsResult applicationSorts
        verified = application { applicationChildren = verifiedChildren }
    return (asUnified Valid { patternSort } :< verified)
  where
    Application { applicationSymbolOrAlias } = application
    Application { applicationChildren } = application

verifyBinder
    :: (MetaOrObject level, Traversable binder)
    => (forall a. binder a -> Sort level)
    -> (forall a. binder a -> Variable level)
    -> binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder (Unified Valid) VerifiedKorePattern)
verifyBinder binderSort binderVariable = \binder -> do
    let variable = binderVariable binder
        patternSort = binderSort binder
    verifyVariableDeclaration variable
    verifyPatternSort patternSort
    let withQuantifiedVariable ctx@Context { declaredVariables } =
            ctx
                { declaredVariables =
                    addDeclaredVariable
                        variable
                        declaredVariables
                }
    Reader.local withQuantifiedVariable (verifyOperands binderSort binder)
{-# INLINE verifyBinder #-}

verifyExists
    :: (binder ~ Exists level Variable, MetaOrObject level)
    => binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder (Unified Valid) VerifiedKorePattern)
verifyExists = verifyBinder existsSort existsVariable

verifyForall
    :: (binder ~ Forall level Variable, MetaOrObject level)
    => binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder (Unified Valid) VerifiedKorePattern)
verifyForall = verifyBinder forallSort forallVariable

verifyVariable
    :: (MetaOrObject level, base ~ Const (Variable level))
    => Variable level
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyVariable variable@Variable { variableName, variableSort } = do
    declaredVariable <- lookupDeclaredVariable variableName
    let Variable { variableSort = declaredSort } = declaredVariable
    koreFailWithLocationsWhen
        (variableSort /= declaredSort)
        [ variable, declaredVariable ]
        "The declared sort is different."
    let patternSort = variableSort
        verified = Const variable
    return (asUnified Valid { patternSort } :< verified)

verifyDomainValue
    :: base ~ DomainValue Object Domain.Builtin
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyDomainValue dv@DomainValue { domainValueSort, domainValueChild } = do
    let patternSort = domainValueSort
    verifyPatternSort patternSort
    verified <-
        case domainValueChild of
            Domain.BuiltinPattern (StringLiteral_ _) -> sequence dv
            _ -> koreFail "Domain value argument must be a literal string."
    return (asUnified Valid { patternSort } :< verified)

verifyStringLiteral
    :: base ~ Const StringLiteral
    => StringLiteral
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyStringLiteral str = do
    let patternSort = charListMetaSort
        verified = Const str
    return (asUnified Valid { patternSort } :< verified)

verifyCharLiteral
    :: base ~ Const CharLiteral
    => CharLiteral
    -> PatternVerifier (CofreeF base (Unified Valid) VerifiedKorePattern)
verifyCharLiteral char = do
    let patternSort = charMetaSort
        verified = Const char
    return (asUnified Valid { patternSort } :< verified)

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

assertSameSort
    :: Unified Sort
    -> Unified Sort
    -> PatternVerifier ()
assertSameSort (UnifiedObject expectedSort) (UnifiedObject actualSort) = do
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
assertSameSort (UnifiedMeta expectedSort) (UnifiedMeta actualSort) = do
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
assertSameSort (UnifiedMeta expectedSort) (UnifiedObject actualSort) = do
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
assertSameSort (UnifiedObject expectedSort) (UnifiedMeta actualSort) = do
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

assertExpectedSort
    :: Maybe (Unified Sort)
    -> Unified Valid
    -> PatternVerifier ()
assertExpectedSort Nothing _ = return ()
assertExpectedSort (Just expected) verified =
    case verified of
        UnifiedMeta Valid { patternSort } ->
            assertSameSort expected (UnifiedMeta patternSort)
        UnifiedObject Valid { patternSort } ->
            assertSameSort expected (UnifiedObject patternSort)

verifyFreeVariables
    :: CommonKorePattern
    -> PatternVerifier DeclaredVariables
verifyFreeVariables unifiedPattern =
    Monad.foldM
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
