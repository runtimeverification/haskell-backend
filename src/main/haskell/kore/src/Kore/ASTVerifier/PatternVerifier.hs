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
    , verifyStandalonePattern
    , verifyNoPatterns
    , verifyAliasLeftPattern
    , verifyFreeVariables
    , withDeclaredVariables
    , PatternVerifier (..)
    , runPatternVerifier
    , Context (..)
    , DeclaredVariables (..), emptyDeclaredVariables
    , assertExpectedSort
    , assertSameSort
    ) where

import           Control.Comonad
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
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

import qualified Kore.Annotation.Valid as Valid
import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTHelpers
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
import qualified Kore.Variables.Free as Variables

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
        , indexedModule :: !(KoreIndexedModule Attribute.Null Attribute.Null)
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

{- | Add a new variable to the set of 'DeclaredVariables'.

The new variable must not already be declared.

 -}
newDeclaredVariable
    :: DeclaredVariables
    -> Unified Variable
    -> PatternVerifier DeclaredVariables
newDeclaredVariable declared =
    \case
        UnifiedMeta variable@Variable { variableName } -> do
            let DeclaredVariables { metaDeclaredVariables } = declared
            case Map.lookup variableName metaDeclaredVariables of
                Just variable' ->
                    alreadyDeclared variable variable'
                Nothing ->
                    return declared
                        { metaDeclaredVariables =
                            Map.insert
                                variableName
                                variable
                                metaDeclaredVariables
                        }
        UnifiedObject variable@Variable { variableName } -> do
            let DeclaredVariables { objectDeclaredVariables } = declared
            case Map.lookup variableName objectDeclaredVariables of
                Just variable' ->
                    alreadyDeclared variable variable'
                Nothing ->
                    return declared
                        { objectDeclaredVariables =
                            Map.insert
                                variableName
                                variable
                                objectDeclaredVariables
                        }
  where
    alreadyDeclared
        :: MetaOrObject level
        => Variable level
        -> Variable level
        -> PatternVerifier DeclaredVariables
    alreadyDeclared variable@Variable { variableName } variable' =
        koreFailWithLocations [variable', variable]
            ("Variable '"
                ++ getIdForError variableName
                ++ "' was already declared."
            )

{- | Collect 'DeclaredVariables'.

Each variable in the 'Foldable' collection must be unique.

See also: 'newDeclaredVariable'

 -}
uniqueDeclaredVariables
    :: Foldable f
    => f (Unified Variable)
    -> PatternVerifier DeclaredVariables
uniqueDeclaredVariables =
    Foldable.foldlM newDeclaredVariable emptyDeclaredVariables

{- | Run a 'PatternVerifier' in a particular variable context.

See also: 'verifyStandalonePattern'

 -}
withDeclaredVariables
    :: DeclaredVariables
    -> PatternVerifier a
    -> PatternVerifier a
withDeclaredVariables declaredVariables' =
    Reader.local (\ctx -> ctx { declaredVariables = declaredVariables' })

{- | Verify the left-hand side of an alias definition.

The left-hand side must consist of the alias applied to a non-repeating sequence
of variables with the same sorts as the alias declaration.

The verified left-hand side is returned with the set of 'DeclaredVariables'. The
'DeclaredVariables' are used to verify the right-hand side of the alias
definition.

See also: 'uniqueDeclaredVariables', 'withDeclaredVariables'

 -}
verifyAliasLeftPattern
    :: forall level. MetaOrObject level
    => Application level (Variable level)
    -> PatternVerifier
        (DeclaredVariables, Application level (Variable level))
verifyAliasLeftPattern leftPattern = do
    _ :< verified <- verifyApplication (expectVariable <$> leftPattern)
    declaredVariables <- uniqueDeclaredVariables (asUnified . fst <$> verified)
    let verifiedLeftPattern = fst <$> verified
    return (declaredVariables, verifiedLeftPattern)
  where
    expectVariable
        :: Variable level
        -> PatternVerifier (Variable level, Unified (Valid (Unified Variable)))
    expectVariable var = do
        verifyVariableDeclaration var
        let
            patternSort = variableSort var
            freeVariables = Set.singleton (asUnified var)
            valid = Valid { patternSort, freeVariables }
        return (var, asUnified valid)

{- | Verify that a Kore pattern is well-formed.

This includes verifying that:
- the pattern has the expected sort (if provided)
- the sorts of all subterms agree
- all variables are explicitly quantified

 -}
verifyPattern
    :: Maybe UnifiedSort
    -- ^ If present, represents the expected sort of the pattern.
    -> CommonKorePattern
    -> PatternVerifier VerifiedKorePattern
verifyPattern expectedSort korePattern = do
    verified <- Recursive.fold verifyUnifiedPattern korePattern
    assertExpectedSort expectedSort (extract verified)
    return verified

{- | Verify a Kore pattern with implicitly-quantified variables.

@verifyStandalonePattern@ calls 'verifyPattern', but quantifies all free
variables of the pattern.

See also: 'verifyPattern', 'verifyFreeVariables', 'withDeclaredVariables'

 -}
verifyStandalonePattern
    :: Maybe UnifiedSort
    -> CommonKorePattern
    -> PatternVerifier VerifiedKorePattern
verifyStandalonePattern expectedSort korePattern = do
    declaredVariables <- verifyFreeVariables korePattern
    withDeclaredVariables declaredVariables
        (verifyPattern expectedSort korePattern)

{- | Fail if a Kore pattern is found.

@verifyNoPatterns@ is useful to 'traverse' sentence types with phantom pattern
type variables.

 -}
verifyNoPatterns
    :: MonadError (Error VerifyError) m
    => CommonKorePattern
    -> m VerifiedKorePattern
verifyNoPatterns _ = koreFail "Unexpected pattern."

verifyUnifiedPattern
    :: Base CommonKorePattern (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier VerifiedKorePattern
verifyUnifiedPattern (_ :< pat) =
    case pat of
        UnifiedMetaPattern mpat -> do
            valid :< vpat <- verifyMetaPattern mpat
            (return . Recursive.embed)
                (UnifiedMeta valid :< UnifiedMetaPattern vpat)
        UnifiedObjectPattern opat -> do
            valid :< vpat <- verifyObjectPattern opat
            (return . Recursive.embed)
                (UnifiedObject valid :< UnifiedObjectPattern vpat)

verifyMetaPattern
    ::  ( base ~ Pattern Meta Domain.Builtin Variable
        , valid ~ Valid (Unified Variable) Meta
        )
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
verifyMetaPattern pat =
    withLocationAndContext pat patternName $ do
        verifyPatternHead pat
  where
    patternName = patternNameForContext pat

verifyObjectPattern
    ::  ( base ~ Pattern Object Domain.Builtin Variable
        , valid ~ Valid (Unified Variable) Object
        )
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
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
    ::  ( MetaOrObject level
        , base ~ Pattern level Domain.Builtin Variable
        , valid ~ Valid (Unified Variable) level
        )
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
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

unifiedFreeVariables :: Unified (Valid variable) -> Set variable
unifiedFreeVariables = transformUnified Valid.freeVariables

verifyOperands
    ::  ( MetaOrObject level
        , Traversable operator
        , valid ~ Valid (Unified Variable) level
        )
    => (forall a. operator a -> Sort level)
    -> operator (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF operator valid VerifiedKorePattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just (asUnified patternSort)
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (extract child)
            return child
    verified <- traverse verifyChildWithSort operator
    let freeVariables =
            Foldable.foldl'
                Set.union
                Set.empty
                (unifiedFreeVariables . extract <$> verified)
    return (Valid { patternSort, freeVariables } :< verified)
{-# INLINE verifyOperands #-}

verifyAnd
    ::  ( logical ~ And level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyAnd = verifyOperands andSort

verifyOr
    ::  ( logical ~ Or level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyOr = verifyOperands orSort

verifyIff
    ::  ( logical ~ Iff level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyIff = verifyOperands iffSort

verifyImplies
    ::  ( logical ~ Implies level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyImplies = verifyOperands impliesSort

verifyBottom
    ::  ( logical ~ Bottom level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyBottom = verifyOperands bottomSort

verifyTop
    ::  ( logical ~ Top level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyTop = verifyOperands topSort

verifyNot
    ::  ( logical ~ Not level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyNot = verifyOperands notSort

verifyRewrites
    ::  ( logical ~ Rewrites Object
        , valid ~ Valid (Unified Variable) Object
        )
    => logical (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF logical valid VerifiedKorePattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate
    ::  ( MetaOrObject level
        , Traversable predicate
        , valid ~ Valid (Unified Variable) level
        )
    => (forall a. predicate a -> Sort level)  -- ^ Operand sort
    -> (forall a. predicate a -> Sort level)  -- ^ Result sort
    -> predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate valid VerifiedKorePattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    Valid { freeVariables } :< verified <- verifyOperands operandSort predicate
    return (Valid { patternSort, freeVariables } :< verified)
{-# INLINE verifyPredicate #-}

verifyCeil
    ::  ( predicate ~ Ceil level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate valid VerifiedKorePattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor
    ::  ( predicate ~ Floor level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate valid VerifiedKorePattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals
    ::  ( predicate ~ Equals level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate valid VerifiedKorePattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn
    ::  ( predicate ~ In level
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => predicate (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF predicate valid VerifiedKorePattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext
    ::  ( operator ~ Next Object
        , valid ~ Valid (Unified Variable) Object
        )
    => operator (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF operator valid VerifiedKorePattern)
verifyNext = verifyOperands nextSort

verifyBuiltinPattern
    :: Pattern Object Domain.Builtin Variable ()
    -> PatternVerifier ()
verifyBuiltinPattern pat = do
    Context { builtinPatternVerifier } <- Reader.ask
    Builtin.runPatternVerifier builtinPatternVerifier lookupSortDeclaration pat

verifyPatternsWithSorts
    :: ( Comonad pat, valid ~ Valid (Unified Variable) )
    => [UnifiedSort]
    -> [PatternVerifier (pat (Unified valid))]
    -> PatternVerifier [(pat (Unified valid))]
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
    ::  ( MetaOrObject level
        , Comonad child
        , base ~ Application level
        , valid ~ Valid (Unified Variable)
        )
    => base (PatternVerifier (child (Unified valid)))
    -> PatternVerifier (CofreeF base (valid level) (child (Unified valid)))
verifyApplication application = do
    applicationSorts <- verifySymbolOrAlias applicationSymbolOrAlias
    let ApplicationSorts { applicationSortsOperands } = applicationSorts
        operandSorts = asUnified <$> applicationSortsOperands
    verifiedChildren <- verifyPatternsWithSorts operandSorts applicationChildren
    let patternSort = applicationSortsResult applicationSorts
        verified = application { applicationChildren = verifiedChildren }
        freeVariables =
            Set.unions (unifiedFreeVariables . extract <$> verifiedChildren)
    return (Valid { patternSort, freeVariables } :< verified)
  where
    Application { applicationSymbolOrAlias } = application
    Application { applicationChildren } = application

verifyBinder
    ::  ( MetaOrObject level
        , Traversable binder
        , valid ~ Valid (Unified Variable) level
        )
    => (forall a. binder a -> Sort level)
    -> (forall a. binder a -> Variable level)
    -> binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder valid VerifiedKorePattern)
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
    ::  ( binder ~ Exists level Variable
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder valid VerifiedKorePattern)
verifyExists = verifyBinder existsSort existsVariable

verifyForall
    ::  ( binder ~ Forall level Variable
        , valid ~ Valid (Unified Variable) level
        , MetaOrObject level
        )
    => binder (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF binder valid VerifiedKorePattern)
verifyForall = verifyBinder forallSort forallVariable

verifyVariable
    ::  ( MetaOrObject level
        , base ~ Const (Variable level)
        , valid ~ Valid (Unified Variable) level
        )
    => Variable level
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
verifyVariable variable@Variable { variableName, variableSort } = do
    declaredVariable <- lookupDeclaredVariable variableName
    let Variable { variableSort = declaredSort } = declaredVariable
    koreFailWithLocationsWhen
        (variableSort /= declaredSort)
        [ variable, declaredVariable ]
        "The declared sort is different."
    let patternSort = variableSort
        verified = Const variable
        freeVariables = Set.singleton (asUnified variable)
    return (Valid { patternSort, freeVariables } :< verified)

verifyDomainValue
    ::  ( base ~ DomainValue Object Domain.Builtin
        , valid ~ Valid (Unified Variable) Object
        )
    => base (PatternVerifier VerifiedKorePattern)
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
verifyDomainValue dv@DomainValue { domainValueSort, domainValueChild } = do
    let patternSort = domainValueSort
    verifyPatternSort patternSort
    verified <-
        case domainValueChild of
            Domain.BuiltinPattern (StringLiteral_ _) -> sequence dv
            _ -> koreFail "Domain value argument must be a literal string."
    let freeVariables =
            Foldable.foldl'
                Set.union
                Set.empty
                (unifiedFreeVariables . extract <$> verified)
    Monad.unless (Set.null freeVariables)
        (koreFail "Domain value must not contain free variables.")
    return (Valid { patternSort, freeVariables } :< verified)

verifyStringLiteral
    :: (base ~ Const StringLiteral, valid ~ Valid variable Meta)
    => StringLiteral
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
verifyStringLiteral str = do
    let patternSort = charListMetaSort
        freeVariables = Set.empty
        verified = Const str
    return (Valid { patternSort, freeVariables } :< verified)

verifyCharLiteral
    :: (base ~ Const CharLiteral, valid ~ Valid variable Meta)
    => CharLiteral
    -> PatternVerifier (CofreeF base valid VerifiedKorePattern)
verifyCharLiteral char = do
    let patternSort = charMetaSort
        freeVariables = Set.empty
        verified = Const char
    return (Valid { patternSort, freeVariables } :< verified)

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
    -> sa level pat
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
    -> Unified (Valid variable)
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
        (Set.toList (Variables.freeVariables unifiedPattern))

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
