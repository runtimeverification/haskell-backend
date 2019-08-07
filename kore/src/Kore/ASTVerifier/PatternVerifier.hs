{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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

import           Control.Applicative
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Trans.Class as Trans
import           Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( (&) )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           Data.Text.Prettyprint.Doc
                 ( (<+>) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc.Render.Text
                 ( renderStrict )

import           Kore.AST.Error
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Sort as Attribute.Sort
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Attribute.Synthetic
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import qualified Kore.Internal.Alias as Internal
import           Kore.Internal.ApplicationSorts
import qualified Kore.Internal.Symbol as Internal
import           Kore.Internal.TermLike
                 ( TermLike )
import qualified Kore.Internal.TermLike as Internal
import           Kore.Parser
                 ( ParsedPattern )
import           Kore.Syntax as Syntax
import           Kore.Syntax.Definition
import           Kore.Unparser
import qualified Kore.Variables.Free as Variables
import           Kore.Variables.UnifiedVariable
import qualified Kore.Verified as Verified

newtype DeclaredVariables =
    DeclaredVariables
        { getDeclaredVariables :: Map.Map Id (UnifiedVariable Variable) }
    deriving (Monoid, Semigroup)

emptyDeclaredVariables :: DeclaredVariables
emptyDeclaredVariables = mempty

data Context =
    Context
        { declaredVariables :: !DeclaredVariables
        , declaredSortVariables :: !(Set SortVariable)
        -- ^ The sort variables in scope.
        , indexedModule :: !(IndexedModule () Attribute.Symbol Attribute.Null)
        -- ^ The indexed Kore module containing all definitions in scope.
        , builtinDomainValueVerifiers
            :: !(Builtin.DomainValueVerifiers Verified.Pattern)
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
runPatternVerifier context PatternVerifier { getPatternVerifier } =
    runReaderT getPatternVerifier context

lookupSortDeclaration
    :: Id
    -> PatternVerifier (SentenceSort ())
lookupSortDeclaration sortId = do
    Context { indexedModule } <- Reader.ask
    (_, sortDecl) <- resolveSort indexedModule sortId
    return sortDecl

lookupAlias
    ::  SymbolOrAlias
    ->  MaybeT PatternVerifier Internal.Alias
lookupAlias symbolOrAlias = do
    Context { indexedModule } <- Reader.ask
    let resolveAlias' = resolveAlias indexedModule aliasConstructor
    (_, decl) <- resolveAlias' `catchError` const empty
    aliasSorts <-
        Trans.lift
        $ applicationSortsFromSymbolOrAliasSentence symbolOrAlias decl
    return Internal.Alias
        { aliasConstructor
        , aliasParams
        , aliasSorts
        }
  where
    aliasConstructor = symbolOrAliasConstructor symbolOrAlias
    aliasParams = symbolOrAliasParams symbolOrAlias

lookupSymbol
    ::  SymbolOrAlias
    ->  MaybeT PatternVerifier Internal.Symbol
lookupSymbol symbolOrAlias = do
    Context { indexedModule } <- Reader.ask
    let resolveSymbol' = resolveSymbol indexedModule symbolConstructor
    (symbolAttributes, decl) <- resolveSymbol' `catchError` const empty
    symbolSorts <-
        Trans.lift
        $ applicationSortsFromSymbolOrAliasSentence symbolOrAlias decl
    let symbol =
            Internal.Symbol
                { symbolConstructor
                , symbolParams
                , symbolAttributes
                , symbolSorts
                }
    return symbol
  where
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias

lookupDeclaredVariable :: Id -> PatternVerifier (UnifiedVariable Variable)
lookupDeclaredVariable varId = do
    variables <- Reader.asks (getDeclaredVariables . declaredVariables)
    maybe errorUnquantified return $ Map.lookup varId variables
  where
    errorUnquantified :: PatternVerifier (UnifiedVariable Variable)
    errorUnquantified =
        koreFailWithLocations [varId]
            ("Unquantified variable: '" <> getId varId <> "'.")

addDeclaredVariable
    :: UnifiedVariable Variable
    -> DeclaredVariables
    -> DeclaredVariables
addDeclaredVariable variable (getDeclaredVariables -> variables) =
    DeclaredVariables $ Map.insert
        (foldMapVariable variableName variable)
        variable
        variables

{- | Add a new variable to the set of 'DeclaredVariables'.

The new variable must not already be declared.

 -}
newDeclaredVariable
    :: DeclaredVariables
    -> UnifiedVariable Variable
    -> PatternVerifier DeclaredVariables
newDeclaredVariable declared variable = do
    let declaredVariables = getDeclaredVariables declared
    case Map.lookup name declaredVariables of
        Just variable' -> alreadyDeclared variable'
        Nothing -> return (addDeclaredVariable variable declared)
  where
    name = foldMapVariable variableName variable
    alreadyDeclared
        :: UnifiedVariable Variable -> PatternVerifier DeclaredVariables
    alreadyDeclared variable' =
        koreFailWithLocations [variable', variable]
            (  "Variable '"
            <> getId name
            <> "' was already declared."
            )

{- | Collect 'DeclaredVariables'.

Each variable in the 'Foldable' collection must be unique.

See also: 'newDeclaredVariable'

 -}
uniqueDeclaredVariables
    :: Foldable f
    => f (UnifiedVariable Variable)
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
    :: Application SymbolOrAlias (ElementVariable Variable)
    -> PatternVerifier
        ( DeclaredVariables
        , Application SymbolOrAlias (ElementVariable Variable)
        )
verifyAliasLeftPattern leftPattern = do
    _ :< verified <-
        verifyApplyAlias snd (expectVariable . ElemVar  <$> leftPattern)
        & runMaybeT
        & (>>= maybe (error . noHead $ symbolOrAlias) return)
    declaredVariables <- uniqueDeclaredVariables (fst <$> verified)
    let verifiedLeftPattern = traverse extractElementVariable
            leftPattern
                { applicationChildren = fst <$> applicationChildren verified }
    case verifiedLeftPattern of
        Just result -> return (declaredVariables, result)
        Nothing -> error "Impossible change from element var to set var"
  where
    symbolOrAlias = applicationSymbolOrAlias leftPattern
    expectVariable
        :: UnifiedVariable Variable
        -> PatternVerifier
            (UnifiedVariable Variable, Attribute.Pattern Variable)
    expectVariable var = do
        verifyVariableDeclaration var
        let attrs = synthetic (Const var)
        return (var, attrs)

{- | Verify that a Kore pattern is well-formed.

This includes verifying that:
- the pattern has the expected sort (if provided)
- the sorts of all subterms agree
- all variables are explicitly quantified

 -}
verifyPattern
    :: Maybe Sort
    -- ^ If present, represents the expected sort of the pattern.
    -> ParsedPattern
    -> PatternVerifier Verified.Pattern
verifyPattern expectedSort korePattern = do
    verified <- Recursive.fold verifyPatternWorker korePattern
    assertExpectedSort expectedSort (Internal.extractAttributes verified)
    return verified
  where
    verifyPatternWorker base = Recursive.embed <$> verifyObjectPattern base

{- | Verify a Kore pattern with implicitly-quantified variables.

@verifyStandalonePattern@ calls 'verifyPattern', but quantifies all free
variables of the pattern.

See also: 'verifyPattern', 'verifyFreeVariables', 'withDeclaredVariables'

 -}
verifyStandalonePattern
    :: Maybe Sort
    -> ParsedPattern
    -> PatternVerifier Verified.Pattern
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
    => ParsedPattern
    -> m Verified.Pattern
verifyNoPatterns _ = koreFail "Unexpected pattern."

verifyObjectPattern
    :: Base ParsedPattern (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Base (TermLike Variable) Verified.Pattern)
verifyObjectPattern base@(_ :< patternF) =
    withLocationAndContext patternF patternName $ verifyPatternHead base
  where
    patternName = patternNameForContext patternF

verifyPatternHead
    :: Base ParsedPattern (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Base (TermLike Variable) Verified.Pattern)
verifyPatternHead (_ :< patternF) =
    case patternF of
        Syntax.AndF and' ->
            transCofreeF Internal.AndF <$> verifyAnd and'
        Syntax.ApplicationF app ->
            verifyApplication Internal.extractAttributes app
        Syntax.BottomF bottom ->
            transCofreeF Internal.BottomF <$> verifyBottom bottom
        Syntax.CeilF ceil' ->
            transCofreeF Internal.CeilF <$> verifyCeil ceil'
        Syntax.DomainValueF dv -> verifyDomainValue dv
        Syntax.EqualsF equals' ->
            transCofreeF Internal.EqualsF <$> verifyEquals equals'
        Syntax.ExistsF exists ->
            transCofreeF Internal.ExistsF <$> verifyExists exists
        Syntax.FloorF floor' ->
            transCofreeF Internal.FloorF <$> verifyFloor floor'
        Syntax.ForallF forall' ->
            transCofreeF Internal.ForallF <$> verifyForall forall'
        Syntax.IffF iff ->
            transCofreeF Internal.IffF <$> verifyIff iff
        Syntax.ImpliesF implies ->
            transCofreeF Internal.ImpliesF <$> verifyImplies implies
        Syntax.InF in' ->
            transCofreeF Internal.InF <$> verifyIn in'
        Syntax.MuF mu ->
            transCofreeF Internal.MuF <$> verifyMu mu
        Syntax.NextF next ->
            transCofreeF Internal.NextF <$> verifyNext next
        Syntax.NotF not' ->
            transCofreeF Internal.NotF <$> verifyNot not'
        Syntax.NuF nu ->
            transCofreeF Internal.NuF <$> verifyNu nu
        Syntax.OrF or' ->
            transCofreeF Internal.OrF <$> verifyOr or'
        Syntax.RewritesF rewrites ->
            transCofreeF Internal.RewritesF <$> verifyRewrites rewrites
        Syntax.StringLiteralF str ->
            transCofreeF Internal.StringLiteralF <$> verifyStringLiteral str
        Syntax.CharLiteralF char ->
            transCofreeF Internal.CharLiteralF <$> verifyCharLiteral char
        Syntax.TopF top ->
            transCofreeF Internal.TopF <$> verifyTop top
        Syntax.VariableF var ->
            transCofreeF (Internal.VariableF . getConst)
                <$> verifyVariable var
        Syntax.InhabitantF _ ->
            koreFail "Unexpected pattern."
  where
    transCofreeF fg (a :< fb) = a :< fg fb

verifyPatternSort :: Sort -> PatternVerifier ()
verifyPatternSort patternSort = do
    Context { declaredSortVariables } <- Reader.ask
    _ <- verifySort lookupSortDeclaration declaredSortVariables patternSort
    return ()

verifyOperands
    :: (Traversable operator, Synthetic operator (Attribute.Pattern Variable))
    => (forall a. operator a -> Sort)
    -> operator (PatternVerifier Verified.Pattern)
    ->  PatternVerifier
            (CofreeF operator (Attribute.Pattern Variable) Verified.Pattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just patternSort
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (Internal.extractAttributes child)
            return child
    verified <- traverse verifyChildWithSort operator
    let attrs = synthetic (Internal.extractAttributes <$> verified)
    return (attrs :< verified)
{-# INLINE verifyOperands #-}

verifyAnd
    ::  ( logical ~ And Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyAnd = verifyOperands andSort

verifyOr
    ::  ( logical ~ Or Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyOr = verifyOperands orSort

verifyIff
    ::  ( logical ~ Iff Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyIff = verifyOperands iffSort

verifyImplies
    ::  ( logical ~ Implies Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyImplies = verifyOperands impliesSort

verifyBottom
    ::  ( logical ~ Bottom Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyBottom = verifyOperands bottomSort

verifyTop
    ::  ( logical ~ Top Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyTop = verifyOperands topSort

verifyNot
    ::  ( logical ~ Not Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyNot = verifyOperands notSort

verifyRewrites
    ::  ( logical ~ Rewrites Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate
    ::  ( Traversable predicate
        , Synthetic predicate (Attribute.Pattern Variable)
        , valid ~ Attribute.Pattern Variable
        )
    => (forall a. predicate a -> Sort)  -- ^ Operand sort
    -> (forall a. predicate a -> Sort)  -- ^ Result sort
    -> predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    verifyOperands operandSort predicate
{-# INLINE verifyPredicate #-}

verifyCeil
    ::  ( predicate ~ Ceil Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor
    ::  ( predicate ~ Floor Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals
    ::  ( predicate ~ Equals Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn
    ::  ( predicate ~ In Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext
    ::  ( operator ~ Next Sort
        , valid ~ Attribute.Pattern Variable
        )
    => operator (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF operator valid Verified.Pattern)
verifyNext = verifyOperands nextSort

verifyPatternsWithSorts
    :: (child -> Attribute.Pattern Variable)
    -> [Sort]
    -> [PatternVerifier child]
    -> PatternVerifier [child]
verifyPatternsWithSorts getChildAttributes sorts operands = do
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
            assertExpectedSort (Just sort) (getChildAttributes verified)
            return verified
        )
        sorts
        operands
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplyAlias
    ::  (child -> Attribute.Pattern Variable)
    ->  Application SymbolOrAlias (PatternVerifier child)
    ->  MaybeT PatternVerifier
            (CofreeF
                (Application Internal.Alias)
                (Attribute.Pattern Variable)
                child
            )
verifyApplyAlias getChildAttributes application =
    lookupAlias symbolOrAlias >>= \alias -> Trans.lift $ do
    let verified = application { applicationSymbolOrAlias = alias }
        sorts = Internal.aliasSorts alias
    verifyApplicationChildren getChildAttributes verified sorts
  where
    Application { applicationSymbolOrAlias = symbolOrAlias } = application

verifyApplySymbol
    ::  (child -> Attribute.Pattern Variable)
    ->  Application SymbolOrAlias (PatternVerifier child)
    ->  MaybeT PatternVerifier
            (CofreeF
                (Application Internal.Symbol)
                (Attribute.Pattern Variable)
                child
            )
verifyApplySymbol getChildAttributes application =
    lookupSymbol symbolOrAlias >>= \symbol -> Trans.lift $ do
    let verified = application { applicationSymbolOrAlias = symbol }
        sorts = Internal.symbolSorts symbol
    verifyApplicationChildren getChildAttributes verified sorts
  where
    Application { applicationSymbolOrAlias = symbolOrAlias } = application

verifyApplicationChildren
    ::  Synthetic (Application head) (Attribute.Pattern Variable)
    =>  (child -> Attribute.Pattern Variable)
    ->  Application head (PatternVerifier child)
    ->  ApplicationSorts
    ->  PatternVerifier
            (CofreeF
                (Application head)
                (Attribute.Pattern Variable)
                child
            )
verifyApplicationChildren getChildAttributes application sorts = do
    let operandSorts = applicationSortsOperands sorts
    verifiedChildren <- verifyChildren operandSorts children
    let verified = application { applicationChildren = verifiedChildren }
        attrs = synthetic (getChildAttributes <$> verified)
    return (attrs :< verified)
  where
    verifyChildren = verifyPatternsWithSorts getChildAttributes
    Application { applicationChildren = children } = application

verifyApplication
    ::  (Verified.Pattern -> Attribute.Pattern Variable)
    ->  Application SymbolOrAlias (PatternVerifier Verified.Pattern)
    ->  PatternVerifier (Base (TermLike Variable) Verified.Pattern)
verifyApplication getChildAttributes application = do
    result <- verifyApplyAlias' <|> verifyApplySymbol' & runMaybeT
    maybe (koreFail . noHead $ symbolOrAlias) return result
  where
    symbolOrAlias = applicationSymbolOrAlias application
    transCofreeF fg (a :< fb) = a :< fg fb
    verifyApplyAlias' =
        transCofreeF Internal.ApplyAliasF
        <$> verifyApplyAlias getChildAttributes application
    verifyApplySymbol' =
        transCofreeF Internal.ApplySymbolF
        <$> verifyApplySymbol getChildAttributes application

verifyBinder
    ::  ( Traversable binder, Synthetic binder (Attribute.Pattern Variable)
        , valid ~ Attribute.Pattern Variable
        )
    => (forall a. binder a -> Sort)
    -> (forall a. binder a -> (UnifiedVariable Variable))
    -> binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
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
    valid :< binder' <-
        Reader.local
            withQuantifiedVariable
            (verifyOperands binderSort binder)
    let valid' = Attribute.deleteFreeVariable variable valid
    return (valid' :< binder')
{-# INLINE verifyBinder #-}

verifyExists
    ::  ( binder ~ Exists Sort Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyExists = verifyBinder existsSort (ElemVar . existsVariable)

verifyForall
    ::  ( binder ~ Forall Sort Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyForall = verifyBinder forallSort (ElemVar . forallVariable)

verifyMu
    ::  ( binder ~ Mu Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyMu = verifyBinder muSort (SetVar . muVariable)
  where
    muSort = variableSort . getSetVariable . muVariable

verifyNu
    ::  ( binder ~ Nu Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyNu = verifyBinder nuSort (SetVar . nuVariable)
  where
    nuSort = variableSort . getSetVariable . nuVariable

verifyVariable
    ::  ( base ~ Const (UnifiedVariable Variable)
        , valid ~ Attribute.Pattern Variable
        )
    => UnifiedVariable Variable
    -> PatternVerifier (CofreeF base valid Verified.Pattern)
verifyVariable var = do
    declaredVariable <- lookupDeclaredVariable varName
    let declaredSort = foldMapVariable variableSort declaredVariable
    koreFailWithLocationsWhen
        (varSort /= declaredSort)
        [ var, declaredVariable ]
        "The declared sort is different."
    let verified = Const var
        attrs = synthetic (Internal.extractAttributes <$> verified)
    return (attrs :< verified)
  where
    varName = foldMapVariable variableName var
    varSort = foldMapVariable variableSort var

verifyDomainValue
    :: DomainValue Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Base Verified.Pattern Verified.Pattern)
verifyDomainValue domain = do
    let DomainValue { domainValueSort = patternSort } = domain
    Context { builtinDomainValueVerifiers, indexedModule } <- Reader.ask
    verifyPatternSort patternSort
    let
        lookupSortDeclaration' sortId = do
            (_, sortDecl) <- resolveSort indexedModule sortId
            return sortDecl
    verifySortHasDomainValues patternSort
    domain' <- sequence domain
    verified <-
        PatternVerifier
        $ Reader.lift
        $ Builtin.verifyDomainValue
            builtinDomainValueVerifiers
            lookupSortDeclaration'
            domain'
    let attrs = synthetic (Internal.extractAttributes <$> verified)
        Attribute.Pattern { freeVariables } = attrs
    Monad.unless (null freeVariables)
        (koreFail "Domain value must not contain free variables.")
    return (attrs :< verified)

verifySortHasDomainValues :: Sort -> PatternVerifier ()
verifySortHasDomainValues patternSort = do
    Context { indexedModule } <- Reader.ask
    (sortAttrs, _) <- resolveSort indexedModule dvSortId
    koreFailWithLocationsWhen
        (not
            (Attribute.HasDomainValues.getHasDomainValues
                (Attribute.Sort.hasDomainValues sortAttrs)
            )
        )
        [patternSort]
        sortNeedsDomainValueAttributeMessage
  where
    dvSortId = case patternSort of
        SortVariableSort _ ->
            error "Unimplemented: domain values with variable sorts"
        SortActualSort SortActual {sortActualName} -> sortActualName

verifyStringLiteral
    :: valid ~ Attribute.Pattern Variable
    => StringLiteral (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF StringLiteral valid Verified.Pattern)
verifyStringLiteral str = do
    verified <- sequence str
    let attrs = synthetic (Internal.extractAttributes <$> verified)
    return (attrs :< verified)

verifyCharLiteral
    :: valid ~ Attribute.Pattern Variable
    => CharLiteral (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF CharLiteral valid Verified.Pattern)
verifyCharLiteral char = do
    verified <- sequence char
    let attrs = synthetic (Internal.extractAttributes <$> verified)
    return (attrs :< verified)

verifyVariableDeclaration
    :: UnifiedVariable Variable -> PatternVerifier VerifySuccess
verifyVariableDeclaration variable = do
    Context { declaredSortVariables } <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        varSort
  where
    varSort = foldMapVariable variableSort variable

applicationSortsFromSymbolOrAliasSentence
    :: SentenceSymbolOrAlias sentence
    => SymbolOrAlias
    -> sentence pat
    -> PatternVerifier ApplicationSorts
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
    :: Sort
    -> Sort
    -> PatternVerifier ()
assertSameSort expectedSort actualSort =
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
        ((renderStrict . Pretty.layoutCompact)
         ("Expecting sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
        )

assertExpectedSort
    :: Maybe Sort
    -> Attribute.Pattern variable
    -> PatternVerifier ()
assertExpectedSort Nothing _ = return ()
assertExpectedSort (Just expected) Attribute.Pattern { patternSort } =
    assertSameSort expected patternSort

verifyFreeVariables
    :: ParsedPattern
    -> PatternVerifier DeclaredVariables
verifyFreeVariables unifiedPattern =
    Monad.foldM
        addFreeVariable
        emptyDeclaredVariables
        $
        Set.toList (Variables.freePureVariables unifiedPattern)

addFreeVariable
    :: DeclaredVariables
    -> UnifiedVariable Variable
    -> PatternVerifier DeclaredVariables
addFreeVariable (getDeclaredVariables -> vars) var = do
    checkVariable var vars
    return . DeclaredVariables $
        Map.insert (foldMapVariable variableName var) var vars

checkVariable
    :: UnifiedVariable Variable
    -> Map.Map Id (UnifiedVariable Variable)
    -> PatternVerifier VerifySuccess
checkVariable var vars =
    maybe verifySuccess inconsistent
    $ Map.lookup (foldMapVariable variableName var) vars
  where
    inconsistent v =
        koreFailWithLocations [v, var]
        $ renderStrict $ Pretty.layoutCompact
        $ "Inconsistent free variable usage:"
            <+> unparse v
            <+> "and"
            <+> unparse var
            <> Pretty.dot

patternNameForContext :: PatternF Variable p -> Text
patternNameForContext (AndF _) = "\\and"
patternNameForContext (ApplicationF application) =
    "symbol or alias '"
    <> getId
        (symbolOrAliasConstructor (applicationSymbolOrAlias application))
    <> "'"
patternNameForContext (BottomF _) = "\\bottom"
patternNameForContext (CeilF _) = "\\ceil"
patternNameForContext (DomainValueF _) = "\\dv"
patternNameForContext (EqualsF _) = "\\equals"
patternNameForContext (ExistsF exists) =
    "\\exists '"
    <> variableNameForContext (getElementVariable $ existsVariable exists)
    <> "'"
patternNameForContext (FloorF _) = "\\floor"
patternNameForContext (ForallF forall) =
    "\\forall '"
    <> variableNameForContext (getElementVariable $ forallVariable forall)
    <> "'"
patternNameForContext (IffF _) = "\\iff"
patternNameForContext (ImpliesF _) = "\\implies"
patternNameForContext (InF _) = "\\in"
patternNameForContext (MuF _) = "\\mu"
patternNameForContext (NextF _) = "\\next"
patternNameForContext (NotF _) = "\\not"
patternNameForContext (NuF _) = "\\nu"
patternNameForContext (OrF _) = "\\or"
patternNameForContext (RewritesF _) = "\\rewrites"
patternNameForContext (StringLiteralF _) = "<string>"
patternNameForContext (CharLiteralF _) = "<char>"
patternNameForContext (TopF _) = "\\top"
patternNameForContext (VariableF (ElemVar variable)) =
    "element variable '" <> variableNameForContext (getElementVariable variable) <> "'"
patternNameForContext (InhabitantF _) = "\\inh"
patternNameForContext (VariableF (SetVar variable)) =
    "set variable '" <> variableNameForContext (getSetVariable variable) <> "'"

variableNameForContext :: Variable -> Text
variableNameForContext variable = getId (variableName variable)
