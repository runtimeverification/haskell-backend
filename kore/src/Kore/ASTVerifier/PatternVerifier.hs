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
    , withBuiltinVerifiers
    , module Kore.ASTVerifier.PatternVerifier.PatternVerifier
    ) where

import Prelude.Kore

import Control.Applicative
import qualified Control.Monad as Monad
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import Data.Function
    ( (&)
    )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( (<+>)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Text.Prettyprint.Doc.Render.Text
    ( renderStrict
    )

import Kore.AST.Error
import Kore.ASTVerifier.Error
import Kore.ASTVerifier.PatternVerifier.PatternVerifier
import Kore.ASTVerifier.SortVerifier
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , freeVariables
    )
import qualified Kore.Attribute.Sort as Attribute.Sort
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import Kore.Attribute.Synthetic
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.Error
import Kore.IndexedModule.Resolvers
import qualified Kore.Internal.Alias as Internal
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.Symbol as Internal
import Kore.Internal.TermLike
    ( TermLikeF
    )
import qualified Kore.Internal.TermLike as Internal
import Kore.Parser
    ( ParsedPattern
    )
import Kore.Syntax as Syntax
import Kore.Syntax.Definition
import Kore.Unparser
import qualified Kore.Variables.Free as Variables
import Kore.Variables.UnifiedVariable
import qualified Kore.Verified as Verified

withBuiltinVerifiers :: Builtin.Verifiers -> Context -> Context
withBuiltinVerifiers verifiers context =
    context { patternVerifierHook = Builtin.patternVerifierHook verifiers }

{- | Verify the left-hand side of an alias definition.

The left-hand side must consist of the alias applied to a non-repeating sequence
of variables with the same sorts as the alias declaration.

The verified left-hand side is returned with the set of 'DeclaredVariables'. The
'DeclaredVariables' are used to verify the right-hand side of the alias
definition.

See also: 'uniqueDeclaredVariables', 'withDeclaredVariables'

 -}
verifyAliasLeftPattern
    :: Alias
    -> [Sort]
    -> Application SymbolOrAlias (UnifiedVariable Variable)
    -> PatternVerifier
        ( DeclaredVariables
        , Application SymbolOrAlias (UnifiedVariable Variable)
        )
verifyAliasLeftPattern alias aliasSorts leftPattern = do
    koreFailWhen (declaredHead /= symbolOrAlias) aliasDeclarationMismatch
    let expect = expectVariable <$> applicationChildren leftPattern
    verified <- verifyPatternsWithSorts unifiedVariableSort aliasSorts expect
    declaredVariables <- uniqueDeclaredVariables verified
    let verifiedLeftPattern = leftPattern { applicationChildren = verified }
    return (declaredVariables, verifiedLeftPattern)
  where
    symbolOrAlias = applicationSymbolOrAlias leftPattern
    declaredHead =
        SymbolOrAlias
            { symbolOrAliasConstructor = aliasConstructor alias
            , symbolOrAliasParams = SortVariableSort <$> aliasParams alias
            }
    aliasDeclarationMismatch =
        (show . Pretty.vsep)
            [ "Alias left-hand side:"
            , Pretty.indent 4 $ unparse symbolOrAlias
            , "does not match declaration:"
            , Pretty.indent 4 $ unparse alias
            ]
    expectVariable
        :: UnifiedVariable Variable
        -> PatternVerifier (UnifiedVariable Variable)
    expectVariable var = do
        verifyVariableDeclaration var
        return var

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
    verified <- Recursive.fold verifyBasePattern korePattern
    assertExpectedSort expectedSort (Internal.termLikeSort verified)
    return verified

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

verifyBasePattern
    :: Base ParsedPattern (PatternVerifier Verified.Pattern)
    -> PatternVerifier Verified.Pattern
verifyBasePattern (_ :< patternF) =
    withLocationAndContext patternF (patternNameForContext patternF) $ do
    Context { patternVerifierHook } <- Reader.ask
    termLikeF <-
        case patternF of
            Syntax.AndF and' ->
                Internal.AndF <$> verifyAnd and'
            Syntax.ApplicationF app -> verifyApplication app
            Syntax.BottomF bottom ->
                Internal.BottomF <$> verifyBottom bottom
            Syntax.CeilF ceil' ->
                Internal.CeilF <$> verifyCeil ceil'
            Syntax.DomainValueF dv -> verifyDomainValue dv
            Syntax.EqualsF equals' ->
                Internal.EqualsF <$> verifyEquals equals'
            Syntax.ExistsF exists ->
                Internal.ExistsF <$> verifyExists exists
            Syntax.FloorF floor' ->
                Internal.FloorF <$> verifyFloor floor'
            Syntax.ForallF forall' ->
                Internal.ForallF <$> verifyForall forall'
            Syntax.IffF iff ->
                Internal.IffF <$> verifyIff iff
            Syntax.ImpliesF implies ->
                Internal.ImpliesF <$> verifyImplies implies
            Syntax.InF in' ->
                Internal.InF <$> verifyIn in'
            Syntax.MuF mu ->
                Internal.MuF <$> verifyMu mu
            Syntax.NextF next ->
                Internal.NextF <$> verifyNext next
            Syntax.NotF not' ->
                Internal.NotF <$> verifyNot not'
            Syntax.NuF nu ->
                Internal.NuF <$> verifyNu nu
            Syntax.OrF or' ->
                Internal.OrF <$> verifyOr or'
            Syntax.RewritesF rewrites ->
                Internal.RewritesF <$> verifyRewrites rewrites
            Syntax.StringLiteralF str ->
                Internal.StringLiteralF <$> verifyStringLiteral str
            Syntax.TopF top ->
                Internal.TopF <$> verifyTop top
            Syntax.VariableF (Const variable) ->
                Internal.VariableF <$> verifyVariable variable
            Syntax.InhabitantF _ ->
                koreFail "Unexpected pattern."
    let PatternVerifierHook { runPatternVerifierHook } = patternVerifierHook
    runPatternVerifierHook (synthesize termLikeF)

verifyPatternSort :: Sort -> PatternVerifier ()
verifyPatternSort patternSort = do
    Context { declaredSortVariables } <- Reader.ask
    _ <- verifySort lookupSortDeclaration declaredSortVariables patternSort
    return ()

verifyOperands
    :: Traversable operator
    => (forall a. operator a -> Sort)
    -> operator (PatternVerifier Verified.Pattern)
    -> PatternVerifier (operator Verified.Pattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just patternSort
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (Internal.termLikeSort child)
            return child
    traverse verifyChildWithSort operator
{-# INLINE verifyOperands #-}

verifyAnd
    :: And Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (And Sort Verified.Pattern)
verifyAnd = verifyOperands andSort

verifyOr
    :: Or Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Or Sort Verified.Pattern)
verifyOr = verifyOperands orSort

verifyIff
    :: Iff Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Iff Sort Verified.Pattern)
verifyIff = verifyOperands iffSort

verifyImplies
    :: Implies Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Implies Sort Verified.Pattern)
verifyImplies = verifyOperands impliesSort

verifyBottom
    :: Bottom Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Bottom Sort Verified.Pattern)
verifyBottom = verifyOperands bottomSort

verifyTop
    :: Top Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Top Sort Verified.Pattern)
verifyTop = verifyOperands topSort

verifyNot
    :: Not Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Not Sort Verified.Pattern)
verifyNot = verifyOperands notSort

verifyRewrites
    :: Rewrites Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Rewrites Sort Verified.Pattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate
    :: Traversable predicate
    => (forall a. predicate a -> Sort)  -- ^ Operand sort
    -> (forall a. predicate a -> Sort)  -- ^ Result sort
    -> predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (predicate Verified.Pattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    verifyOperands operandSort predicate
{-# INLINE verifyPredicate #-}

verifyCeil
    :: Ceil Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Ceil Sort Verified.Pattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor
    :: Floor Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Floor Sort Verified.Pattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals
    :: Equals Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Equals Sort Verified.Pattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn
    :: In Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (In Sort Verified.Pattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext
    :: Next Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Next Sort Verified.Pattern)
verifyNext = verifyOperands nextSort

verifyPatternsWithSorts
    :: (child -> Sort)
    -> [Sort]
    -> [PatternVerifier child]
    -> PatternVerifier [child]
verifyPatternsWithSorts getChildSort sorts operands = do
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
            assertExpectedSort (Just sort) (getChildSort verified)
            return verified
        )
        sorts
        operands
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplyAlias
    ::  Application SymbolOrAlias (PatternVerifier Verified.Pattern)
    ->  MaybeT PatternVerifier
            (Application (Internal.Alias Verified.Pattern) Verified.Pattern)
verifyApplyAlias application =
    lookupAlias symbolOrAlias >>= \alias -> Trans.lift $ do
    let verified = application { applicationSymbolOrAlias = alias }
        sorts = Internal.aliasSorts alias
    leftVariables <- getLeftVariables (Internal.aliasConstructor alias)
    Foldable.traverse_ ensureChildIsDeclaredVarType $ zip leftVariables children
    verifyApplicationChildren Internal.termLikeSort verified sorts
  where
    Application
        { applicationSymbolOrAlias = symbolOrAlias
        , applicationChildren      = children
        } = application

    getLeftVariables :: Id -> PatternVerifier [UnifiedVariable Variable]
    getLeftVariables aliasId = do
        indexedModule <- Reader.asks indexedModule
        alias <- resolveAlias indexedModule aliasId
        pure . applicationChildren . sentenceAliasLeftPattern . snd $ alias

    -- If an alias was defined using an element variable, it can only take an
    -- argument that is an element variable.
    -- If it was defined using a set variable, we can use it with any argument.
    -- Otherwise, it is a verification error.
    ensureChildIsDeclaredVarType
        :: (UnifiedVariable Variable, PatternVerifier Verified.Pattern)
        -> PatternVerifier ()
    ensureChildIsDeclaredVarType (var, mpat) = do
        pat <- mpat
        case (var, pat) of
            (ElemVar _, Internal.ElemVar_ _) -> pure ()
            (SetVar  _, _) -> pure ()
            _ ->
                koreFail
                    "The alias was declared with an element variable, but its\
                    \argument is not an element variable."

verifyApplySymbol
    :: (child -> Sort)
    -> Application SymbolOrAlias (PatternVerifier child)
    -> MaybeT PatternVerifier (Application Internal.Symbol child)
verifyApplySymbol getChildSort application =
    lookupSymbol symbolOrAlias >>= \symbol -> Trans.lift $ do
    let verified = application { applicationSymbolOrAlias = symbol }
        sorts = Internal.symbolSorts symbol
    verifyApplicationChildren getChildSort verified sorts
  where
    Application { applicationSymbolOrAlias = symbolOrAlias } = application

verifyApplicationChildren
    :: (child -> Sort)
    -> Application head (PatternVerifier child)
    -> ApplicationSorts
    -> PatternVerifier (Application head child)
verifyApplicationChildren getChildSort application sorts = do
    let operandSorts = applicationSortsOperands sorts
    verifiedChildren <- verifyChildren operandSorts children
    return application { applicationChildren = verifiedChildren }
  where
    verifyChildren = verifyPatternsWithSorts getChildSort
    Application { applicationChildren = children } = application

verifyApplication
    ::  Application SymbolOrAlias (PatternVerifier Verified.Pattern)
    ->  PatternVerifier (TermLikeF Variable Verified.Pattern)
verifyApplication application = do
    result <- verifyApplyAlias' <|> verifyApplySymbol' & runMaybeT
    maybe (koreFail . noHead $ symbolOrAlias) return result
  where
    symbolOrAlias = applicationSymbolOrAlias application
    verifyApplyAlias' =
        Internal.ApplyAliasF
        <$> verifyApplyAlias application
    verifyApplySymbol' =
        Internal.ApplySymbolF
        <$> verifyApplySymbol Internal.termLikeSort application

verifyBinder
    :: Traversable binder
    => (forall a. binder a -> Sort)
    -> (forall a. binder a -> UnifiedVariable Variable)
    -> binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (binder Verified.Pattern)
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
    :: Exists Sort Variable (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Exists Sort Variable Verified.Pattern)
verifyExists = verifyBinder existsSort (ElemVar . existsVariable)

verifyForall
    :: Forall Sort Variable (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Forall Sort Variable Verified.Pattern)
verifyForall = verifyBinder forallSort (ElemVar . forallVariable)

verifyMu
    :: Mu Variable (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Mu Variable Verified.Pattern)
verifyMu = verifyBinder muSort (SetVar . muVariable)
  where
    muSort = variableSort . getSetVariable . muVariable

verifyNu
    :: Nu Variable (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Nu Variable Verified.Pattern)
verifyNu = verifyBinder nuSort (SetVar . nuVariable)
  where
    nuSort = variableSort . getSetVariable . nuVariable

verifyVariable
    :: UnifiedVariable Variable
    -> PatternVerifier (Const (UnifiedVariable Variable) Verified.Pattern)
verifyVariable var = do
    declaredVariable <- lookupDeclaredVariable varName
    let declaredSort = foldMapVariable variableSort declaredVariable
    koreFailWithLocationsWhen
        (varSort /= declaredSort)
        [ var, declaredVariable ]
        "The declared sort is different."
    return (Const var)
  where
    varName = foldMapVariable variableName var
    varSort = foldMapVariable variableSort var

verifyDomainValue
    :: DomainValue Sort (PatternVerifier Verified.Pattern)
    -> PatternVerifier (TermLikeF Variable Verified.Pattern)
verifyDomainValue domain = do
    let DomainValue { domainValueSort = patternSort } = domain
    verifyPatternSort patternSort
    verifySortHasDomainValues patternSort
    verified <- Internal.DomainValueF <$> sequence domain
    let freeVariables' :: FreeVariables Variable =
            foldMap freeVariables
                (Internal.extractAttributes <$> verified)
    Monad.unless (null freeVariables')
        (koreFail "Domain value must not contain free variables.")
    return verified

verifySortHasDomainValues :: Sort -> PatternVerifier ()
verifySortHasDomainValues patternSort = do
    Context { indexedModule } <- Reader.ask
    (sortAttrs, _) <- resolveSort indexedModule dvSortId
    koreFailWithLocationsWhen
        (not
            . Attribute.HasDomainValues.getHasDomainValues
            $ Attribute.Sort.hasDomainValues sortAttrs
        )
        [patternSort]
        sortNeedsDomainValueAttributeMessage
  where
    dvSortId = case patternSort of
        SortVariableSort _ ->
            error "Unimplemented: domain values with variable sorts"
        SortActualSort SortActual {sortActualName} -> sortActualName

verifyStringLiteral
    :: Const StringLiteral (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Const StringLiteral Verified.Pattern)
verifyStringLiteral = sequence

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
patternNameForContext (TopF _) = "\\top"
patternNameForContext (VariableF (Const (ElemVar variable))) =
    "element variable '" <> variableNameForContext (getElementVariable variable) <> "'"
patternNameForContext (InhabitantF _) = "\\inh"
patternNameForContext (VariableF (Const (SetVar variable))) =
    "set variable '" <> variableNameForContext (getSetVariable variable) <> "'"

variableNameForContext :: Variable -> Text
variableNameForContext variable = getId (variableName variable)
