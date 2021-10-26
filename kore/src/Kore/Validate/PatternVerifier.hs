{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Validate.PatternVerifier (
    verifyPattern,
    verifyStandalonePattern,
    verifyNoPatterns,
    verifyAliasLeftPattern,
    verifyFreeVariables,
    withBuiltinVerifiers,
    module Kore.Validate.PatternVerifier.PatternVerifier,
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.Maybe
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (
    Text,
 )
import Kore.AST.Error
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    freeVariables,
    nullFreeVariables,
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
import Kore.Internal.TermLike (
    TermLikeF,
 )
import qualified Kore.Internal.TermLike as Internal
import Kore.Syntax as Syntax
import Kore.Syntax.Definition
import Kore.Unparser
import Kore.Validate (ValidatedPattern)
import qualified Kore.Validate as Validated
import Kore.Validate.Error
import Kore.Validate.PatternVerifier.PatternVerifier
import Kore.Validate.SortVerifier
import qualified Kore.Variables.Free as Variables
import Prelude.Kore
import Pretty (
    (<+>),
 )
import qualified Pretty

withBuiltinVerifiers :: Builtin.Verifiers -> Context -> Context
withBuiltinVerifiers verifiers context =
    context{patternVerifierHook = Builtin.patternVerifierHook verifiers}

{- | Verify the left-hand side of an alias definition.

The left-hand side must consist of the alias applied to a non-repeating sequence
of variables with the same sorts as the alias declaration.

The verified left-hand side is returned with the set of 'DeclaredVariables'. The
'DeclaredVariables' are used to verify the right-hand side of the alias
definition.

See also: 'uniqueDeclaredVariables', 'withDeclaredVariables'
-}
verifyAliasLeftPattern ::
    Alias ->
    [Sort] ->
    Application SymbolOrAlias (SomeVariable VariableName) ->
    PatternVerifier
        ( DeclaredVariables
        , Application SymbolOrAlias (SomeVariable VariableName)
        )
verifyAliasLeftPattern alias aliasSorts leftPattern = do
    koreFailWhen (declaredHead /= symbolOrAlias) aliasDeclarationMismatch
    let expect = expectVariable <$> applicationChildren leftPattern
    verified <- verifyPatternsWithSorts variableSort aliasSorts expect
    declaredVariables <- uniqueDeclaredVariables verified
    let verifiedLeftPattern = leftPattern{applicationChildren = verified}
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
    expectVariable ::
        SomeVariable VariableName ->
        PatternVerifier (SomeVariable VariableName)
    expectVariable var = do
        verifyVariableDeclaration var
        return var

{- | Verify that a Kore pattern is well-formed.

This includes verifying that:
- the pattern has the expected sort (if provided)
- the sorts of all subterms agree
- all variables are explicitly quantified
-}
verifyPattern ::
    -- | If present, represents the expected sort of the pattern.
    Maybe Sort ->
    ParsedPattern ->
    PatternVerifier ValidatedPattern
verifyPattern expectedSort korePattern = do
    verified <- Recursive.fold verifyBasePattern korePattern
    assertExpectedSort expectedSort (Validated.patternSort verified)
    return verified

{- | Verify a Kore pattern with implicitly-quantified variables.

@verifyStandalonePattern@ calls 'verifyPattern', but quantifies all free
variables of the pattern.

See also: 'verifyPattern', 'verifyFreeVariables', 'withDeclaredVariables'
-}
verifyStandalonePattern ::
    Maybe Sort ->
    ParsedPattern ->
    PatternVerifier ValidatedPattern
verifyStandalonePattern expectedSort korePattern = do
    declaredVariables <- verifyFreeVariables korePattern
    withDeclaredVariables
        declaredVariables
        (verifyPattern expectedSort korePattern)

{- | Fail if a Kore pattern is found.

@verifyNoPatterns@ is useful to 'traverse' sentence types with phantom pattern
type variables.
-}
verifyNoPatterns ::
    MonadError (Error VerifyError) m =>
    ParsedPattern ->
    m ValidatedPattern
verifyNoPatterns _ = koreFail "Unexpected pattern."

verifyBasePattern ::
    Base ParsedPattern (PatternVerifier ValidatedPattern) ->
    PatternVerifier ValidatedPattern
verifyBasePattern (_ :< patternF) =
    withLocationAndContext patternF (patternNameForContext patternF) $ do
        Context{patternVerifierHook} <- Reader.ask
        termLikeF <-
            case patternF of
                Syntax.AndF and' ->
                    Validated.AndF <$> verifyAnd and'
                Syntax.ApplicationF app -> verifyApplication app
                Syntax.BottomF bottom ->
                    Validated.BottomF <$> verifyBottom bottom
                Syntax.CeilF ceil' ->
                    Validated.CeilF <$> verifyCeil ceil'
                Syntax.DomainValueF dv -> verifyDomainValue dv
                Syntax.EqualsF equals' ->
                    Validated.EqualsF <$> verifyEquals equals'
                Syntax.ExistsF exists ->
                    Validated.ExistsF <$> verifyExists exists
                Syntax.FloorF floor' ->
                    Validated.FloorF <$> verifyFloor floor'
                Syntax.ForallF forall' ->
                    Validated.ForallF <$> verifyForall forall'
                Syntax.IffF iff ->
                    Validated.IffF <$> verifyIff iff
                Syntax.ImpliesF implies ->
                    Validated.ImpliesF <$> verifyImplies implies
                Syntax.InF in' ->
                    Validated.InF <$> verifyIn in'
                Syntax.MuF mu ->
                    Validated.MuF <$> verifyMu mu
                Syntax.NextF next ->
                    Validated.NextF <$> verifyNext next
                Syntax.NotF not' ->
                    Validated.NotF <$> verifyNot not'
                Syntax.NuF nu ->
                    Validated.NuF <$> verifyNu nu
                Syntax.OrF or' ->
                    Validated.OrF <$> verifyOr or'
                Syntax.RewritesF rewrites ->
                    Validated.RewritesF <$> verifyRewrites rewrites
                Syntax.StringLiteralF str ->
                    Validated.StringLiteralF <$> verifyStringLiteral str
                Syntax.TopF top ->
                    Validated.TopF <$> verifyTop top
                Syntax.VariableF (Const variable) ->
                    Validated.VariableF <$> verifyVariable variable
                Syntax.InhabitantF _ ->
                    koreFail "Unexpected pattern."
        let PatternVerifierHook{runPatternVerifierHook} = patternVerifierHook
        runPatternVerifierHook (synthesize termLikeF)

verifyPatternSort :: Sort -> PatternVerifier ()
verifyPatternSort patternSort = do
    Context{declaredSortVariables} <- Reader.ask
    _ <- verifySort lookupSortDeclaration declaredSortVariables patternSort
    return ()

verifyOperands ::
    Traversable operator =>
    (forall a. operator a -> Sort) ->
    operator (PatternVerifier ValidatedPattern) ->
    PatternVerifier (operator ValidatedPattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just patternSort
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (Validated.patternSort child)
            return child
    traverse verifyChildWithSort operator
{-# INLINE verifyOperands #-}

verifyAnd ::
    And Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (And Sort ValidatedPattern)
verifyAnd = verifyOperands andSort

verifyOr ::
    Or Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Or Sort ValidatedPattern)
verifyOr = verifyOperands orSort

verifyIff ::
    Iff Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Iff Sort ValidatedPattern)
verifyIff = verifyOperands iffSort

verifyImplies ::
    Implies Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Implies Sort ValidatedPattern)
verifyImplies = verifyOperands impliesSort

verifyBottom ::
    Bottom Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Bottom Sort ValidatedPattern)
verifyBottom = verifyOperands bottomSort

verifyTop ::
    Top Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Top Sort ValidatedPattern)
verifyTop = verifyOperands topSort

verifyNot ::
    Not Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Not Sort ValidatedPattern)
verifyNot = verifyOperands notSort

verifyRewrites ::
    Rewrites Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Rewrites Sort ValidatedPattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate ::
    Traversable predicate =>
    -- | Operand sort
    (forall a. predicate a -> Sort) ->
    -- | Result sort
    (forall a. predicate a -> Sort) ->
    predicate (PatternVerifier ValidatedPattern) ->
    PatternVerifier (predicate ValidatedPattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    verifyOperands operandSort predicate
{-# INLINE verifyPredicate #-}

verifyCeil ::
    Ceil Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Ceil Sort ValidatedPattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor ::
    Floor Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Floor Sort ValidatedPattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals ::
    Equals Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Equals Sort ValidatedPattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn ::
    In Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (In Sort ValidatedPattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext ::
    Next Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Next Sort ValidatedPattern)
verifyNext = verifyOperands nextSort

verifyPatternsWithSorts ::
    (child -> Sort) ->
    [Sort] ->
    [PatternVerifier child] ->
    PatternVerifier [child]
verifyPatternsWithSorts getChildSort sorts operands = do
    koreFailWhen
        (declaredOperandCount /= actualOperandCount)
        ( "Expected "
            ++ show declaredOperandCount
            ++ " operands, but got "
            ++ show actualOperandCount
            ++ "."
        )
    Monad.zipWithM
        ( \sort verify -> do
            verified <- verify
            assertExpectedSort (Just sort) (getChildSort verified)
            return verified
        )
        sorts
        operands
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplyAlias ::
    Application SymbolOrAlias (PatternVerifier ValidatedPattern) ->
    MaybeT
        PatternVerifier
        (Application (Internal.Alias ValidatedPattern) ValidatedPattern)
verifyApplyAlias application =
    lookupAlias symbolOrAlias >>= \alias -> Trans.lift $ do
        let verified = application{applicationSymbolOrAlias = alias}
            sorts = Internal.aliasSorts alias
        leftVariables <- getLeftVariables (Internal.aliasConstructor alias)
        traverse_ ensureChildIsDeclaredVarType $ zip leftVariables children
        verifyApplicationChildren Validated.patternSort verified sorts
  where
    Application
        { applicationSymbolOrAlias = symbolOrAlias
        , applicationChildren = children
        } = application

    getLeftVariables :: Id -> PatternVerifier [SomeVariable VariableName]
    getLeftVariables aliasId = do
        indexedModule <- Reader.asks indexedModule
        alias <- resolveAlias indexedModule aliasId
        pure . applicationChildren . sentenceAliasLeftPattern . snd $ alias

    -- If an alias was defined using an element variable, it can only take an
    -- argument that is an element variable.
    -- If it was defined using a set variable, we can use it with any argument.
    -- Otherwise, it is a verification error.
    ensureChildIsDeclaredVarType ::
        (SomeVariable VariableName, PatternVerifier ValidatedPattern) ->
        PatternVerifier ()
    ensureChildIsDeclaredVarType (var, mpat)
        | isElementVariable var = do
            pat <- mpat
            case pat of
                Validated.ElemVar_ _ -> pure ()
                _ ->
                    koreFail
                        "The alias was declared with an element variable, but its\
                        \ argument is not an element variable."
        | otherwise = pure ()

verifyApplySymbol ::
    (child -> Sort) ->
    Application SymbolOrAlias (PatternVerifier child) ->
    MaybeT PatternVerifier (Application Internal.Symbol child)
verifyApplySymbol getChildSort application =
    lookupSymbol symbolOrAlias >>= \symbol -> Trans.lift $ do
        let verified = application{applicationSymbolOrAlias = symbol}
            sorts = Internal.symbolSorts symbol
        verifyApplicationChildren getChildSort verified sorts
  where
    Application{applicationSymbolOrAlias = symbolOrAlias} = application

verifyApplicationChildren ::
    (child -> Sort) ->
    Application head (PatternVerifier child) ->
    ApplicationSorts ->
    PatternVerifier (Application head child)
verifyApplicationChildren getChildSort application sorts = do
    let operandSorts = applicationSortsOperands sorts
    verifiedChildren <- verifyChildren operandSorts children
    return application{applicationChildren = verifiedChildren}
  where
    verifyChildren = verifyPatternsWithSorts getChildSort
    Application{applicationChildren = children} = application

verifyApplication ::
    Application SymbolOrAlias (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Validated.PatternF VariableName ValidatedPattern)
verifyApplication application = do
    result <- verifyApplyAlias' <|> verifyApplySymbol' & runMaybeT
    maybe (koreFail . noHead $ symbolOrAlias) return result
  where
    symbolOrAlias = applicationSymbolOrAlias application
    verifyApplyAlias' =
        Validated.ApplyAliasF
            <$> verifyApplyAlias application
    verifyApplySymbol' =
        Validated.ApplySymbolF
            <$> verifyApplySymbol Validated.patternSort application

verifyBinder ::
    Traversable binder =>
    (forall a. binder a -> Sort) ->
    (forall a. binder a -> SomeVariable VariableName) ->
    binder (PatternVerifier ValidatedPattern) ->
    PatternVerifier (binder ValidatedPattern)
verifyBinder binderSort binderVariable = \binder -> do
    let variable = binderVariable binder
        patternSort = binderSort binder
    verifyVariableDeclaration variable
    verifyPatternSort patternSort
    let withQuantifiedVariable ctx@Context{declaredVariables} =
            ctx
                { declaredVariables =
                    addDeclaredVariable
                        variable
                        declaredVariables
                }
    Reader.local withQuantifiedVariable (verifyOperands binderSort binder)
{-# INLINE verifyBinder #-}

verifyExists ::
    Exists Sort VariableName (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Exists Sort VariableName ValidatedPattern)
verifyExists = verifyBinder existsSort (inject . existsVariable)

verifyForall ::
    Forall Sort VariableName (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Forall Sort VariableName ValidatedPattern)
verifyForall = verifyBinder forallSort (inject . forallVariable)

verifyMu ::
    Mu VariableName (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Mu VariableName ValidatedPattern)
verifyMu = verifyBinder muSort (inject . muVariable)
  where
    muSort = variableSort . muVariable

verifyNu ::
    Nu VariableName (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Nu VariableName ValidatedPattern)
verifyNu = verifyBinder nuSort (inject . nuVariable)
  where
    nuSort = variableSort . nuVariable

verifyVariable ::
    SomeVariable VariableName ->
    PatternVerifier (Const (SomeVariable VariableName) ValidatedPattern)
verifyVariable var = do
    declaredVariable <- lookupDeclaredVariable varName
    let declaredSort = variableSort declaredVariable
    koreFailWithLocationsWhen
        (varSort /= declaredSort)
        [var, declaredVariable]
        "The declared sort is different."
    return (Const var)
  where
    varName = variableName var
    varSort = variableSort var

verifyDomainValue ::
    DomainValue Sort (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Validated.PatternF VariableName ValidatedPattern)
verifyDomainValue domain = do
    let DomainValue{domainValueSort = patternSort} = domain
    verifyPatternSort patternSort
    verifySortHasDomainValues patternSort
    verified <- Validated.DomainValueF <$> sequence domain
    let freeVariables' :: FreeVariables VariableName =
            foldMap
                freeVariables
                (Validated.extractAttributes <$> verified)
    unless
        (nullFreeVariables freeVariables')
        (koreFail "Domain value must not contain free variables.")
    return verified

verifySortHasDomainValues :: Sort -> PatternVerifier ()
verifySortHasDomainValues patternSort = do
    Context{indexedModule} <- Reader.ask
    (sortAttrs, _) <- resolveSort indexedModule dvSortId
    koreFailWithLocationsWhen
        ( not
            . Attribute.HasDomainValues.getHasDomainValues
            $ Attribute.Sort.hasDomainValues sortAttrs
        )
        [patternSort]
        sortNeedsDomainValueAttributeMessage
  where
    dvSortId = case patternSort of
        SortVariableSort _ ->
            error "Unimplemented: domain values with variable sorts"
        SortActualSort SortActual{sortActualName} -> sortActualName

verifyStringLiteral ::
    Const StringLiteral (PatternVerifier ValidatedPattern) ->
    PatternVerifier (Const StringLiteral ValidatedPattern)
verifyStringLiteral = sequence

verifyVariableDeclaration ::
    SomeVariable VariableName -> PatternVerifier VerifySuccess
verifyVariableDeclaration variable = do
    Context{declaredSortVariables} <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        varSort
  where
    varSort = variableSort variable

verifyFreeVariables ::
    ParsedPattern ->
    PatternVerifier DeclaredVariables
verifyFreeVariables unifiedPattern =
    Monad.foldM
        addFreeVariable
        emptyDeclaredVariables
        $ Set.toList (Variables.freePureVariables unifiedPattern)

addFreeVariable ::
    DeclaredVariables ->
    SomeVariable VariableName ->
    PatternVerifier DeclaredVariables
addFreeVariable (getDeclaredVariables -> vars) var = do
    checkVariable var vars
    return . DeclaredVariables $ Map.insert (variableName var) var vars

checkVariable ::
    SomeVariable VariableName ->
    Map.Map (SomeVariableName VariableName) (SomeVariable VariableName) ->
    PatternVerifier VerifySuccess
checkVariable var vars =
    maybe verifySuccess inconsistent $
        Map.lookup (variableName var) vars
  where
    inconsistent v =
        koreFailWithLocations [v, var] $
            Pretty.renderText $
                Pretty.layoutCompact $
                    "Inconsistent free variable usage:"
                        <+> unparse v
                        <+> "and"
                        <+> unparse var
                        <> Pretty.dot

patternNameForContext :: PatternF VariableName p -> Text
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
    (Pretty.renderText . Pretty.layoutOneLine . Pretty.hsep)
        [ "\\exists"
        , Pretty.squotes (unparse $ variableName $ existsVariable exists)
        ]
patternNameForContext (FloorF _) = "\\floor"
patternNameForContext (ForallF forall) =
    (Pretty.renderText . Pretty.layoutOneLine . Pretty.hsep)
        [ "\\forall"
        , Pretty.squotes (unparse $ variableName $ forallVariable forall)
        ]
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
patternNameForContext (InhabitantF _) = "\\inh"
patternNameForContext (VariableF (Const someVariable)) =
    (Pretty.renderText . Pretty.layoutOneLine . Pretty.hsep)
        [ variableClass
        , Pretty.squotes (unparse $ variableName someVariable)
        ]
  where
    variableClass =
        case variableName someVariable of
            SomeVariableNameElement _ -> "element variable"
            SomeVariableNameSet _ -> "set variable"
