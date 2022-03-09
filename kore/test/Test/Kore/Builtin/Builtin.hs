module Test.Kore.Builtin.Builtin (
    mkPair,
    emptyNormalizedSet,
    expectHook,
    hpropUnparse,
    testMetadataTools,
    testEnv,
    testConditionSimplifier,
    testEvaluators,
    testSymbolWithoutSolver,
    simplify,
    evaluateTerm,
    evaluateTermT,
    evaluatePredicate,
    evaluatePredicateT,
    evaluateExpectTopK,
    evaluateToList,
    indexedModule,
    verifiedModule,
    verifyPattern,
    runStep,
    runSMT,
    runSMTWithConfig,
    unifyEq,
    simplifyCondition',
    simplifyPattern,
) where

import Control.Monad ((>=>))
import Control.Monad.Catch (
    MonadMask,
 )
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Text (
    Text,
 )
import Hedgehog qualified
import Kore.Attribute.Null qualified as Attribute
import Kore.Attribute.Symbol as Attribute
import Kore.Builtin qualified as Builtin
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Error (
    Error,
 )
import Kore.Error qualified
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.IndexedModule.MetadataToolsBuilder qualified as MetadataTools (
    build,
 )
import Kore.IndexedModule.OverloadGraph qualified as OverloadGraph
import Kore.IndexedModule.SortGraph qualified as SortGraph
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.InternalSet
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (Predicate)
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.Symbol qualified as Internal (
    Symbol,
 )
import Kore.Internal.TermLike
import Kore.Parser (
    parseKorePattern,
 )
import Kore.Rewrite.Function.Memo qualified as Memo
import Kore.Rewrite.RewriteStep qualified as Step
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern,
 )
import Kore.Rewrite.Step qualified as Step
import Kore.Simplify.AndTerms (termUnification)
import Kore.Simplify.Condition qualified as Simplifier.Condition
import Kore.Simplify.Data hiding (simplifyPattern)
import Kore.Simplify.InjSimplifier
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.OverloadSimplifier
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Simplify.Simplify hiding (simplifyPattern)
import Kore.Simplify.SubstitutionSimplifier qualified as SubstitutionSimplifier
import Kore.Simplify.TermLike qualified as TermLike
import Kore.Syntax.Definition (
    ModuleName,
    ParsedDefinition,
 )
import Kore.Unification.UnifierT (evalEnvUnifierT)
import Kore.Unparser (
    unparseToText,
 )
import Kore.Validate.DefinitionVerifier
import Kore.Validate.Error (
    VerifyError,
 )
import Kore.Validate.PatternVerifier (
    runPatternVerifier,
    verifyStandalonePattern,
 )
import Kore.Validate.PatternVerifier qualified as PatternVerifier
import Logic qualified
import Prelude.Kore
import SMT (
    NoSMT,
 )
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.External
import Test.SMT
import Test.Tasty (
    TestTree,
 )
import Test.Tasty.HUnit (
    assertEqual,
    testCase,
 )

emptyNormalizedSet :: NormalizedAc NormalizedSet key child
emptyNormalizedSet = emptyNormalizedAc

mkPair ::
    Sort ->
    Sort ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
mkPair lSort rSort l r = mkApplySymbol (pairSymbol lSort rSort) [l, r]

-- | 'testSymbol' is useful for writing unit tests for symbols.
testSymbolWithoutSolver ::
    forall p expanded.
    ( HasCallStack
    , p ~ TermLike RewritingVariableName
    , expanded ~ OrPattern RewritingVariableName
    ) =>
    -- | evaluator function for the builtin
    (p -> NoSMT expanded) ->
    -- | test name
    String ->
    -- | symbol being tested
    Internal.Symbol ->
    -- | arguments for symbol
    [p] ->
    -- | expected result
    expanded ->
    TestTree
testSymbolWithoutSolver eval title symbol args expected =
    testCase title $ do
        actual <- runNoSMT eval'
        assertEqual "" expected actual
  where
    eval' = eval $ mkApplySymbol symbol args

expectHook :: Internal.Symbol -> Text
expectHook =
    fromMaybe (error "Expected hook attribute")
        . Attribute.getHook
        . Attribute.hook
        . symbolAttributes

-- -------------------------------------------------------------

-- * Evaluation

verify ::
    ParsedDefinition ->
    Either
        (Kore.Error.Error VerifyError)
        (Map ModuleName (VerifiedModule StepperAttributes))
verify = verifyAndIndexDefinition Builtin.koreVerifiers

verifiedModules ::
    Map ModuleName (VerifiedModule StepperAttributes)
verifiedModules =
    either (error . Kore.Error.printError) id (verify testDefinition)

verifiedModule :: VerifiedModule Attribute.Symbol
verifiedModule =
    fromMaybe
        (error $ "Missing module: " ++ show testModuleName)
        (Map.lookup testModuleName verifiedModules)

indexedModule :: KoreIndexedModule Attribute.Symbol Attribute.Null
indexedModule =
    verifiedModule
        & IndexedModule.eraseAxiomAttributes
        & IndexedModule.mapPatterns externalize

verifyPattern ::
    -- | Expected sort
    Maybe Sort ->
    TermLike VariableName ->
    Either (Error VerifyError) (TermLike VariableName)
verifyPattern expectedSort termLike =
    runPatternVerifier context $
        verifyStandalonePattern expectedSort parsedPattern
  where
    context =
        PatternVerifier.verifiedModuleContext (indexedModuleSyntax verifiedModule)
            & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers
    parsedPattern = externalize termLike

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build verifiedModule

testConditionSimplifier ::
    MonadSimplify simplifier => ConditionSimplifier simplifier
testConditionSimplifier =
    Simplifier.Condition.create SubstitutionSimplifier.substitutionSimplifier

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators $ indexedModuleSyntax verifiedModule

testSortGraph :: SortGraph.SortGraph
testSortGraph = SortGraph.fromIndexedModule verifiedModule

testOverloadGraph :: OverloadGraph.OverloadGraph
testOverloadGraph =
    OverloadGraph.fromIndexedModule verifiedModule

testInjSimplifier :: InjSimplifier
testInjSimplifier = mkInjSimplifier testSortGraph

testOverloadSimplifier :: OverloadSimplifier
testOverloadSimplifier =
    mkOverloadSimplifier testOverloadGraph testInjSimplifier

-- TODO(Ana): if needed, create copy with experimental simplifier
-- enabled
testEnv :: MonadSimplify simplifier => Env simplifier
testEnv =
    Env
        { metadataTools = testMetadataTools
        , simplifierCondition = testConditionSimplifier
        , simplifierAxioms = testEvaluators
        , memo = Memo.forgetful
        , injSimplifier = testInjSimplifier
        , overloadSimplifier = testOverloadSimplifier
        , simplifierXSwitch = DisabledSimplifierX
        }

simplify :: TermLike RewritingVariableName -> IO [Pattern RewritingVariableName]
simplify =
    id
        . runNoSMT
        . runSimplifier testEnv
        . Logic.observeAllT
        . (simplifyTerm SideCondition.top >=> Logic.scatter)

evaluateTerm ::
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    TermLike RewritingVariableName ->
    smt (OrPattern RewritingVariableName)
evaluateTerm termLike =
    runSimplifier testEnv $
        Pattern.simplify (Pattern.fromTermLike termLike)

evaluatePredicate ::
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    Predicate RewritingVariableName ->
    smt (OrPattern RewritingVariableName)
evaluatePredicate predicate =
    runSimplifier testEnv $
        Pattern.simplify
            ( Pattern.fromCondition kSort
                . Condition.fromPredicate
                $ predicate
            )

evaluateTermT ::
    MonadTrans t =>
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    TermLike RewritingVariableName ->
    t smt (OrPattern RewritingVariableName)
evaluateTermT = lift . evaluateTerm

evaluatePredicateT ::
    MonadTrans t =>
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    Predicate RewritingVariableName ->
    t smt (OrPattern RewritingVariableName)
evaluatePredicateT = lift . evaluatePredicate

evaluateExpectTopK ::
    HasCallStack =>
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    TermLike RewritingVariableName ->
    Hedgehog.PropertyT smt ()
evaluateExpectTopK termLike = do
    actual <- evaluateTermT termLike
    OrPattern.topOf kSort Hedgehog.=== actual

evaluateToList ::
    TermLike RewritingVariableName ->
    NoSMT [Pattern RewritingVariableName]
evaluateToList =
    fmap toList
        . runSimplifier testEnv
        . TermLike.simplify SideCondition.top

runStep ::
    -- | configuration
    Pattern RewritingVariableName ->
    -- | axiom
    RewriteRule RewritingVariableName ->
    NoSMT (OrPattern RewritingVariableName)
runStep configuration axiom = do
    results <- runStepResult configuration axiom
    return $ Step.gatherResults results

runStepResult ::
    -- | configuration
    Pattern RewritingVariableName ->
    -- | axiom
    RewriteRule RewritingVariableName ->
    NoSMT (Step.Results (RulePattern RewritingVariableName))
runStepResult configuration axiom =
    Step.applyRewriteRulesParallel
        [axiom]
        configuration
        & runSimplifier testEnv

-- | Test unparsing internalized patterns.
hpropUnparse ::
    -- | Generate patterns with internal representations
    Hedgehog.Gen (TermLike VariableName) ->
    Hedgehog.Property
hpropUnparse gen = Hedgehog.property $ do
    builtin <- Hedgehog.forAll gen
    let syntax = unparseToText builtin
        expected = externalize builtin
    Right expected Hedgehog.=== parseKorePattern "<test>" syntax

unifyEq ::
    Text ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO [Maybe (Pattern RewritingVariableName)]
unifyEq eqKey term1 term2 =
    unify matched
        & runMaybeT
        & evalEnvUnifierT Not.notSimplifier
        & runSimplifierBranch testEnv
        & runNoSMT
  where
    unify Nothing = empty
    unify (Just unifyData) =
        Builtin.unifyEq
            (termUnification Not.notSimplifier)
            Not.notSimplifier
            unifyData
            & lift

    matched =
        Builtin.matchUnifyEq eqKey term1 term2

simplifyCondition' ::
    Condition RewritingVariableName ->
    IO [Condition RewritingVariableName]
simplifyCondition' condition =
    simplifyCondition SideCondition.top condition
        & runSimplifierBranch testEnv
        & runNoSMT

simplifyPattern ::
    Pattern RewritingVariableName ->
    IO [Pattern RewritingVariableName]
simplifyPattern pattern1 =
    Pattern.simplify pattern1
        & runSimplifier testEnv
        & runNoSMT
        & fmap OrPattern.toPatterns
