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
    evaluate,
    evaluateT,
    evaluateToList,
    indexedModule,
    verifiedModule,
    verifyPattern,
    runStep,
    runSMT,
    runSMTWithConfig,
) where

import Control.Monad.Catch (
    MonadMask,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Hedgehog
import qualified Kore.Attribute.Null as Attribute
import Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error (
    Error,
 )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools (
    build,
 )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import qualified Kore.IndexedModule.SortGraph as SortGraph
import Kore.Internal.InternalSet
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import qualified Kore.Internal.Symbol as Internal (
    Symbol,
 )
import Kore.Internal.TermLike
import Kore.Parser (
    parseKorePattern,
 )
import qualified Kore.Rewrite.Function.Memo as Memo
import qualified Kore.Rewrite.RewriteStep as Step
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern,
 )
import qualified Kore.Rewrite.Step as Step
import qualified Kore.Simplify.Condition as Simplifier.Condition
import Kore.Simplify.Data
import Kore.Simplify.InjSimplifier
import Kore.Simplify.OverloadSimplifier
import Kore.Simplify.Simplify
import qualified Kore.Simplify.SubstitutionSimplifier as SubstitutionSimplifier
import qualified Kore.Simplify.TermLike as TermLike
import Kore.Syntax.Definition (
    ModuleName,
    ParsedDefinition,
 )
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
import qualified Kore.Validate.PatternVerifier as PatternVerifier
import qualified Logic
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
        PatternVerifier.verifiedModuleContext verifiedModule
            & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers
    parsedPattern = externalize termLike

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build verifiedModule

testConditionSimplifier ::
    MonadSimplify simplifier => ConditionSimplifier simplifier
testConditionSimplifier =
    Simplifier.Condition.create SubstitutionSimplifier.substitutionSimplifier

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators verifiedModule

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

testEnv :: MonadSimplify simplifier => Env simplifier
testEnv =
    Env
        { metadataTools = testMetadataTools
        , simplifierCondition = testConditionSimplifier
        , simplifierAxioms = testEvaluators
        , memo = Memo.forgetful
        , injSimplifier = testInjSimplifier
        , overloadSimplifier = testOverloadSimplifier
        }

simplify :: TermLike RewritingVariableName -> IO [Pattern RewritingVariableName]
simplify =
    id
        . runNoSMT
        . runSimplifier testEnv
        . Logic.observeAllT
        . simplifyConditionalTerm SideCondition.top

evaluate ::
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    TermLike RewritingVariableName ->
    smt (OrPattern RewritingVariableName)
evaluate termLike =
    runSimplifier testEnv $ do
        TermLike.simplify SideCondition.top termLike

evaluateT ::
    MonadTrans t =>
    (MonadSMT smt, MonadLog smt, MonadProf smt, MonadMask smt) =>
    TermLike RewritingVariableName ->
    t smt (OrPattern RewritingVariableName)
evaluateT = lift . evaluate

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
