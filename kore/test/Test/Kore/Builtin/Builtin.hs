module Test.Kore.Builtin.Builtin
    ( mkPair
    , emptyNormalizedSet
    , expectHook
    , hpropUnparse
    , testMetadataTools
    , testEnv
    , testConditionSimplifier
    , testTermLikeSimplifier
    , testEvaluators
    , testSymbolWithSolver
    , simplify
    , evaluate
    , evaluateT
    , evaluateToList
    , indexedModule
    , verifiedModule
    , verifyPattern
    , runStep
    , runSMT
    ) where

import Prelude.Kore

import qualified Hedgehog
import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( assertEqual
    , testCase
    )

import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )

import Kore.ASTVerifier.DefinitionVerifier
import Kore.ASTVerifier.Error
    ( VerifyError
    )
import Kore.ASTVerifier.PatternVerifier
    ( runPatternVerifier
    , verifyStandalonePattern
    )
import qualified Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Null as Attribute
import Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Domain.Builtin
    ( NormalizedAc
    , NormalizedSet
    , emptyNormalizedAc
    )
import Kore.Error
    ( Error
    )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import qualified Kore.IndexedModule.SortGraph as SortGraph
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Symbol as Internal
    ( Symbol
    )
import Kore.Internal.TermLike
import Kore.Parser
    ( parseKorePattern
    )
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.Function.Memo as Memo
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.RulePattern
    ( RewriteRule
    , RulePattern
    )
import qualified Kore.Step.Simplification.Condition as Simplifier.Condition
import Kore.Step.Simplification.Data
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.OverloadSimplifier
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import qualified Kore.Step.Simplification.TermLike as TermLike
import qualified Kore.Step.Step as Step
import Kore.Syntax.Definition
    ( ModuleName
    , ParsedDefinition
    )
import qualified Kore.Unification.Procedure as Unification
import Kore.Unification.UnificationProcedure
import Kore.Unparser
    ( unparseToString
    )
import Log
    ( MonadLog
    )
import qualified Logic
import SMT
    ( MonadSMT
    , SMT
    )

import Test.Kore.Builtin.Definition
import Test.SMT

emptyNormalizedSet :: NormalizedAc NormalizedSet key child
emptyNormalizedSet = emptyNormalizedAc

mkPair
    :: Sort
    -> Sort
    -> TermLike VariableName
    -> TermLike VariableName
    -> TermLike VariableName
mkPair lSort rSort l r = mkApplySymbol (pairSymbol lSort rSort) [l, r]

-- | 'testSymbol' is useful for writing unit tests for symbols.
testSymbolWithSolver
    ::  ( HasCallStack
        , p ~ TermLike VariableName
        , expanded ~ Pattern VariableName
        )
    => (p -> SMT expanded)
    -- ^ evaluator function for the builtin
    -> String
    -- ^ test name
    -> Internal.Symbol
    -- ^ symbol being tested
    -> [p]
    -- ^ arguments for symbol
    -> expanded
    -- ^ expected result
    -> TestTree
testSymbolWithSolver eval title symbol args expected =
    testCase title $ do
        actual <- runSMT eval'
        assertEqual "" expected actual
  where
    eval' = eval $ mkApplySymbol symbol args

expectHook :: Internal.Symbol -> Text
expectHook =
    fromMaybe (error "Expected hook attribute")
    . Attribute.getHook . Attribute.hook . symbolAttributes

-- -------------------------------------------------------------
-- * Evaluation

verify
    :: ParsedDefinition
    -> Either
        (Kore.Error.Error VerifyError)
        (Map ModuleName (VerifiedModule StepperAttributes))
verify = verifyAndIndexDefinition Builtin.koreVerifiers

verifiedModules
    :: Map ModuleName (VerifiedModule StepperAttributes)
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
    & IndexedModule.mapPatterns Builtin.externalize

verifyPattern
    :: Maybe Sort  -- ^ Expected sort
    -> TermLike VariableName
    -> Either (Error VerifyError) (TermLike VariableName)
verifyPattern expectedSort termLike =
    runPatternVerifier context
    $ verifyStandalonePattern expectedSort parsedPattern
  where
    context =
        PatternVerifier.verifiedModuleContext verifiedModule
        & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers
    parsedPattern = Builtin.externalize termLike

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build verifiedModule

testConditionSimplifier
    :: MonadSimplify simplifier => ConditionSimplifier simplifier
testConditionSimplifier =
    Simplifier.Condition.create SubstitutionSimplifier.substitutionSimplifier

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators verifiedModule

testTermLikeSimplifier :: TermLikeSimplifier
testTermLikeSimplifier = Simplifier.create

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
        , simplifierTermLike = testTermLikeSimplifier
        , simplifierCondition = testConditionSimplifier
        , simplifierAxioms = testEvaluators
        , memo = Memo.forgetful
        , injSimplifier = testInjSimplifier
        , overloadSimplifier = testOverloadSimplifier
        }

simplify :: TermLike VariableName -> IO [Pattern VariableName]
simplify =
    id
    . runNoSMT
    . runSimplifier testEnv
    . Logic.observeAllT
    . simplifyConditionalTerm SideCondition.top

evaluate
    :: (MonadSMT smt, MonadLog smt)
    => TermLike VariableName
    -> smt (Pattern VariableName)
evaluate termLike =
    runSimplifier testEnv $ do
        patterns <- TermLike.simplifyToOr SideCondition.top termLike
        pure (OrPattern.toPattern patterns)

evaluateT
    :: MonadTrans t
    => (MonadSMT smt, MonadLog smt)
    => TermLike VariableName
    -> t smt (Pattern VariableName)
evaluateT = lift . evaluate

evaluateToList :: TermLike VariableName -> SMT [Pattern VariableName]
evaluateToList =
    fmap MultiOr.extractPatterns
    . runSimplifier testEnv
    . TermLike.simplifyToOr SideCondition.top

runStep
    :: Pattern VariableName
    -- ^ configuration
    -> RewriteRule VariableName
    -- ^ axiom
    -> SMT (OrPattern VariableName)
runStep configuration axiom = do
    results <- runStepResult configuration axiom
    return (Step.gatherResults results)

runStepResult
    :: Pattern VariableName
    -- ^ configuration
    -> RewriteRule VariableName
    -- ^ axiom
    -> SMT (Step.Results RulePattern VariableName)
runStepResult configuration axiom =
    Step.applyRewriteRulesParallel
        unificationProcedure
        [mkRewritingRule axiom]
        configuration
    & runSimplifier testEnv

unificationProcedure
    :: MonadSimplify simplifier
    => UnificationProcedure simplifier
unificationProcedure = Unification.unificationProcedure

-- | Test unparsing internalized patterns.
hpropUnparse
    :: Hedgehog.Gen (TermLike VariableName)
    -- ^ Generate patterns with internal representations
    -> Hedgehog.Property
hpropUnparse gen = Hedgehog.property $ do
    builtin <- Hedgehog.forAll gen
    let syntax = unparseToString builtin
        expected = Builtin.externalize builtin
    Right expected Hedgehog.=== parseKorePattern "<test>" syntax
