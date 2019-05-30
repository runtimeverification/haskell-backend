module Test.Kore.Builtin.Builtin
    ( mkPair
    , hpropUnparse
    , testMetadataTools
    , testEnv
    , testSubstitutionSimplifier
    , testTermLikeSimplifier
    , testEvaluators
    , testSymbolWithSolver
    , evaluate
    , evaluateT
    , evaluateToList
    , indexedModule
    , runStep
    , runSMT
    ) where

import qualified Hedgehog
import           Test.Tasty
                 ( TestTree )
import           Test.Tasty.HUnit
                 ( assertEqual, testCase )

import qualified Control.Lens as Lens
import qualified Control.Monad.Trans as Trans
import           Data.Function
                 ( (&) )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
import qualified Data.Set as Set
import           GHC.Stack
                 ( HasCallStack )

import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Symbol
import qualified Kore.Builtin as Builtin
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Pattern )
import           Kore.Internal.TermLike
import           Kore.Parser
                 ( parseKorePattern )
import           Kore.Step.Axiom.Data
import qualified Kore.Step.Result as Result
                 ( mergeResults )
import           Kore.Step.Rule
                 ( RewriteRule )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import qualified Kore.Step.Simplification.TermLike as TermLike
import qualified Kore.Step.Step as Step
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( unparseToString )
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Step.MockSimplifiers as Mock

mkPair
    :: Sort
    -> Sort
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
mkPair lSort rSort l r =
    mkApp (pairSort lSort rSort) (pairSymbol lSort rSort) [l, r]

-- | 'testSymbol' is useful for writing unit tests for symbols.
testSymbolWithSolver
    ::  ( HasCallStack
        , p ~ TermLike Variable
        , expanded ~ Pattern Variable
        )
    => (p -> SMT expanded)
    -- ^ evaluator function for the builtin
    -> String
    -- ^ test name
    -> Sort
    -- ^ symbol result sort
    -> SymbolOrAlias
    -- ^ symbol being tested
    -> [p]
    -- ^ arguments for symbol
    -> expanded
    -- ^ expected result
    -> TestTree
testSymbolWithSolver eval title resultSort symbol args expected =
    testCase title $ do
        actual <- runSMT eval'
        assertEqual "" expected actual
  where
    eval' = eval $ mkApp resultSort symbol args

-- -------------------------------------------------------------
-- * Evaluation

verify
    :: ParsedDefinition
    -> Either
        (Kore.Error.Error VerifyError)
        (Map
            ModuleName (VerifiedModule StepperAttributes Attribute.Axiom)
        )
verify = verifyAndIndexDefinition attrVerify Builtin.koreVerifiers
  where
    attrVerify = defaultAttributesVerification Proxy Proxy

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @kseq@ and @dotk@ are both functional and constructor.
constructorFunctions
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> VerifiedModule StepperAttributes Attribute.Axiom
constructorFunctions ixm =
    ixm
        { indexedModuleSymbolSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleSymbolSentences ixm)
        , indexedModuleAliasSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleAliasSentences ixm)
        , indexedModuleImports = recurseIntoImports <$> indexedModuleImports ixm
        }
  where
    constructorFunctions1 ident (atts, defn) =
        ( atts
            & lensConstructor Lens.<>~ Constructor isCons
            & lensFunctional Lens.<>~ Functional (isCons || isInj)
            & lensInjective Lens.<>~ Injective (isCons || isInj)
            & lensSortInjection Lens.<>~ SortInjection isInj
        , defn
        )
      where
        isInj = getId ident == "inj"
        isCons = Set.member (getId ident) (Set.fromList ["kseq", "dotk"])

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)

verifiedModules
    :: Map ModuleName (VerifiedModule StepperAttributes Attribute.Axiom)
verifiedModules =
    either (error . Kore.Error.printError) id (verify testDefinition)

verifiedModule :: VerifiedModule StepperAttributes Attribute.Axiom
Just verifiedModule = Map.lookup testModuleName verifiedModules

indexedModule :: KoreIndexedModule Attribute.Null Attribute.Null
indexedModule =
    verifiedModule
    & IndexedModule.eraseAttributes
    & IndexedModule.mapPatterns Builtin.externalizePattern

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build (constructorFunctions verifiedModule)

testSubstitutionSimplifier :: PredicateSimplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testMetadataTools

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators verifiedModule

testTermLikeSimplifier :: TermLikeSimplifier
testTermLikeSimplifier = Simplifier.create testMetadataTools testEvaluators

testEnv :: Env
testEnv = Env { metadataTools = testMetadataTools }

evaluate
    :: TermLike Variable
    -> SMT (Pattern Variable)
evaluate =
    evalSimplifier testEnv
    . TermLike.simplify
        testMetadataTools
        testSubstitutionSimplifier
        testEvaluators

evaluateT
    :: Trans.MonadTrans t
    => TermLike Variable
    -> t SMT (Pattern Variable)
evaluateT = Trans.lift . evaluate

evaluateToList
    :: TermLike Variable
    -> SMT [Pattern Variable]
evaluateToList =
    fmap MultiOr.extractPatterns
    . evalSimplifier testEnv
    . TermLike.simplifyToOr
        testMetadataTools
        testEvaluators
        testSubstitutionSimplifier

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig emptyLogger

runStep
    :: Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> SMT (Either UnificationOrSubstitutionError (OrPattern Variable))
runStep configuration axiom = do
    results <- runStepResult configuration axiom
    return (Step.gatherResults <$> results)

runStepResult
    :: Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> SMT (Either UnificationOrSubstitutionError (Step.Results Variable))
runStepResult configuration axiom = do
    results <-
        evalSimplifier testEnv
        $ Monad.Unify.runUnifier
        $ Step.applyRewriteRules
            testMetadataTools
            testSubstitutionSimplifier
            testTermLikeSimplifier
            testEvaluators
            (Step.UnificationProcedure Unification.unificationProcedure)
            [axiom]
            configuration
    return (Result.mergeResults <$> results)


-- | Test unparsing internalized patterns.
hpropUnparse
    :: Hedgehog.Gen (TermLike Variable)
    -- ^ Generate patterns with internal representations
    -> Hedgehog.Property
hpropUnparse gen = Hedgehog.property $ do
    builtin <- Hedgehog.forAll gen
    let syntax = unparseToString builtin
        expected = Builtin.externalizePattern builtin
    Right expected Hedgehog.=== parseKorePattern "<test>" syntax
