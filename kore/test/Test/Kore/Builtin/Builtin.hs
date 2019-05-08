module Test.Kore.Builtin.Builtin where

import qualified Hedgehog
import           Test.Tasty
                 ( TestTree )
import           Test.Tasty.HUnit
                 ( assertEqual )

import           Control.Concurrent.MVar
                 ( MVar )
import qualified Control.Lens as Lens
import           Control.Monad.Reader
                 ( runReaderT )
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
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import           Kore.Internal.TermLike
import           Kore.Parser
                 ( parseKorePattern )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
import           Kore.Step.Rule
                 ( RewriteRule )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Predicate as Predicate
import qualified Kore.Step.Simplification.TermLike as TermLike
import qualified Kore.Step.Step as Step
import           Kore.Syntax.Definition
import qualified Kore.Syntax.Pattern as AST
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( unparseToString )
import           SMT
                 ( MonadSMT (..), SMT, Solver )
import qualified SMT

import           Test.Kore
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

mkPair
    :: Sort
    -> Sort
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
mkPair lSort rSort l r =
    mkApp (pairSort lSort rSort) (pairSymbol lSort rSort) [l, r]

substitutionSimplifier
    :: SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
substitutionSimplifier tools =
    Predicate.create tools stepSimplifier evaluators

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
    testCaseWithSolver title $ \solver -> do
        actual <- runReaderT (SMT.getSMT eval') solver
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
    makeIndexedModuleAttributesNull
    $ mapIndexedModulePatterns AST.eraseAnnotations verifiedModule

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build (constructorFunctions verifiedModule)

testSubstitutionSimplifier :: PredicateSimplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testMetadataTools

evaluators :: BuiltinAndAxiomSimplifierMap
evaluators = Builtin.koreEvaluators verifiedModule

stepSimplifier :: TermLikeSimplifier
stepSimplifier =
    termLikeSimplifier $ \_ p ->
        return $ OrPattern.fromPattern
            Conditional
                { term = mkTop_
                , predicate = Predicate.wrapPredicate p
                , substitution = mempty
                }

evaluate
    :: MonadSMT m
    => TermLike Variable
    -> m (Pattern Variable)
evaluate =
    liftSMT
    . evalSimplifier emptyLogger
    . TermLike.simplify
        testMetadataTools
        testSubstitutionSimplifier
        evaluators

evaluateWith
    :: MVar Solver
    -> TermLike Variable
    -> IO (Pattern Variable)
evaluateWith solver patt =
    runReaderT (SMT.getSMT $ evaluate patt) solver

runStep
    :: Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> IO (Either UnificationOrSubstitutionError (OrPattern Variable))
runStep configuration axiom = do
    result <- runStepResult configuration axiom
    return (Step.gatherResults <$> result)

runStepResult
    :: Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> IO (Either UnificationOrSubstitutionError (Step.Results Variable))
runStepResult configuration axiom =
    runSMT
    $ evalSimplifier emptyLogger
    $ Monad.Unify.runUnifier
    $ Step.applyRewriteRules
        testMetadataTools
        testSubstitutionSimplifier
        stepSimplifier
        evaluators
        (Step.UnificationProcedure Unification.unificationProcedure)
        [axiom]
        configuration

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig

runStepWith
    :: MVar Solver
    -> Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> IO (Either UnificationOrSubstitutionError (OrPattern Variable))
runStepWith solver configuration axiom = do
    result <- runStepResultWith solver configuration axiom
    return (Step.gatherResults <$> result)

runStepResultWith
    :: MVar Solver
    -> Pattern Variable
    -- ^ configuration
    -> RewriteRule Variable
    -- ^ axiom
    -> IO (Either UnificationOrSubstitutionError (Step.Results Variable))
runStepResultWith solver configuration axiom =
    let smt =
            evalSimplifier emptyLogger
            $ Monad.Unify.runUnifier
            $ Step.applyRewriteRules
                testMetadataTools
                testSubstitutionSimplifier
                stepSimplifier
                evaluators
                (Step.UnificationProcedure Unification.unificationProcedure)
                [axiom]
                configuration
    in runReaderT (SMT.getSMT smt) solver


-- | Test unparsing internalized patterns.
hpropUnparse
    :: Hedgehog.Gen (TermLike Variable)
    -- ^ Generate patterns with internal representations
    -> Hedgehog.Property
hpropUnparse gen = Hedgehog.property $ do
    builtin <- Hedgehog.forAll gen
    let syntax = unparseToString builtin
        expected = AST.eraseAnnotations (Builtin.externalizePattern builtin)
    Right expected Hedgehog.=== parseKorePattern "<test>" syntax
