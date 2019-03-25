module Test.Kore.Builtin.Builtin where

import qualified Hedgehog
import           Test.Tasty
                 ( TestTree )
import           Test.Tasty.HUnit
                 ( assertEqual )

import           Control.Concurrent.MVar
                 ( MVar )
import qualified Control.Lens as Lens
import           Control.Monad.Except
                 ( runExceptT )
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

import qualified Kore.AST.Kore as Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import           Kore.Parser.Parser
                 ( parseKorePattern )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
import           Kore.Step.AxiomPatterns
                 ( RewriteRule )
import           Kore.Step.Error
                 ( StepError )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Step
                 ( OrStepResult (..) )
import qualified Kore.Step.Step as Step
import           Kore.Step.StepperAttributes
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
    :: Sort Object
    -> Sort Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkPair lSort rSort l r =
    mkApp (pairSort lSort rSort) (pairSymbol lSort rSort) [l, r]

substitutionSimplifier
    :: MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
substitutionSimplifier tools =
    PredicateSubstitution.create tools stepSimplifier evaluators

-- | 'testSymbol' is useful for writing unit tests for symbols.
testSymbolWithSolver
    ::  ( HasCallStack
        , p ~ CommonStepPattern Object
        , expanded ~ CommonExpandedPattern Object
        )
    => (p -> SMT expanded)
    -- ^ evaluator function for the builtin
    -> String
    -- ^ test name
    -> Sort Object
    -- ^ symbol result sort
    -> SymbolOrAlias Object
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
    :: KoreDefinition
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

testMetadataTools :: MetadataTools Object StepperAttributes
testMetadataTools = extractMetadataTools (constructorFunctions verifiedModule)

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object
testSubstitutionSimplifier = Mock.substitutionSimplifier testMetadataTools

evaluators :: BuiltinAndAxiomSimplifierMap Object
evaluators = Builtin.koreEvaluators verifiedModule

stepSimplifier :: StepPatternSimplifier level
stepSimplifier =
    StepPatternSimplifier
        (\_ p ->
            return
                ( MultiOr.make
                    [ Predicated
                        { term = mkTop_
                        , predicate = Predicate.wrapPredicate p
                        , substitution = mempty
                        }
                    ]
                , SimplificationProof
                )
        )

evaluate
    :: MonadSMT m
    => CommonStepPattern Object
    -> m (CommonExpandedPattern Object)
evaluate =
    (<$>) fst
    . liftSMT
    . evalSimplifier emptyLogger
    . Pattern.simplify
        testMetadataTools
        testSubstitutionSimplifier
        evaluators

evaluateWith
    :: MVar Solver
    -> CommonStepPattern Object
    -> IO (CommonExpandedPattern Object)
evaluateWith solver patt =
    runReaderT (SMT.getSMT $ evaluate patt) solver

runStep
    :: CommonExpandedPattern Object
    -- ^ configuration
    -> RewriteRule Object Variable
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (CommonExpandedPattern Object))
        )
runStep configuration axiom = do
    result <- runStepResult configuration axiom
    return (discardRemainders <$> result)

runStepResult
    :: CommonExpandedPattern Object
    -- ^ configuration
    -> RewriteRule Object Variable
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (OrStepResult Object Variable)
        )
runStepResult configuration axiom =
    runSMT
    $ evalSimplifier emptyLogger
    $ runExceptT
    $ Step.applyRewriteRules
        testMetadataTools
        testSubstitutionSimplifier
        stepSimplifier
        evaluators
        [axiom]
        configuration

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig

runStepWith
    :: MVar Solver
    -> CommonExpandedPattern Object
    -- ^ configuration
    -> RewriteRule Object Variable
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (CommonExpandedPattern Object))
        )
runStepWith solver configuration axiom = do
    result <- runStepResultWith solver configuration axiom
    return (discardRemainders <$> result)

discardRemainders
    :: OrStepResult Object Variable
    -> MultiOr (CommonExpandedPattern Object)
discardRemainders OrStepResult { rewrittenPattern } = rewrittenPattern

runStepResultWith
    :: MVar Solver
    -> CommonExpandedPattern Object
    -- ^ configuration
    -> RewriteRule Object Variable
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (OrStepResult Object Variable)
        )
runStepResultWith solver configuration axiom =
    let smt =
            evalSimplifier emptyLogger
            $ runExceptT
            $ Step.applyRewriteRules
                testMetadataTools
                testSubstitutionSimplifier
                stepSimplifier
                evaluators
                [axiom]
                configuration
    in runReaderT (SMT.getSMT smt) solver


-- | Test unparsing internalized patterns.
hpropUnparse
    :: Hedgehog.Gen (CommonStepPattern Object)
    -- ^ Generate patterns with internal representations
    -> Hedgehog.Property
hpropUnparse gen = Hedgehog.property $ do
    builtin <- Hedgehog.forAll gen
    let syntax = unparseToString builtin
        expected =
            (Kore.eraseAnnotations . toKorePattern)
                (Builtin.externalizePattern builtin)
    Right expected Hedgehog.=== parseKorePattern "<test>" syntax
