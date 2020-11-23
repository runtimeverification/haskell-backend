module Test.Kore.Step.RewriteStep
    ( test_applyInitialConditions
    , test_renameRuleVariables
    , test_unifyRule
    , test_applyRewriteRule_
    , test_applyRewriteRulesParallel
    , test_applyRewriteRulesSequence
    , test_narrowing
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Exception as Exception
import Data.Default as Default
    ( def
    )
import Data.Maybe
    ( fromJust
    )
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate as Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate
    , makeFalsePredicate
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Reachability
    ( AllPathClaim (..)
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.ClaimPattern
    ( ClaimPattern
    , mkClaimPattern
    , refreshExistentials
    )
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.RulePattern
    ( RHS (..)
    , RewriteRule (..)
    , RulePattern (..)
    , injectTermIntoRHS
    , mkRewritingRule
    , rulePattern
    )
import qualified Kore.Step.RulePattern as RulePattern
import qualified Kore.Step.Step as Step
import qualified Kore.Unification.Procedure as Unification
import Kore.Variables.Fresh
    ( nextName
    )
import qualified Logic

import Test.Kore.Internal.Condition as Condition
import Test.Kore.Internal.OrCondition
    ( OrTestCondition
    )
import Test.Kore.Internal.OrPattern
    ( OrPattern
    , OrTestPattern
    )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern as Pattern
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

type RewriteRule' = RewriteRule VariableName
type Results' = Step.Results (RulePattern RewritingVariableName)

applyInitialConditions
    :: TestCondition
    -> TestCondition
    -> IO [OrTestCondition]
applyInitialConditions initial unification =
    Step.applyInitialConditions initial unification
    & runSimplifierSMT Mock.env . Logic.observeAllT

test_applyInitialConditions :: [TestTree]
test_applyInitialConditions =
    [ testCase "\\bottom initial condition" $ do
        let unification =
                Conditional
                    { term = ()
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
            initial = Condition.bottom
            expect = mempty
        actual <- applyInitialConditions initial unification
        assertEqual "" expect actual

    , testCase "returns axiom right-hand side" $ do
        let unification = Condition.top
            initial = Condition.top
            expect = [MultiOr.singleton initial]
        actual <- applyInitialConditions initial unification
        assertEqual "" expect actual

    , testCase "combine initial and rule conditions" $ do
        let unification = Condition.fromPredicate expect2
            initial = Condition.fromPredicate expect1
            expect1 =
                Predicate.makeEqualsPredicate
                    Mock.a
                    (Mock.f $ mkElemVar Mock.x)
            expect2 =
                Predicate.makeEqualsPredicate
                    Mock.b
                    (Mock.f $ mkElemVar Mock.y)
            expect =
                MultiOr.singleton (Predicate.makeAndPredicate expect1 expect2)
        [applied] <- applyInitialConditions initial unification
        let actual = MultiOr.map Conditional.predicate applied
        assertEqual "" expect actual

    , testCase "conflicting initial and rule conditions" $ do
        let predicate = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a
            unification = Condition.fromPredicate predicate
            initial =
                Condition.fromPredicate
                $ Predicate.makeNotPredicate predicate
            expect = mempty
        actual <- applyInitialConditions initial unification
        assertEqual "" expect actual

    ]

unifyRule
    :: InternalVariable variable
    => Step.UnifyingRule rule
    => Step.UnifyingRuleVariable rule ~ variable
    => Pattern variable
    -> rule
    -> IO [Step.UnifiedRule rule]
unifyRule initial rule =
    Step.unifyRule Unification.unificationProcedure initial rule
    & Logic.observeAllT
    & runSimplifier Mock.env

claimPatternFromPatterns
    :: Pattern VariableName
    -> Pattern VariableName
    -> ClaimPattern
claimPatternFromPatterns patt1 patt2 =
    mkClaimPattern
        ( patt1
        & Pattern.mapVariables (pure mkRuleVariable)
        )
        ( patt2
        & Pattern.mapVariables (pure mkRuleVariable)
        & OrPattern.fromPattern
        )
        []

claimPatternFromTerms
    :: TermLike VariableName
    -> TermLike VariableName
    -> [ElementVariable VariableName]
    -> ClaimPattern
claimPatternFromTerms term1 term2 existentials' =
    mkClaimPattern
        ( term1
        & Pattern.fromTermLike
        & Pattern.mapVariables (pure mkRuleVariable)
        )
        ( term2
        & Pattern.fromTermLike
        & Pattern.mapVariables (pure mkRuleVariable)
        & OrPattern.fromPattern
        )
        (mapElementVariable (pure mkRuleVariable) <$> existentials')

test_renameRuleVariables :: [TestTree]
test_renameRuleVariables =
    [ testCase "renames axiom left variables" $ do
        let initial =
                Step.mkRewritingPattern
                $ Pattern.fromTermLike
                $ Mock.f (mkElemVar Mock.x)
            axiom =
                RulePattern
                    { left = Mock.f (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , requires =
                        Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a
                    , rhs = injectTermIntoRHS (Mock.g (mkElemVar Mock.x))
                    , attributes = Default.def
                    }
            claim =
                claimPatternFromPatterns
                    ( Pattern.fromTermAndPredicate
                        (Mock.f (mkElemVar Mock.x))
                        (Predicate.makeEqualsPredicate
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                    )
                    ( Mock.g (mkElemVar Mock.x)
                    & Pattern.fromTermLike
                    )
            actualAxiom = mkRewritingRule axiom
            actualClaim = claim
            initialFreeVariables :: FreeVariables RewritingVariableName
            initialFreeVariables = freeVariables initial
            actualAxiomFreeVariables = freeVariables actualAxiom
            actualClaimFreeVariables = freeVariables actualClaim
        assertEqual "Axiom: Expected no common free variables"
            Set.empty
            $ on Set.intersection FreeVariables.toSet
                initialFreeVariables
                actualAxiomFreeVariables
        assertEqual "Claim: Expected no common free variables"
            Set.empty
            $ on Set.intersection FreeVariables.toSet
                initialFreeVariables
                actualClaimFreeVariables

    ]

test_unifyRule :: [TestTree]
test_unifyRule =
    [ testCase "performs unification with initial term" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr10 (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , requires = Predicate.makeTruePredicate
                    , rhs = injectTermIntoRHS (Mock.g Mock.b)
                    , attributes = Default.def
                    }
            claim =
                claimPatternFromTerms
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.g Mock.b)
                    []
            expectAxiom = [(pure axiom) { substitution = substitutionAxiom }]
            expectClaim = [(pure claim) { substitution = substitutionClaim }]
            substitutionAxiom =
                Substitution.unsafeWrap [(inject Mock.x, Mock.a)]
            substitutionClaim =
                Substitution.unsafeWrap [(inject x, Mock.a)]
              where
                x = mapElementVariable (pure mkRuleVariable) Mock.x
        actualAxiom <- unifyRule initial axiom
        actualClaim <- unifyRule (mkRewritingPattern initial) claim
        assertEqual "" expectAxiom actualAxiom
        assertEqual "" expectClaim actualClaim

    , testCase "returns unification failures" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr11 (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , requires = Predicate.makeTruePredicate
                    , rhs = injectTermIntoRHS (Mock.g Mock.b)
                    , attributes = Default.def
                    }
            claim =
                claimPatternFromTerms
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                    (Mock.g Mock.b)
                    []
            expect = []
        actualAxiom <- unifyRule initial axiom
        actualClaim <- unifyRule (mkRewritingPattern initial) claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim
    ]

-- | Apply the 'RewriteRule' to the configuration, but discard remainders.
applyRewriteRule_
    ::  ( Pattern VariableName -> [RewriteRule'] -> IO Results' )
    -- ^ 'RewriteRule'
    -> TestPattern
    -- ^ Configuration
    -> RewriteRule'
    -- ^ Rewrite rule
    -> IO [OrPattern RewritingVariableName]
applyRewriteRule_ applyRewriteRules initial rule =
    applyRewriteRules_ applyRewriteRules initial [rule]

-- | Apply the 'RewriteRule's to the configuration, but discard remainders.
applyRewriteRules_
    :: (Pattern VariableName -> [RewriteRule'] -> IO Results')
    -- ^ 'RewriteRule's
    -> TestPattern
    -- ^ Configuration
    -> [RewriteRule']
    -- ^ Rewrite rule
    -> IO [OrPattern RewritingVariableName]
applyRewriteRules_ applyRewriteRules initial rules = do
    result <- applyRewriteRules initial rules
    return (toList . discardRemainders $ result)
  where
    discardRemainders = fmap Step.result . Step.results

applyClaim_
    :: (TestPattern -> [ClaimPattern] -> IO (Step.Results ClaimPattern))
    -- ^ 'RewriteRule's
    -> TestPattern
    -- ^ Configuration
    -> ClaimPattern
    -- ^ Rewrite rule
    -> IO [OrPattern RewritingVariableName]
applyClaim_ applyClaims initial claim =
    applyClaims_ applyClaims initial [claim]

-- | Apply the 'RewriteRule's to the configuration, but discard remainders.
applyClaims_
    :: (TestPattern -> [ClaimPattern] -> IO (Step.Results ClaimPattern))
    -- ^ 'RewriteRule's
    -> TestPattern
    -- ^ Configuration
    -> [ClaimPattern]
    -- ^ Rewrite rule
    -> IO [OrPattern RewritingVariableName]
applyClaims_ applyClaims initial claims = do
    result <- applyClaims initial claims
    return (toList . discardRemainders $ result)
  where
    discardRemainders = fmap Step.result . Step.results

test_applyRewriteRule_ :: [TestTree]
test_applyRewriteRule_ =
    [ testCase "apply identity axiom" $ do
        let expect =
                [ OrPattern.fromPatterns [initial] ]
            initial = Pattern.fromTermLike (mkElemVar Mock.x)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomId
        actualClaim <- applyClaim initial claimId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "apply identity without renaming" $ do
        let expect =
                [ OrPattern.fromPatterns [initial] ]
            initial = Pattern.fromTermLike (mkElemVar Mock.y)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomId
        actualClaim <- applyClaim initial claimId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "substitute variable with itself" $ do
        let expect =
                [ OrPattern.fromPatterns [initial { term = mkElemVar Mock.x }] ]
            initial = Pattern.fromTermLike
                (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "merge configuration patterns" $ do
        let term = Mock.functionalConstr10 (mkElemVar Mock.y)
            expect =
                [ OrPattern.fromPatterns [initial { term, substitution }] ]
              where
                substitution =
                    Substitution.wrap
                    $ Substitution.mkUnwrappedSubstitution
                    [ (inject Mock.x, term) ]
            initial = Pattern.fromTermLike (Mock.sigma (mkElemVar Mock.x) term)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "substitution with symbol matching" $ do
        let expect =
                [ OrPattern.fromPatterns [initial { term = fz, substitution }] ]
              where
                substitution =
                    Substitution.wrap
                    $ Substitution.mkUnwrappedSubstitution
                    [ (inject Mock.y, mkElemVar Mock.z) ]
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            initial = Pattern.fromTermLike (Mock.sigma fy fz)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "merge multiple variables" $ do
        let expect =
                [ OrPattern.fromPatterns [initial { term = yy, substitution }] ]
              where
                substitution =
                    Substitution.wrap
                    $ Substitution.mkUnwrappedSubstitution
                    [ (inject Mock.x, mkElemVar Mock.y) ]
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            yx = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.x)
            yy = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y)
            initial = Pattern.fromTermLike (Mock.sigma xy yx)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaXXYY
        actualClaim <- applyClaim initial claimSigmaXXYY
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "rename quantified right variables" $ do
        let expect =
                 [ OrPattern.fromPatterns [Pattern.fromTermLike final] ]
            final = mkElemVar Mock.y
            initial = pure (mkElemVar Mock.y)
            axiom =
                RewriteRule $ rulePattern
                    (mkElemVar Mock.x)
                    (mkExists Mock.y (mkElemVar Mock.x))
            claim =
                claimPatternFromTerms
                    (mkElemVar Mock.x)
                    (mkElemVar Mock.x)
                    [Mock.y]
        actualAxiom <- applyRewriteRuleParallel_ initial axiom
        actualClaim <- applyClaim initial claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "quantified rhs: non-clashing" $ do
        let expect =
                [ OrPattern.fromPatterns [Pattern.fromTermLike final] ]
            x' =
                traverse (nextName (variableName Mock.x)) Mock.x
                & fromJust
            final = mkElemVar x'
            initial = pure (mkElemVar Mock.y)
            axiom =
                RewriteRule $ rulePattern
                    (mkElemVar Mock.x)
                    (mkExists Mock.x (mkElemVar Mock.x))
            claim =
                refreshExistentials $ claimPatternFromTerms
                    (mkElemVar Mock.x)
                    (mkElemVar Mock.x)
                    [Mock.x]
        actualAxiom <- applyRewriteRuleParallel_ initial axiom
        actualClaim <- applyClaim initial claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "Apply non-function-like rule in parallel" $ do
        let initial =
                pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        resultAxiom <-
            Exception.try
            $ applyRewriteRuleParallel_ initial axiomSigmaTopId
        case resultAxiom of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

        resultClaim <-
            Exception.try
            $ applyClaim initial claimSigmaTopId
        case resultClaim of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply list containing non-function-like rule in parallel" $ do
        let initial =
                pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        resultAxiom <-
            Exception.try
            $ applyRewriteRules_
                applyRewriteRulesParallel
                initial
                [axiomCaseA, axiomSigmaTopId]
        case resultAxiom of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

        resultClaim <-
            Exception.try
            $ applyClaims_
                applyClaimsSequence
                initial
                [claimCaseA, claimSigmaTopId]
        case resultClaim of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply non-function-like rule in sequence" $ do
        let initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        resultAxiom <-
            Exception.try
            $ applyRewriteRule_
                applyRewriteRulesSequence
                initial
                axiomSigmaTopId
        case resultAxiom of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

        resultClaim <-
            Exception.try
            $ applyClaim_
                applyClaimsSequence
                initial
                claimSigmaTopId
        case resultClaim of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply list containing non-function-like rule in sequence" $ do
        let initial =
                pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        resultAxiom <-
            Exception.try
            $ applyRewriteRules_
                applyRewriteRulesParallel
                initial
                [axiomCaseA, axiomSigmaTopId]
        case resultAxiom of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

        resultClaim <-
            Exception.try
            $ applyClaims_
                applyClaimsSequence
                initial
                [claimCaseA, claimSigmaTopId]
        case resultClaim of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "symbol clash" $ do
        let expect =  mempty
            fx = Mock.functionalConstr10 (mkElemVar Mock.x)
            gy = Mock.functionalConstr11 (mkElemVar Mock.y)
            initial = pure (Mock.sigma fx gy)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "impossible substitution" $ do
        let expect =  mempty
            xfy =
                Mock.sigma
                    (mkElemVar Mock.x)
                    (Mock.functionalConstr10 (mkElemVar Mock.y))
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            initial = pure (Mock.sigma xfy xy)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaXXYY
        actualClaim <- applyClaim initial claimSigmaXXYY
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "impossible substitution (ctor)" $ do
        let expect =  mempty
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (mkElemVar Mock.x)
                            (Mock.functionalConstr10 (mkElemVar Mock.y))
                    , predicate = Predicate.makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, mkElemVar Mock.x)]
                    }
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    {- TODO: (MirceaS) Enable this test when it no longer loops
    , testCase "circular dependency error" $ do
        let expect =
                Conditional
                    { term = fy
                    , predicate =
                        makeEqualsPredicate (mkElemVar Mock.y) fy
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, fy)]
                    }
                & pure . OrPattern.fromPattern
            fy = Mock.functional10 (mkElemVar Mock.y)
            initial =
                Conditional
                    { term = Mock.sigma (mkElemVar Mock.x) fy
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, mkElemVar Mock.x)]
                    }
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim
    -}
    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "unify all children" $ do
        let expect =

                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma zz zz
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.x, zz)
                                , (inject Mock.y, mkElemVar Mock.z)
                                ]
                            }
                        ]
                    ]
            xx = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x)
            yy = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y)
            zz = Mock.sigma (mkElemVar Mock.z) (mkElemVar Mock.z)
            yz = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z)
            initial = pure $ Mock.sigma xx (Mock.sigma yz yy)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaId
        actualClaim <- applyClaim initial claimSigmaId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "normalize substitution" $ do
        let
            fb = Mock.functional10 (mkElemVar Mock.y)
            expect =

                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.x, fb)]
                            }
                        ]
                    ]
            initial = pure $
                Mock.sigma(Mock.sigma (mkElemVar Mock.x) fb) (mkElemVar Mock.x)
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaXXY
        actualClaim <- applyClaim initial claimSigmaXXY
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , testCase "merge substitution with initial" $ do
        let
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            expect =

                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fz fz
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                    [ (inject Mock.x, fz)
                                    , (inject Mock.y, mkElemVar Mock.z)
                                    ]
                            }
                        ]
                    ]
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (Mock.sigma (mkElemVar Mock.x) fy)
                            (mkElemVar Mock.x)
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, fz)]
                    }
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaXXY
        actualClaim <- applyClaim initial claimSigmaXXY
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "unmatched string literals" $ do
        let expect =  mempty
            initial = pure (mkStringLiteral "sl2")
            axiom =
                RewriteRule $ rulePattern
                    (mkStringLiteral "sl1")
                    (mkElemVar Mock.x)
            claim =
                claimPatternFromTerms
                    (mkStringLiteral "sl1")
                    (mkElemVar Mock.x)
                    []
        actualAxiom <- applyRewriteRuleParallel_ initial axiom
        actualClaim <- applyClaim initial claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: a and g(a)=f(a)
    , testCase "preserve initial condition" $ do
        let expect =
                [ OrPattern.fromPatterns [initial] ]
            predicate =
                makeEqualsPredicate
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            initial =
                Conditional
                    { term = Mock.a
                    , predicate
                    , substitution = mempty
                    }
        actualAxiom <- applyRewriteRuleParallel_ initial axiomId
        actualClaim <- applyClaim initial claimId
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    , testCase "normalize substitution with initial condition" $ do
        let
            fb = Mock.functional10 (mkElemVar Mock.y)
            expect =

                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate =
                                makeEqualsPredicate
                                    (Mock.functional10 fb)
                                    (Mock.functional11 fb)
                            , substitution =
                                Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.x, fb)]
                            }
                        ]
                    ]
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (Mock.sigma (mkElemVar Mock.x) fb)
                            (mkElemVar Mock.x)
                    , predicate =
                        makeEqualsPredicate
                            (Mock.functional11 (mkElemVar Mock.x))
                            (Mock.functional10 (mkElemVar Mock.x))
                    , substitution = mempty
                    }
        actualAxiom <- applyRewriteRuleParallel_ initial axiomSigmaXXY
        actualClaim <- applyClaim initial claimSigmaXXY
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- x => x ensures g(x)=f(x)
    -- vs
    -- y
    -- Expected: y and g(y)=f(y)
    , testCase "conjoin rule ensures" $ do
        let
            ensures =
                makeEqualsPredicate
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            rhs = (RulePattern.rhs ruleId) { ensures }
            expect =
                [ OrPattern.fromPatterns
                    [ Conditional
                        { term = mkElemVar Mock.y
                        , predicate = makeEqualsPredicate
                            (Mock.functional10 (mkElemVar Mock.y))
                            (Mock.functional11 (mkElemVar Mock.y))
                        , substitution = mempty
                        }
                    ]
                ]
            initial = Pattern.fromTermLike (mkElemVar Mock.y)
            axiom = RewriteRule ruleId { rhs }
            claim =
                claimPatternFromPatterns
                    (mkElemVar Mock.x & Pattern.fromTermLike)
                    (Pattern.fromTermAndPredicate
                        (mkElemVar Mock.x)
                        ensures
                    )
        actualAxiom <- applyRewriteRuleParallel_ initial axiom
        actualClaim <- applyClaim initial claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "conjoin rule requirement" $ do
        let
            requires =
                makeEqualsPredicate
                    (Mock.functional10 (mkElemVar Mock.x))
                    (Mock.functional11 (mkElemVar Mock.x))
            expect =
                [ OrPattern.fromPatterns
                    [ initialTerm
                    `Pattern.withCondition` Condition.fromPredicate requires
                    ]
                ]
            initialTerm = mkElemVar Mock.x
            initial = pure initialTerm
            axiom = RewriteRule ruleId { requires }
            claim =
                claimPatternFromPatterns
                    (Pattern.fromTermAndPredicate
                        (mkElemVar Mock.x)
                        requires
                    )
                    (mkElemVar Mock.x & Pattern.fromTermLike)
        actualAxiom <- applyRewriteRuleParallel_ initial axiom
        actualClaim <- applyClaim initial claim
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "rule a => \\bottom" $ do
        let expect =  [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actualAxiom <- applyRewriteRuleParallel_ initial axiomBottom
        actualClaim <- applyClaim initial claimBottom
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "rule a => b ensures \\bottom" $ do
        let expect =  [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actualAxiom <- applyRewriteRuleParallel_ initial axiomEnsuresBottom
        actualClaim <- applyClaim initial claimEnsuresBottom
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "rule a => b requires \\bottom" $ do
        let expect =  [ ]
            initial = pure Mock.a
        actualAxiom <- applyRewriteRuleParallel_ initial axiomRequiresBottom
        actualClaim <- applyClaim initial claimRequiresBottom
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim

    , testCase "rule a => \\bottom does not apply to c" $ do
        let expect =  [ ]
            initial = pure Mock.c
        actualAxiom <- applyRewriteRuleParallel_ initial axiomRequiresBottom
        actualClaim <- applyClaim initial claimRequiresBottom
        assertEqual "" expect actualAxiom
        assertEqual "" expect actualClaim
    ]
  where
    applyRewriteRuleParallel_
        :: TestPattern
        -> RewriteRule'
        -> IO [OrPattern VariableName]
    applyRewriteRuleParallel_ patt rule =
        applyRewriteRule_ applyRewriteRulesParallel patt rule
        & (fmap . fmap . OrPattern.map) getRewritingPattern

    applyClaim
        :: TestPattern
        -> ClaimPattern
        -> IO [OrPattern VariableName]
    applyClaim patt rule =
        applyClaim_ applyClaimsSequence patt rule
        & (fmap . fmap . OrPattern.map) getRewritingPattern

    ruleId =
        rulePattern
            (mkElemVar Mock.x)
            (mkElemVar Mock.x)
    axiomId = RewriteRule ruleId
    claimId =
        claimPatternFromTerms
            (mkElemVar Mock.x)
            (mkElemVar Mock.x)
            []

    axiomBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , requires = makeTruePredicate
            , rhs = injectTermIntoRHS (mkBottom Mock.testSort)
            , attributes = def
            }

    claimBottom =
        claimPatternFromTerms
            Mock.a
            (mkBottom Mock.testSort)
            []

    axiomEnsuresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , requires = makeTruePredicate
            , rhs = RHS
                { existentials = []
                , right = Mock.b
                , ensures = makeFalsePredicate
                }
            , attributes = def
            }

    claimEnsuresBottom =
        claimPatternFromPatterns
            (Mock.a & Pattern.fromTermLike )
            (Pattern.fromTermAndPredicate
                Mock.b
                makeFalsePredicate
            )

    axiomRequiresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , requires = makeFalsePredicate
            , rhs = injectTermIntoRHS Mock.b
            , attributes = def
            }

    claimRequiresBottom =
        claimPatternFromPatterns
            (Pattern.fromTermAndPredicate
                Mock.a
                makeFalsePredicate
            )
            (Mock.b & Pattern.fromTermLike)

    axiomSigmaId =
        RewriteRule $ rulePattern
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
            (mkElemVar Mock.x)

    claimSigmaId =
        claimPatternFromTerms
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
            (mkElemVar Mock.x)
            []

    axiomSigmaTopId =
        RewriteRule $ rulePattern
            (Mock.sigma (mkElemVar Mock.x) mkTop_)
            (mkElemVar Mock.x)

    claimSigmaTopId =
        claimPatternFromTerms
            (Mock.sigma (mkElemVar Mock.x) mkTop_)
            (mkElemVar Mock.x)
            []

    axiomSigmaXXYY =
        RewriteRule $ rulePattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y))
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    claimSigmaXXYY =
        claimPatternFromTerms
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y))
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))
            []

    axiomSigmaXXY =
        RewriteRule $ rulePattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    claimSigmaXXY =
        claimPatternFromTerms
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))
            []

{- | Tests for symbolic narrowing.

Narrowing happens when a variable in a symbolic configuration is instantiated
with a particular value.

 -}
test_narrowing :: [TestTree]
test_narrowing =
    [ testCase "applyRewriteRulesParallel" $ do
        actual <- apply axiom (Pattern.fromTermLike initial)
        let results = OrPattern.fromPatterns [result]
        checkResults results actual
        let remainders = OrPattern.fromPatterns [remainder]
        checkRemainders remainders actual
    , testCase "resetResultPattern" $ do
        let resultRewriting =
                Pattern.withCondition (Mock.sigma Mock.b (mkElemVar xRule))
                $ Condition.fromSingleSubstitution
                $ Substitution.assign
                    (inject xConfig)
                    (Mock.sigma Mock.a (mkElemVar xRule))
            initialVariables = FreeVariables.freeVariable (inject xConfig)
            actual = resetResultPattern initialVariables resultRewriting
        assertEqual "" (mkRewritingPattern result) actual
    ]
  where
    apply rule config = applyRewriteRulesParallel config [rule]
    x = Mock.x
    x' = traverse (\name -> nextName name name) x & fromJust
    xConfig = mkElementConfigVariable x
    xRule = mkElementRuleVariable x
    initial = mkElemVar x
    -- The significance of this axiom is that it narrows the initial term and
    -- introduces a new variable.
    axiom =
        RewriteRule $ rulePattern
            (Mock.sigma Mock.a (mkElemVar x))
            (Mock.sigma Mock.b (mkElemVar x))
    result =
        Pattern.withCondition (Mock.sigma Mock.b (mkElemVar x'))
        $ Condition.fromSingleSubstitution
        $ Substitution.assign (inject x) (Mock.sigma Mock.a (mkElemVar x'))
    remainder =
        Pattern.withCondition initial
        $ Condition.fromPredicate
        $ Predicate.makeNotPredicate
        $ Predicate.makeExistsPredicate x'
        $ Predicate.makeEqualsPredicate
            (mkElemVar x)
            (Mock.sigma Mock.a (mkElemVar x'))

-- | Apply the 'RewriteRule's to the configuration.
applyRewriteRulesParallel
    :: TestPattern
    -- ^ Configuration
    -> [RewriteRule']
    -- ^ Rewrite rule
    -> IO Results'
applyRewriteRulesParallel initial rules =
    Step.applyRewriteRulesParallel
        Unification.unificationProcedure
        (mkRewritingRule <$> rules)
        (mkRewritingPattern $ simplifiedPattern initial)
    & runSimplifierSMT Mock.env

applyClaimsSequence
    :: TestPattern
    -- ^ Configuration
    -> [ClaimPattern]
    -- ^ Rewrite rule
    -> IO (Step.Results ClaimPattern)
applyClaimsSequence initial claims =
    Step.applyClaimsSequence
        AllPathClaim
        Unification.unificationProcedure
        (mkRewritingPattern $ simplifiedPattern initial)
        claims
    & runSimplifierSMT Mock.env

checkResults
    :: Step.UnifyingRuleVariable rule ~ RewritingVariableName
    => HasCallStack
    => OrTestPattern
    -> Step.Results rule
    -> Assertion
checkResults expect actual =
    assertEqual "compare results"
        expect
        (OrPattern.map getRewritingPattern $ Step.gatherResults actual)

checkRemainders
    :: Step.UnifyingRuleVariable rule ~ RewritingVariableName
    => HasCallStack
    => OrTestPattern
    -> Step.Results rule
    -> Assertion
checkRemainders expect actual =
    assertEqual "compare remainders"
        expect
        (OrPattern.map getRewritingPattern $ Step.remainders actual)

test_applyRewriteRulesParallel :: [TestTree]
test_applyRewriteRulesParallel =
    [ testCase "if _ then _" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: constr20(x, cg)
        --   axiom: constr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cg⌉ and [x=a]
        --   remainder: constr20(x, cg), with ¬(⌈cg⌉ and x=a)
        let
            results =
                MultiOr.singleton Conditional
                    { term = Mock.cg
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = initialTerm
                        , predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate
                                    (mkElemVar Mock.x)
                                    Mock.a
                                )
                        , substitution = mempty
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
            initial = pure initialTerm
        actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "if _ then _ with initial condition" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: constr20(x, cg), with a ⌈cf⌉ predicate
        --   axiom: constr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cf⌉ and ⌈cg⌉ and [x=a]
        --   remainder: constr20(x, cg), with ⌈cf⌉ and ¬(⌈cg⌉ and x=a)
        let
            results =
                MultiOr.singleton Conditional
                    { term = Mock.cg
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeCeilPredicate Mock.cg)
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term =
                            Mock.functionalConstr20
                                (mkElemVar Mock.x)
                                Mock.cg
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeNotPredicate $ makeAndPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate
                                        (mkElemVar Mock.x)
                                        Mock.a
                                    )
                                )
                        , substitution = mempty
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
            initial =
                Conditional
                    { term = initialTerm
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = mempty
                    }
        actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "signum - side condition" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: signum(x)
        --   axiom: signum(y) => -1 if (y<0 == true)
        -- Actual:
        --   term: functionalConstr10(x)
        --   axiom: functionalConstr10(y) => a if f(y) == b
        -- Expected:
        --   rewritten: a, with f(x) == b
        --   remainder: functionalConstr10(x), with ¬(f(x) == b)
        let
            results =
                MultiOr.singleton Conditional
                    { term = Mock.a
                    , predicate = requirement
                    , substitution = mempty
                    }
            remainders =
                MultiOr.singleton Conditional
                    { term = Mock.functionalConstr10 (mkElemVar Mock.x)
                    , predicate = makeNotPredicate requirement
                    , substitution = mempty
                    }
            initial = pure (Mock.functionalConstr10 (mkElemVar Mock.x))
            requirement =
                makeEqualsPredicate
                    Mock.b
                    (Mock.f (mkElemVar Mock.x))
        actual <- applyRewriteRulesParallel initial [axiomSignum]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "if _ then _ -- partial" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: functionalConstr20(x, cg)
        --   axiom: functionalConstr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cg⌉ and [x=a]
        --   remainder: functionalConstr20(x, cg), with ¬(⌈cg⌉ and x=a)
        let
            results =
                MultiOr.singleton Conditional
                    { term = Mock.cg
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate
                                    (mkElemVar Mock.x)
                                    Mock.a
                                )
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
            initial = pure initialTerm
        actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "case _ of a -> _; b -> _ -- partial" $ do
        -- This uses `functionalConstr30(x, y, z)` to represent a case
        -- statement,
        -- i.e. `case x of 1 -> y; 2 -> z`
        -- and `a`, `b` as the case labels.
        --
        -- Intended:
        --   term: case x of 1 -> cf; 2 -> cg
        --   axiom: case 1 of 1 -> cf; 2 -> cg => cf
        --   axiom: case 2 of 1 -> cf; 2 -> cg => cg
        -- Actual:
        --   term: constr30(x, cg, cf)
        --   axiom: constr30(a, y, z) => y
        --   axiom: constr30(b, y, z) => z
        -- Expected:
        --   rewritten: cf, with (⌈cf⌉ and ⌈cg⌉) and [x=a]
        --   rewritten: cg, with (⌈cf⌉ and ⌈cg⌉) and [x=b]
        --   remainder:
        --     constr20(x, cf, cg)
        --        with ¬(⌈cf⌉ and ⌈cg⌉ and [x=a])
        --         and ¬(⌈cf⌉ and ⌈cg⌉ and [x=b])
        let
            definedBranches =
                makeAndPredicate
                    (makeCeilPredicate Mock.cf)
                    (makeCeilPredicate Mock.cg)
            results =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.b)]
                        }
                    ]
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            Predicate.makeAndPredicate
                                (makeNotPredicate $ makeAndPredicate
                                    definedBranches
                                    (Predicate.makeEqualsPredicate
                                        (mkElemVar Mock.x)
                                        Mock.a
                                    )
                                )
                                (makeNotPredicate $ makeAndPredicate
                                    definedBranches
                                    (Predicate.makeEqualsPredicate
                                        (mkElemVar Mock.x)
                                        Mock.b
                                    )
                                )
                        }
                    ]
            initialTerm =
                Mock.functionalConstr30 (mkElemVar Mock.x) Mock.cf Mock.cg
            initial = pure initialTerm
        actual <- applyRewriteRulesParallel initial axiomsCase
        checkResults results actual
        checkRemainders remainders actual

    , testCase "if _ then _ -- partial" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: functionalConstr20(x, cg)
        --   axiom: functionalConstr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cg⌉ and [x=a]
        --   remainder: functionalConstr20(x, cg), with ¬(⌈cg⌉ and x=a)
        let
            results =
                MultiOr.singleton Conditional
                    { term = Mock.cg
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate
                                    (mkElemVar Mock.x)
                                    Mock.a
                                )
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
            initial = pure initialTerm
        actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results =
                OrPattern.fromTermLike (mkElemVar Mock.x)
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        actual <- applyRewriteRulesParallel initial
            [ RewriteRule RulePattern
                { left = Mock.a
                , antiLeft = Nothing
                , requires = makeTruePredicate
                , rhs = injectTermIntoRHS (mkElemVar Mock.x)
                , attributes = def
                }
            ]
        checkResults results actual
        checkRemainders remainders actual
    ]

axiomIfThen :: RewriteRule'
axiomIfThen =
    RewriteRule $ rulePattern
        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
        (mkElemVar Mock.y)

axiomSignum :: RewriteRule'
axiomSignum =
    RewriteRule RulePattern
        { left = Mock.functionalConstr10 (mkElemVar Mock.y)
        , antiLeft = Nothing
        , requires = makeEqualsPredicate (Mock.f (mkElemVar Mock.y)) Mock.b
        , rhs = injectTermIntoRHS Mock.a
        , attributes = def
        }

axiomCaseA :: RewriteRule'
axiomCaseA =
    RewriteRule $ rulePattern
        (Mock.functionalConstr30
                Mock.a
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.y)

axiomCaseB :: RewriteRule'
axiomCaseB =
    RewriteRule $ rulePattern
        (Mock.functionalConstr30
                Mock.b
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.z)

axiomsCase :: [RewriteRule']
axiomsCase = [axiomCaseA, axiomCaseB]

claimCaseA :: ClaimPattern
claimCaseA =
    claimPatternFromTerms
        (Mock.functionalConstr30
                Mock.a
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.y)
        []

claimCaseB :: ClaimPattern
claimCaseB =
    claimPatternFromTerms
        (Mock.functionalConstr30
                Mock.b
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.z)
        []

claimsCase :: [ClaimPattern]
claimsCase = [claimCaseA, claimCaseB]

-- | Apply the 'RewriteRule's to the configuration in sequence.
applyRewriteRulesSequence
    :: TestPattern
    -- ^ Configuration
    -> [RewriteRule']
    -- ^ Rewrite rule
    -> IO Results'
applyRewriteRulesSequence initial rules =
    Step.applyRewriteRulesSequence
        Unification.unificationProcedure
        (mkRewritingPattern $ simplifiedPattern initial)
        (mkRewritingRule <$> rules)
    & runSimplifierSMT Mock.env

test_applyRewriteRulesSequence :: [TestTree]
test_applyRewriteRulesSequence =
    [ testCase "case _ of a -> _; b -> _ -- partial" $ do
        -- This uses `functionalConstr30(x, y, z)` to represent a case
        -- statement,
        -- i.e. `case x of 1 -> y; 2 -> z`
        -- and `a`, `b` as the case labels.
        --
        -- Intended:
        --   term: case x of 1 -> cf; 2 -> cg
        --   axiom: case 1 of 1 -> cf; 2 -> cg => cf
        --   axiom: case 2 of 1 -> cf; 2 -> cg => cg
        -- Actual:
        --   term: constr30(x, cg, cf)
        --   axiom: constr30(a, y, z) => y
        --   axiom: constr30(b, y, z) => z
        -- Expected:
        --   rewritten: cf, with (⌈cf⌉ and ⌈cg⌉) and [x=a]
        --   rewritten: cg, with (⌈cf⌉ and ⌈cg⌉) and [x=b]
        --   remainder:
        --     constr20(x, cf, cg)
        --        with ¬(⌈cf⌉ and [x=a])
        --         and ¬(⌈cg⌉ and [x=b])
        let
            definedBranches =
                makeAndPredicate
                    (makeCeilPredicate Mock.cf)
                    (makeCeilPredicate Mock.cg)
            results =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.b)]
                        }
                    ]
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            Predicate.makeAndPredicate
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate
                                        definedBranches
                                        (Predicate.makeEqualsPredicate
                                            (mkElemVar Mock.x)
                                            Mock.a
                                        )
                                )
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate
                                        definedBranches
                                        (Predicate.makeEqualsPredicate
                                            (mkElemVar Mock.x)
                                            Mock.b
                                        )
                                )
                        }
                    ]
            initialTerm =
                Mock.functionalConstr30 (mkElemVar Mock.x) Mock.cf Mock.cg
            initial = pure initialTerm
        actualAxiom <- applyRewriteRulesSequence initial axiomsCase
        checkResults results actualAxiom
        checkRemainders remainders actualAxiom
        actualClaim <- applyClaimsSequence initial claimsCase
        checkResults results actualClaim
        checkRemainders remainders actualClaim

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results =
                OrPattern.fromTermLike (mkElemVar Mock.x)
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        actualAxiom <- applyRewriteRulesSequence initial
            [ RewriteRule $ rulePattern
                Mock.a
                (mkElemVar Mock.x)
            ]
        checkResults results actualAxiom
        checkRemainders remainders actualAxiom
        actualClaim <- applyClaimsSequence initial
            [ claimPatternFromTerms
                Mock.a
                (mkElemVar Mock.x)
                []
            ]
        checkResults results actualClaim
        checkRemainders remainders actualClaim
    ]
