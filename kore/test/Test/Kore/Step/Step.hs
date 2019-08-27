module Test.Kore.Step.Step
    ( test_applyInitialConditions
    , test_unifyRule
    , test_applyRewriteRule_
    , test_applyRewriteRulesParallel
    , test_applyRewriteRulesSequence
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Default as Default
                 ( def )
import qualified Data.Foldable as Foldable

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import           Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate as Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeNotPredicate, makeTruePredicate )
import qualified Kore.Step.Result as Result
                 ( mergeResults )
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
import           Kore.Step.Step hiding
                 ( applyInitialConditions, applyRewriteRulesParallel,
                 applyRewriteRulesSequence, unifyRule )
import qualified Kore.Step.Step as Step
import           Kore.Unification.Error
                 ( SubstitutionError (..), UnificationOrSubstitutionError (..),
                 unsupportedPatterns )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify
                 ( UnifierT, runUnifierT )
import           Kore.Variables.Fresh
                 ( nextVariable )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

evalUnifier
    :: UnifierT Simplifier a
    -> IO (Either UnificationOrSubstitutionError [a])
evalUnifier =
    SMT.runSMT SMT.defaultConfig emptyLogger
    . evalSimplifier Mock.env
    . runUnifierT

applyInitialConditions
    :: Predicate Variable
    -> Predicate Variable
    -> IO (Either UnificationOrSubstitutionError [OrPredicate Variable])
applyInitialConditions initial unification =
    (fmap . fmap) Foldable.toList
    $ evalUnifier
    $ Step.applyInitialConditions initial unification

test_applyInitialConditions :: [TestTree]
test_applyInitialConditions =
    [ testCase "\\bottom initial condition" $ do
        let unification =
                Conditional
                    { term = ()
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
            initial = Predicate.bottom
            expect = Right mempty
        actual <- applyInitialConditions initial unification
        assertEqualWithExplanation "" expect actual

    , testCase "returns axiom right-hand side" $ do
        let unification = Predicate.top
            initial = Predicate.top
            expect = Right [MultiOr.singleton initial]
        actual <- applyInitialConditions initial unification
        assertEqualWithExplanation "" expect actual

    , testCase "combine initial and rule conditions" $ do
        let unification = Predicate.fromPredicate expect2
            initial = Predicate.fromPredicate expect1
            expect1 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkVar Mock.x)
                    Mock.a
            expect2 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkVar Mock.y)
                    Mock.b
            expect =
                MultiOr.singleton (Predicate.makeAndPredicate expect1 expect2)
        Right [applied] <- applyInitialConditions initial unification
        let actual = Conditional.predicate <$> applied
        assertEqual "" expect actual

    , testCase "conflicting initial and rule conditions" $ do
        let predicate = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
            unification = Predicate.fromPredicate predicate
            initial =
                Predicate.fromPredicate
                $ Predicate.makeNotPredicate predicate
            expect = Right mempty
        actual <- applyInitialConditions initial unification
        assertEqualWithExplanation "" expect actual

    ]

unifyRule
    :: Pattern Variable
    -> RulePattern Variable
    -> IO
        (Either
            UnificationOrSubstitutionError
            [Conditional Variable (RulePattern Variable)]
        )
unifyRule initial rule =
    evalUnifier $ Step.unifyRule unificationProcedure initial rule
  where
    unificationProcedure = UnificationProcedure Unification.unificationProcedure

test_unifyRule :: [TestTree]
test_unifyRule =
    [ testCase "renames axiom left variables" $ do
        let initial = pure (Mock.f (mkVar Mock.x))
            axiom =
                RulePattern
                    { left = Mock.f (mkVar Mock.x)
                    , right = Mock.g (mkVar Mock.x)
                    , requires =
                        Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
        Right unified <- unifyRule initial axiom
        let actual = Conditional.term <$> unified
        assertBool ""
            $ Foldable.all (not . FreeVariables.isFreeVariable Mock.x)
            $ RulePattern.freeVariables <$> actual

    , testCase "performs unification with initial term" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right [(pure axiom) { substitution }]
              where
                substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
        actual <- unifyRule initial axiom
        assertEqualWithExplanation "" expect actual

    , testCase "returns unification failures" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr11 (mkVar Mock.x)
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right []
        actual <- unifyRule initial axiom
        assertEqualWithExplanation "" expect actual
    ]

-- | Apply the 'RewriteRule' to the configuration, but discard remainders.
applyRewriteRule_
    :: Pattern Variable
    -- ^ Configuration
    -> RewriteRule Variable
    -- ^ Rewrite rule
    -> IO (Either UnificationOrSubstitutionError [OrPattern Variable])
applyRewriteRule_ initial rule = do
    result <- applyRewriteRulesParallel initial [rule]
    return (Foldable.toList . discardRemainders <$> result)
  where
    discardRemainders = fmap Step.result . Step.results

test_applyRewriteRule_ :: [TestTree]
test_applyRewriteRule_ =
    [ testCase "apply identity axiom" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            initial = pure (mkVar Mock.x)
        actual <- applyRewriteRule_ initial axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "apply identity without renaming" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            initial = pure (mkVar Mock.y)
        actual <- applyRewriteRule_ initial axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "substitute variable with itself" $ do
        let expect = Right [ OrPattern.fromPatterns [initial { term = mkVar Mock.x }] ]
            initial = pure (Mock.sigma (mkVar Mock.x) (mkVar Mock.x))
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "merge configuration patterns" $ do
        let term = Mock.functionalConstr10 (mkVar Mock.y)
            expect = Right [ OrPattern.fromPatterns [initial { term, substitution }] ]
              where
                substitution = Substitution.wrap [ (Mock.x, term) ]
            initial = pure (Mock.sigma (mkVar Mock.x) term)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "substitution with symbol matching" $ do
        let expect =
                Right [ OrPattern.fromPatterns [initial { term = fz, substitution }] ]
              where
                substitution = Substitution.wrap [ (Mock.y, mkVar Mock.z) ]
            fy = Mock.functionalConstr10 (mkVar Mock.y)
            fz = Mock.functionalConstr10 (mkVar Mock.z)
            initial = pure (Mock.sigma fy fz)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "merge multiple variables" $ do
        let expect =
                Right [ OrPattern.fromPatterns [initial { term = yy, substitution }] ]
              where
                substitution = Substitution.wrap [ (Mock.x, mkVar Mock.y) ]
            xy = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            yx = Mock.sigma (mkVar Mock.y) (mkVar Mock.x)
            yy = Mock.sigma (mkVar Mock.y) (mkVar Mock.y)
            initial = pure (Mock.sigma xy yx)
        actual <- applyRewriteRule_ initial axiomSigmaXXYY
        assertEqualWithExplanation "" expect actual

    , testCase "rename quantified right variables" $ do
        let expect = Right [ OrPattern.fromPatterns [pure final] ]
            final = mkExists (nextVariable Mock.y) (mkVar Mock.y)
            initial = pure (mkVar Mock.y)
            axiom =
                RewriteRule RulePattern
                    { left = mkVar Mock.x
                    , right = mkExists Mock.y (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
        actual <- applyRewriteRule_ initial axiom
        assertEqualWithExplanation "" expect actual

    , testCase "symbol clash" $ do
        let expect = Right mempty
            fx = Mock.functionalConstr10 (mkVar Mock.x)
            gy = Mock.functionalConstr11 (mkVar Mock.y)
            initial = pure (Mock.sigma fx gy)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "impossible substitution" $ do
        let expect = Right mempty
            xfy =
                Mock.sigma
                    (mkVar Mock.x)
                    (Mock.functionalConstr10 (mkVar Mock.y))
            xy = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            initial = pure (Mock.sigma xfy xy)
        actual <- applyRewriteRule_ initial axiomSigmaXXYY
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "impossible substitution (ctor)" $ do
        let expect = Right mempty
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (mkVar Mock.x)
                            (Mock.functionalConstr10 (mkVar Mock.y))
                    , predicate = Predicate.makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, mkVar Mock.x)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "circular dependency error" $ do
        let expect =
                -- TODO(virgil): This should probably be a normal result with
                -- b=h(b) in the predicate.
                Left
                $ SubstitutionError
                $ NonCtorCircularVariableDependency [Mock.y]
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (mkVar Mock.x)
                            (Mock.functional10 (mkVar Mock.y))
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, mkVar Mock.x)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "non-function substitution error" $ do
        let expect = Left $ UnificationError $ unsupportedPatterns
                "Unknown unification case."
                (mkVar (nextVariable Mock.x))
                (Mock.plain10 (mkVar Mock.y))
            initial =
                pure $ Mock.sigma (mkVar Mock.x) (Mock.plain10 (mkVar Mock.y))
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "unify all children" $ do
        let expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma zz zz
                            , predicate = makeTruePredicate
                            , substitution = Substitution.wrap
                                [ (Mock.x, zz)
                                , (Mock.y, mkVar Mock.z)
                                ]
                            }
                        ]
                    ]
            xx = Mock.sigma (mkVar Mock.x) (mkVar Mock.x)
            yy = Mock.sigma (mkVar Mock.y) (mkVar Mock.y)
            zz = Mock.sigma (mkVar Mock.z) (mkVar Mock.z)
            yz = Mock.sigma (mkVar Mock.y) (mkVar Mock.z)
            initial = pure $ Mock.sigma xx (Mock.sigma yz yy)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "normalize substitution" $ do
        let
            fb = Mock.functional10 (mkVar Mock.y)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate = makeTruePredicate
                            , substitution = Substitution.wrap [(Mock.x, fb)]
                            }
                        ]
                    ]
            initial =
                pure $ Mock.sigma (Mock.sigma (mkVar Mock.x) fb) (mkVar Mock.x)
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqualWithExplanation "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , testCase "merge substitution with initial" $ do
        let
            fy = Mock.functionalConstr10 (mkVar Mock.y)
            fz = Mock.functionalConstr10 (mkVar Mock.z)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fz fz
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap
                                    [ (Mock.x, fz)
                                    , (Mock.y, mkVar Mock.z)
                                    ]
                            }
                        ]
                    ]
            initial =
                Conditional
                    { term =
                        Mock.sigma (Mock.sigma (mkVar Mock.x) fy) (mkVar Mock.x)
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.x, fz)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqualWithExplanation "" expect actual

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "unmatched string literals" $ do
        let expect = Right mempty
            initial = pure (mkStringLiteral "sl2")
            axiom =
                RewriteRule RulePattern
                    { left = mkStringLiteral "sl1"
                    , right = mkVar Mock.x
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
        actual <- applyRewriteRule_ initial axiom
        assertEqualWithExplanation "" expect actual

    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: a and g(a)=f(a)
    , testCase "preserve initial condition" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
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
        actual <- applyRewriteRule_ initial axiomId
        assertEqualWithExplanation "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    , testCase "normalize substitution with initial condition" $ do
        let
            fb = Mock.functional10 (mkVar Mock.y)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate =
                                makeEqualsPredicate
                                    (Mock.functional11 fb)
                                    (Mock.functional10 fb)
                            , substitution = Substitution.wrap [(Mock.x, fb)]
                            }
                        ]
                    ]
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (Mock.sigma (mkVar Mock.x) fb)
                            (mkVar Mock.x)
                    , predicate =
                        makeEqualsPredicate
                            (Mock.functional11 (mkVar Mock.x))
                            (Mock.functional10 (mkVar Mock.x))
                    , substitution = mempty
                    }
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqualWithExplanation "" expect actual

    -- x => x ensures g(x)=f(x)
    -- vs
    -- a
    -- Expected: a and g(a)=f(a)
    , testCase "conjoin rule ensures" $ do
        let
            ensures =
                makeEqualsPredicate
                    (Mock.functional11 (mkVar Mock.x))
                    (Mock.functional10 (mkVar Mock.x))
            expect :: Either
                UnificationOrSubstitutionError [OrPattern Variable]
            expect = Right
                [ OrPattern.fromTermLike
                    (mkExists
                        Mock.x
                        (mkAnd
                            (mkVar Mock.x)
                            (mkEquals_
                                (Mock.functional11 (mkVar Mock.x))
                                (Mock.functional10 (mkVar Mock.x))
                            )
                        )
                    )
                ]
            initial = Pattern.fromTermLike (mkVar Mock.x)
            axiom = RewriteRule ruleId { ensures }
        actual <- applyRewriteRule_ initial axiom
        assertEqualWithExplanation "" expect actual

    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "conjoin rule requirement" $ do
        let
            requires =
                makeEqualsPredicate
                    (Mock.functional11 (mkVar Mock.x))
                    (Mock.functional10 (mkVar Mock.x))
            expect = Right
                [ OrPattern.fromPatterns [initial { predicate = requires }] ]
            initial = pure (mkVar Mock.x)
            axiom = RewriteRule ruleId { requires }
        actual <- applyRewriteRule_ initial axiom
        assertEqualWithExplanation "" expect actual

    , testCase "rule a => \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomBottom
        assertEqualWithExplanation "" expect actual

    , testCase "rule a => b ensures \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomEnsuresBottom
        assertEqualWithExplanation "" expect actual

    , testCase "rule a => b requires \\bottom" $ do
        let expect = Right [ ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomRequiresBottom
        assertEqualWithExplanation "" expect actual

    , testCase "rule a => \\bottom does not apply to c" $ do
        let expect = Right [ ]
            initial = pure Mock.c
        actual <- applyRewriteRule_ initial axiomRequiresBottom
        assertEqualWithExplanation "" expect actual
    ]
  where
    ruleId =
        RulePattern
            { left = mkVar Mock.x
            , right = mkVar Mock.x
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }
    axiomId = RewriteRule ruleId

    axiomBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , right = mkBottom Mock.testSort
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomEnsuresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , right = Mock.b
            , requires = makeTruePredicate
            , ensures = makeFalsePredicate
            , attributes = def
            }

    axiomRequiresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , right = Mock.b
            , requires = makeFalsePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomSigmaId =
        RewriteRule RulePattern
            { left = Mock.sigma (mkVar Mock.x) (mkVar Mock.x)
            , right = mkVar Mock.x
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomSigmaXXYY =
        RewriteRule RulePattern
            { left =
                Mock.sigma
                    (Mock.sigma (mkVar Mock.x) (mkVar Mock.x))
                    (Mock.sigma (mkVar Mock.y) (mkVar Mock.y))
            , right = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomSigmaXXY =
        RewriteRule RulePattern
            { left =
                Mock.sigma
                    (Mock.sigma (mkVar Mock.x) (mkVar Mock.x))
                    (mkVar Mock.y)
            , right = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

-- | Apply the 'RewriteRule's to the configuration.
applyRewriteRulesParallel
    :: Pattern Variable
    -- ^ Configuration
    -> [RewriteRule Variable]
    -- ^ Rewrite rule
    -> IO (Either UnificationOrSubstitutionError (Step.Results Variable))
applyRewriteRulesParallel initial rules =
    (fmap . fmap) Result.mergeResults
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier Mock.env
    $ runUnifierT
    $ Step.applyRewriteRulesParallel unificationProcedure rules initial
  where
    unificationProcedure =
        UnificationProcedure Unification.unificationProcedure

checkResults
    :: HasCallStack
    => MultiOr (Pattern Variable)
    -> Step.Results Variable
    -> Assertion
checkResults expect actual =
    assertEqualWithExplanation "compare results"
        expect
        (Step.gatherResults actual)

checkRemainders
    :: HasCallStack
    => MultiOr (Pattern Variable)
    -> Step.Results Variable
    -> Assertion
checkRemainders expect actual =
    assertEqualWithExplanation "compare remainders"
        expect
        (Step.remainders actual)

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
                        Substitution.wrap [(Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = initialTerm
                        , predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                        , substitution = mempty
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesParallel initial [axiomIfThen]
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
                            [(Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term =
                            Mock.functionalConstr20
                                (mkVar Mock.x)
                                Mock.cg
                        , predicate =
                            makeAndPredicate (makeCeilPredicate Mock.cf)
                            $ makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                        , substitution = mempty
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
            initial =
                Conditional
                    { term = initialTerm
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = mempty
                    }
        Right actual <- applyRewriteRulesParallel initial [axiomIfThen]
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
                    { term = Mock.functionalConstr10 (mkVar Mock.x)
                    , predicate = makeNotPredicate requirement
                    , substitution = mempty
                    }
            initial = pure (Mock.functionalConstr10 (mkVar Mock.x))
            requirement = makeEqualsPredicate (Mock.f (mkVar Mock.x)) Mock.b
        Right actual <- applyRewriteRulesParallel initial [axiomSignum]
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
                        Substitution.wrap [(Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesParallel initial [axiomIfThen]
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
                            Substitution.wrap [(Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap [(Mock.x, Mock.b)]
                        }
                    ]
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            Predicate.makeAndPredicate
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate definedBranches
                                    $ Predicate.makeEqualsPredicate
                                        (mkVar Mock.x)
                                        Mock.a
                                )
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate definedBranches
                                    $ Predicate.makeEqualsPredicate
                                        (mkVar Mock.x)
                                        Mock.b
                                )
                        }
                    ]
            initialTerm = Mock.functionalConstr30 (mkVar Mock.x) Mock.cf Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesParallel initial axiomsCase
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
                        Substitution.wrap [(Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results = OrPattern.fromTermLike (mkExists Mock.x (mkVar Mock.x))
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        Right actual <- applyRewriteRulesParallel initial
            [ RewriteRule RulePattern
                { left = Mock.a
                , right = mkVar Mock.x
                , requires = makeTruePredicate
                , ensures = makeTruePredicate
                , attributes = def
                }
            ]
        checkResults results actual
        checkRemainders remainders actual
    ]

axiomIfThen :: RewriteRule Variable
axiomIfThen =
    RewriteRule RulePattern
        { left = Mock.functionalConstr20 Mock.a (mkVar Mock.y)
        , right = mkVar Mock.y
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

axiomSignum :: RewriteRule Variable
axiomSignum =
    RewriteRule RulePattern
        { left = Mock.functionalConstr10 (mkVar Mock.y)
        , right = Mock.a
        , requires = makeEqualsPredicate (Mock.f (mkVar Mock.y)) Mock.b
        , ensures = makeTruePredicate
        , attributes = def
        }

axiomCaseA :: RewriteRule Variable
axiomCaseA =
    RewriteRule RulePattern
        { left =
            Mock.functionalConstr30
                Mock.a
                (mkVar Mock.y)
                (mkVar Mock.z)
        , right = mkVar Mock.y
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

axiomCaseB :: RewriteRule Variable
axiomCaseB =
    RewriteRule RulePattern
        { left =
            Mock.functionalConstr30
                Mock.b
                (mkVar Mock.y)
                (mkVar Mock.z)
        , right = mkVar Mock.z
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

axiomsCase :: [RewriteRule Variable]
axiomsCase = [axiomCaseA, axiomCaseB]


-- | Apply the 'RewriteRule's to the configuration in sequence.
applyRewriteRulesSequence
    :: Pattern Variable
    -- ^ Configuration
    -> [RewriteRule Variable]
    -- ^ Rewrite rule
    -> IO (Either UnificationOrSubstitutionError (Results Variable))
applyRewriteRulesSequence initial rules =
    (fmap . fmap) Result.mergeResults
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier Mock.env
    $ runUnifierT
    $ Step.applyRewriteRulesSequence unificationProcedure initial rules
  where
    unificationProcedure = UnificationProcedure Unification.unificationProcedure

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
                            Substitution.wrap [(Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap [(Mock.x, Mock.b)]
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
                                            (mkVar Mock.x)
                                            Mock.a
                                        )
                                )
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate
                                        definedBranches
                                        (Predicate.makeEqualsPredicate
                                            (mkVar Mock.x)
                                            Mock.b
                                        )
                                )
                        }
                    ]
            initialTerm = Mock.functionalConstr30 (mkVar Mock.x) Mock.cf Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesSequence initial axiomsCase
        checkResults results actual
        checkRemainders remainders actual

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results = OrPattern.fromTermLike (mkExists Mock.x (mkVar Mock.x))
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        Right actual <- applyRewriteRulesSequence initial
            [ RewriteRule RulePattern
                { left = Mock.a
                , right = mkVar Mock.x
                , requires = makeTruePredicate
                , ensures = makeTruePredicate
                , attributes = def
                }
            ]
        checkResults results actual
        checkRemainders remainders actual
    ]
