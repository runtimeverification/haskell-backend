module Test.Kore.Step.Step
    ( test_applyInitialConditions
    , test_unifyRule
    , test_applyRewriteRule_
    , test_applyRewriteRulesParallel
    , test_applyRewriteRulesSequence
    ) where

import Test.Tasty

import Data.Default as Default
    ( def
    )
import qualified Data.Foldable as Foldable

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Predicate.Predicate as Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeFalsePredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import qualified Kore.Step.Result as Result
    ( mergeResults
    )
import Kore.Step.Rule
    ( RewriteRule (..)
    , RulePattern (..)
    , rulePattern
    )
import qualified Kore.Step.Rule as RulePattern
import Kore.Step.Step hiding
    ( applyInitialConditions
    , applyRewriteRulesParallel
    , applyRewriteRulesSequence
    , unifyRule
    )
import qualified Kore.Step.Step as Step
import Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationOrSubstitutionError (..)
    , unsupportedPatterns
    )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify
    ( UnifierT
    , runUnifierT
    )
import Kore.Variables.Fresh
    ( nextVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

evalUnifier
    :: UnifierT Simplifier a
    -> IO (Either UnificationOrSubstitutionError [a])
evalUnifier = runSimplifier Mock.env . runUnifierT

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
        assertEqual "" expect actual

    , testCase "returns axiom right-hand side" $ do
        let unification = Predicate.top
            initial = Predicate.top
            expect = Right [MultiOr.singleton initial]
        actual <- applyInitialConditions initial unification
        assertEqual "" expect actual

    , testCase "combine initial and rule conditions" $ do
        let unification = Predicate.fromPredicate expect2
            initial = Predicate.fromPredicate expect1
            expect1 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkElemVar Mock.x)
                    Mock.a
            expect2 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkElemVar Mock.y)
                    Mock.b
            expect =
                MultiOr.singleton (Predicate.makeAndPredicate expect1 expect2)
        Right [applied] <- applyInitialConditions initial unification
        let actual = Conditional.predicate <$> applied
        assertEqual "" expect actual

    , testCase "conflicting initial and rule conditions" $ do
        let predicate = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a
            unification = Predicate.fromPredicate predicate
            initial =
                Predicate.fromPredicate
                $ Predicate.makeNotPredicate predicate
            expect = Right mempty
        actual <- applyInitialConditions initial unification
        assertEqual "" expect actual

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
        let initial = pure (Mock.f (mkElemVar Mock.x))
            axiom =
                RulePattern
                    { left = Mock.f (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , right = Mock.g (mkElemVar Mock.x)
                    , requires =
                        Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
        Right unified <- unifyRule initial axiom
        let actual = Conditional.term <$> unified
        assertBool ""
            $ Foldable.all (not . FreeVariables.isFreeVariable (ElemVar Mock.x))
            $ RulePattern.freeVariables <$> actual

    , testCase "performs unification with initial term" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr10 (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right [(pure axiom) { substitution }]
              where
                substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, Mock.a)]
        actual <- unifyRule initial axiom
        assertEqual "" expect actual

    , testCase "returns unification failures" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr11 (mkElemVar Mock.x)
                    , antiLeft = Nothing
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right []
        actual <- unifyRule initial axiom
        assertEqual "" expect actual
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
            initial = pure (mkElemVar Mock.x)
        actual <- applyRewriteRule_ initial axiomId
        assertEqual "" expect actual

    , testCase "apply identity without renaming" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            initial = pure (mkElemVar Mock.y)
        actual <- applyRewriteRule_ initial axiomId
        assertEqual "" expect actual

    , testCase "substitute variable with itself" $ do
        let expect = Right
                [ OrPattern.fromPatterns [initial { term = mkElemVar Mock.x }] ]
            initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "merge configuration patterns" $ do
        let term = Mock.functionalConstr10 (mkElemVar Mock.y)
            expect = Right
                [ OrPattern.fromPatterns [initial { term, substitution }] ]
              where
                substitution = Substitution.wrap [ (ElemVar Mock.x, term) ]
            initial = pure (Mock.sigma (mkElemVar Mock.x) term)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "substitution with symbol matching" $ do
        let expect = Right
                [ OrPattern.fromPatterns [initial { term = fz, substitution }] ]
              where
                substitution =
                    Substitution.wrap [ (ElemVar Mock.y, mkElemVar Mock.z) ]
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            initial = pure (Mock.sigma fy fz)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "merge multiple variables" $ do
        let expect = Right
                [ OrPattern.fromPatterns [initial { term = yy, substitution }] ]
              where
                substitution =
                    Substitution.wrap [ (ElemVar Mock.x, mkElemVar Mock.y) ]
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            yx = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.x)
            yy = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y)
            initial = pure (Mock.sigma xy yx)
        actual <- applyRewriteRule_ initial axiomSigmaXXYY
        assertEqual "" expect actual

    , testCase "rename quantified right variables" $ do
        let expect = Right [ OrPattern.fromPatterns [pure final] ]
            final = mkExists (nextVariable <$> Mock.y) (mkElemVar Mock.y)
            initial = pure (mkElemVar Mock.y)
            axiom =
                RewriteRule $ rulePattern
                    (mkElemVar Mock.x)
                    (mkExists Mock.y (mkElemVar Mock.x))
        actual <- applyRewriteRule_ initial axiom
        assertEqual "" expect actual

    , testCase "symbol clash" $ do
        let expect = Right mempty
            fx = Mock.functionalConstr10 (mkElemVar Mock.x)
            gy = Mock.functionalConstr11 (mkElemVar Mock.y)
            initial = pure (Mock.sigma fx gy)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "impossible substitution" $ do
        let expect = Right mempty
            xfy =
                Mock.sigma
                    (mkElemVar Mock.x)
                    (Mock.functionalConstr10 (mkElemVar Mock.y))
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            initial = pure (Mock.sigma xfy xy)
        actual <- applyRewriteRule_ initial axiomSigmaXXYY
        assertEqual "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "impossible substitution (ctor)" $ do
        let expect = Right mempty
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (mkElemVar Mock.x)
                            (Mock.functionalConstr10 (mkElemVar Mock.y))
                    , predicate = Predicate.makeTruePredicate
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, mkElemVar Mock.x)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "circular dependency error" $ do
        let expect =
                -- TODO(virgil): This should probably be a normal result with
                -- b=h(b) in the predicate.
                Left
                $ SubstitutionError
                $ SimplifiableCycle [ElemVar Mock.y]
            initial =
                Conditional
                    { term =
                        Mock.sigma
                            (mkElemVar Mock.x)
                            (Mock.functional10 (mkElemVar Mock.y))
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, mkElemVar Mock.x)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "non-function substitution error" $ do
        let expect = Left $ UnificationError $ unsupportedPatterns
                "Unknown unification case."
                (mkElemVar (nextVariable <$> Mock.x))
                (Mock.plain10 (mkElemVar Mock.y))
            initial = pure $
                Mock.sigma (mkElemVar Mock.x) (Mock.plain10 (mkElemVar Mock.y))
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

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
                                [ (ElemVar Mock.x, zz)
                                , (ElemVar Mock.y, mkElemVar Mock.z)
                                ]
                            }
                        ]
                    ]
            xx = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x)
            yy = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y)
            zz = Mock.sigma (mkElemVar Mock.z) (mkElemVar Mock.z)
            yz = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z)
            initial = pure $ Mock.sigma xx (Mock.sigma yz yy)
        actual <- applyRewriteRule_ initial axiomSigmaId
        assertEqual "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "normalize substitution" $ do
        let
            fb = Mock.functional10 (mkElemVar Mock.y)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap [(ElemVar Mock.x, fb)]
                            }
                        ]
                    ]
            initial = pure $
                Mock.sigma(Mock.sigma (mkElemVar Mock.x) fb) (mkElemVar Mock.x)
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqual "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , testCase "merge substitution with initial" $ do
        let
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fz fz
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.wrap
                                    [ (ElemVar Mock.x, fz)
                                    , (ElemVar Mock.y, mkElemVar Mock.z)
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
                    , substitution = Substitution.wrap [(ElemVar Mock.x, fz)]
                    }
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqual "" expect actual

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "unmatched string literals" $ do
        let expect = Right mempty
            initial = pure (mkStringLiteral "sl2")
            axiom =
                RewriteRule $ rulePattern
                    (mkStringLiteral "sl1")
                    (mkElemVar Mock.x)
        actual <- applyRewriteRule_ initial axiom
        assertEqual "" expect actual

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
        assertEqual "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    , testCase "normalize substitution with initial condition" $ do
        let
            fb = Mock.functional10 (mkElemVar Mock.y)
            expect =
                Right
                    [ OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma fb fb
                            , predicate =
                                makeEqualsPredicate
                                    (Mock.functional11 fb)
                                    (Mock.functional10 fb)
                            , substitution =
                                Substitution.wrap [(ElemVar Mock.x, fb)]
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
        actual <- applyRewriteRule_ initial axiomSigmaXXY
        assertEqual "" expect actual

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
            expect :: Either
                UnificationOrSubstitutionError [OrPattern Variable]
            expect = Right
                [ OrPattern.fromPatterns
                    [ Conditional
                        { term = mkElemVar Mock.y
                        , predicate = makeEqualsPredicate
                            (Mock.functional11 (mkElemVar Mock.y))
                            (Mock.functional10 (mkElemVar Mock.y))
                        , substitution = mempty
                        }
                    ]
                ]
            initial = Pattern.fromTermLike (mkElemVar Mock.y)
            axiom = RewriteRule ruleId { ensures }
        actual <- applyRewriteRule_ initial axiom
        assertEqual "" expect actual

    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "conjoin rule requirement" $ do
        let
            requires =
                makeEqualsPredicate
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            expect = Right
                [ OrPattern.fromPatterns [initial { predicate = requires }] ]
            initial = pure (mkElemVar Mock.x)
            axiom = RewriteRule ruleId { requires }
        actual <- applyRewriteRule_ initial axiom
        assertEqual "" expect actual

    , testCase "rule a => \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomBottom
        assertEqual "" expect actual

    , testCase "rule a => b ensures \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomEnsuresBottom
        assertEqual "" expect actual

    , testCase "rule a => b requires \\bottom" $ do
        let expect = Right [ ]
            initial = pure Mock.a
        actual <- applyRewriteRule_ initial axiomRequiresBottom
        assertEqual "" expect actual

    , testCase "rule a => \\bottom does not apply to c" $ do
        let expect = Right [ ]
            initial = pure Mock.c
        actual <- applyRewriteRule_ initial axiomRequiresBottom
        assertEqual "" expect actual
    ]
  where
    ruleId =
        rulePattern
            (mkElemVar Mock.x)
            (mkElemVar Mock.x)
    axiomId = RewriteRule ruleId

    axiomBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , right = mkBottom Mock.testSort
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomEnsuresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , right = Mock.b
            , requires = makeTruePredicate
            , ensures = makeFalsePredicate
            , attributes = def
            }

    axiomRequiresBottom =
        RewriteRule RulePattern
            { left = Mock.a
            , antiLeft = Nothing
            , right = Mock.b
            , requires = makeFalsePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }

    axiomSigmaId =
        RewriteRule $ rulePattern
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
            (mkElemVar Mock.x)

    axiomSigmaXXYY =
        RewriteRule $ rulePattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y))
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    axiomSigmaXXY =
        RewriteRule $ rulePattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

-- | Apply the 'RewriteRule's to the configuration.
applyRewriteRulesParallel
    :: Pattern Variable
    -- ^ Configuration
    -> [RewriteRule Variable]
    -- ^ Rewrite rule
    -> IO (Either UnificationOrSubstitutionError (Step.Results Variable))
applyRewriteRulesParallel initial rules =
    (fmap . fmap) Result.mergeResults
    $ runSimplifier Mock.env
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
    assertEqual "compare results"
        expect
        (Step.gatherResults actual)

checkRemainders
    :: HasCallStack
    => MultiOr (Pattern Variable)
    -> Step.Results Variable
    -> Assertion
checkRemainders expect actual =
    assertEqual "compare remainders"
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
                        Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = initialTerm
                        , predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
                        , substitution = mempty
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
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
                            [(ElemVar Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ Conditional
                        { term =
                            Mock.functionalConstr20
                                (mkElemVar Mock.x)
                                Mock.cg
                        , predicate =
                            makeAndPredicate (makeCeilPredicate Mock.cf)
                            $ makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
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
                    { term = Mock.functionalConstr10 (mkElemVar Mock.x)
                    , predicate = makeNotPredicate requirement
                    , substitution = mempty
                    }
            initial = pure (Mock.functionalConstr10 (mkElemVar Mock.x))
            requirement = makeEqualsPredicate (Mock.f (mkElemVar Mock.x)) Mock.b
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
                        Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
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
                            Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap [(ElemVar Mock.x, Mock.b)]
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
                                        (mkElemVar Mock.x)
                                        Mock.a
                                )
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate definedBranches
                                    $ Predicate.makeEqualsPredicate
                                        (mkElemVar Mock.x)
                                        Mock.b
                                )
                        }
                    ]
            initialTerm =
                Mock.functionalConstr30 (mkElemVar Mock.x) Mock.cf Mock.cg
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
                        Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                    }
            remainders =
                OrPattern.fromPatterns
                    [ initial
                        { predicate =
                            makeNotPredicate
                            $ makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
                        }
                    ]
            initialTerm = Mock.functionalConstr20 (mkElemVar Mock.x) Mock.cg
            initial = pure initialTerm
        Right actual <- applyRewriteRulesParallel initial [axiomIfThen]
        checkResults results actual
        checkRemainders remainders actual

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results =
                OrPattern.fromTermLike (mkExists Mock.x (mkElemVar Mock.x))
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        Right actual <- applyRewriteRulesParallel initial
            [ RewriteRule RulePattern
                { left = Mock.a
                , antiLeft = Nothing
                , right = mkElemVar Mock.x
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
    RewriteRule $ rulePattern
        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
        (mkElemVar Mock.y)

axiomSignum :: RewriteRule Variable
axiomSignum =
    RewriteRule RulePattern
        { left = Mock.functionalConstr10 (mkElemVar Mock.y)
        , antiLeft = Nothing
        , right = Mock.a
        , requires = makeEqualsPredicate (Mock.f (mkElemVar Mock.y)) Mock.b
        , ensures = makeTruePredicate
        , attributes = def
        }

axiomCaseA :: RewriteRule Variable
axiomCaseA =
    RewriteRule $ rulePattern
        (Mock.functionalConstr30
                Mock.a
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.y)

axiomCaseB :: RewriteRule Variable
axiomCaseB =
    RewriteRule $ rulePattern
        (Mock.functionalConstr30
                Mock.b
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.z)

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
    $ runSimplifier Mock.env
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
                            Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.cg
                        , predicate = definedBranches
                        , substitution =
                            Substitution.wrap [(ElemVar Mock.x, Mock.b)]
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
        Right actual <- applyRewriteRulesSequence initial axiomsCase
        checkResults results actual
        checkRemainders remainders actual

    , testCase "adding variables" $ do
        -- Term: a
        -- Rule: a => x
        -- Expected: exists x . x
        let
            results =
                OrPattern.fromTermLike (mkExists Mock.x (mkElemVar Mock.x))
            remainders = OrPattern.bottom
            initialTerm = Mock.a
            initial = Pattern.fromTermLike initialTerm
        Right actual <- applyRewriteRulesSequence initial
            [ RewriteRule $ rulePattern
                Mock.a
                (mkElemVar Mock.x)
            ]
        checkResults results actual
        checkRemainders remainders actual
    ]
