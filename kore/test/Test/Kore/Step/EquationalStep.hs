module Test.Kore.Step.EquationalStep
    ( test_applyEquationalRule_
    , test_applyEquationalRulesSequence
    ) where

import Test.Tasty

import qualified Control.Exception as Exception
import Data.Default as Default
    ( def
    )
import qualified Data.Foldable as Foldable

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiOr
    ( MultiOr
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeFalsePredicate_
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate_
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.Substitution
    ( Normalization (..)
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Step.EqualityPattern as EqualityPattern
    ( EqualityPattern (..)
    , EqualityRule (..)
    , equalityPattern
    )
import Kore.Step.EquationalStep
    ( UnificationProcedure (..)
    )
import qualified Kore.Step.EquationalStep as Step
import qualified Kore.Step.Result as Result
    ( mergeResults
    )
import qualified Kore.Step.Step as Step
    ( gatherResults
    , remainders
    , result
    , results
    )
import Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationOrSubstitutionError (..)
    , unsupportedPatterns
    )
import qualified Kore.Unification.Procedure as Unification
import Kore.Unification.UnifierT
    ( MonadUnify
    , SimplifierVariable
    , runUnifierT
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

-- | Apply the 'EquationalRule' to the configuration, but discard remainders.
applyEquationalRule_
    ::  ( Pattern Variable
          -> [EqualityRule Variable]
          -> IO
            (Either
                UnificationOrSubstitutionError
                (Step.Results EqualityPattern Variable)
            )
        )
    -- ^ 'EquationalRule'
    -> Pattern Variable
    -- ^ Configuration
    -> EqualityRule Variable
    -- ^ Equational rule
    -> IO (Either UnificationOrSubstitutionError [OrPattern Variable])
applyEquationalRule_ applyEquationalRules initial rule =
    applyEquationalRules_ applyEquationalRules initial [rule]

-- | Apply the 'EquationalRule's to the configuration, but discard remainders.
applyEquationalRules_
    ::  ( Pattern Variable
          -> [EqualityRule Variable]
          -> IO
            (Either
                UnificationOrSubstitutionError
                (Step.Results EqualityPattern Variable)
            )
        )
    -- ^ 'EquationalRule's
    -> Pattern Variable
    -- ^ Configuration
    -> [EqualityRule Variable]
    -- ^ Equational rule
    -> IO (Either UnificationOrSubstitutionError [OrPattern Variable])
applyEquationalRules_ applyEquationalRules initial rules = do
    result <- applyEquationalRules initial rules
    return (Foldable.toList . discardRemainders <$> result)
  where
    discardRemainders = fmap Step.result . Step.results

test_applyEquationalRule_ :: [TestTree]
test_applyEquationalRule_ =
    [ testCase "apply identity axiom" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            initial = Pattern.fromTermLike (mkElemVar Mock.x)
        actual <- applyEquationalRuleParallel_ initial axiomId
        assertEqual "" expect actual

    , testCase "apply identity without renaming" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            initial = Pattern.fromTermLike (mkElemVar Mock.y)
        actual <- applyEquationalRuleParallel_ initial axiomId
        assertEqual "" expect actual

    , testCase "substitute variable with itself" $ do
        let expect = Right
                [ OrPattern.fromPatterns [initial { term = mkElemVar Mock.x }] ]
            initial = Pattern.fromTermLike
                (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "merge configuration patterns" $ do
        let term = Mock.functionalConstr10 (mkElemVar Mock.y)
            expect = Right
                [ OrPattern.fromPatterns [initial { term, substitution }] ]
              where
                substitution = Substitution.wrap [ (ElemVar Mock.x, term) ]
            initial = Pattern.fromTermLike (Mock.sigma (mkElemVar Mock.x) term)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "substitution with symbol matching" $ do
        let expect = Right
                [ OrPattern.fromPatterns [initial { term = fz, substitution }] ]
              where
                substitution =
                    Substitution.wrap [ (ElemVar Mock.y, mkElemVar Mock.z) ]
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            initial = Pattern.fromTermLike (Mock.sigma fy fz)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
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
            initial = Pattern.fromTermLike (Mock.sigma xy yx)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaXXYY
        assertEqual "" expect actual

    , testCase "Apply non-function-like rule in parallel" $ do
        let
            initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        result <- Exception.try $ applyEquationalRuleParallel_
                                    initial
                                    axiomSigmaTopId
        case result of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply list containing non-function-like rule in parallel" $ do
        let
            initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        result <- Exception.try $ applyEquationalRules_
                                    applyEquationalRulesSequence
                                    initial
                                    [axiomCaseA, axiomSigmaTopId]
        case result of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply non-function-like rule in sequence" $ do
        let
            initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        result <- Exception.try $ applyEquationalRule_
                                    applyEquationalRulesSequence
                                    initial
                                    axiomSigmaTopId
        case result of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "Apply list containing non-function-like rule in sequence" $ do
        let
            initial = pure (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
        result <- Exception.try $ applyEquationalRules_
                                    applyEquationalRulesSequence
                                    initial
                                    [axiomCaseA, axiomSigmaTopId]
        case result of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected error"

    , testCase "symbol clash" $ do
        let expect = Right mempty
            fx = Mock.functionalConstr10 (mkElemVar Mock.x)
            gy = Mock.functionalConstr11 (mkElemVar Mock.y)
            initial = pure (Mock.sigma fx gy)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
        assertEqual "" expect actual

    , testCase "impossible substitution" $ do
        let expect = Right mempty
            xfy =
                Mock.sigma
                    (mkElemVar Mock.x)
                    (Mock.functionalConstr10 (mkElemVar Mock.y))
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            initial = pure (Mock.sigma xfy xy)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaXXYY
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
                    , predicate = Predicate.makeTruePredicate_
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, mkElemVar Mock.x)]
                    }
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
        assertEqual "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "circular dependency error" $ do
        let expect =
                -- TODO(virgil): This should probably be a normal result with
                -- b=h(b) in the predicate.
                Left . SubstitutionError
                $ SimplifiableCycle [ElemVar Mock.y] normalization
            fy = Mock.functional10 (mkElemVar Mock.y)
            normalization = mempty { denormalized = [(ElemVar Mock.y, fy)] }
            initial =
                Conditional
                    { term = Mock.sigma (mkElemVar Mock.x) fy
                    , predicate = makeTruePredicate_
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, mkElemVar Mock.x)]
                    }
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
        assertEqual "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "non-function substitution error" $ do
        let expect = Left $ UnificationError $ unsupportedPatterns
                "Unknown unification case."
                (mkElemVar Mock.x)
                (Mock.plain10 (mkElemVar Mock.y))
            initial = pure $
                Mock.sigma (mkElemVar Mock.x) (Mock.plain10 (mkElemVar Mock.y))
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
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
                            , predicate = makeTruePredicate Mock.testSort
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
        actual <- applyEquationalRuleParallel_ initial axiomSigmaId
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
                            , predicate = makeTruePredicate Mock.testSort
                            , substitution =
                                Substitution.wrap [(ElemVar Mock.x, fb)]
                            }
                        ]
                    ]
            initial = pure $
                Mock.sigma(Mock.sigma (mkElemVar Mock.x) fb) (mkElemVar Mock.x)
        actual <- applyEquationalRuleParallel_ initial axiomSigmaXXY
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
                            , predicate = makeTruePredicate Mock.testSort
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
                    , predicate = makeTruePredicate_
                    , substitution = Substitution.wrap [(ElemVar Mock.x, fz)]
                    }
        actual <- applyEquationalRuleParallel_ initial axiomSigmaXXY
        assertEqual "" expect actual

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "unmatched string literals" $ do
        let expect = Right mempty
            initial = pure (mkStringLiteral "sl2")
            axiom =
                EqualityRule $ equalityPattern
                    (mkStringLiteral "sl1")
                    (mkElemVar Mock.x)
        actual <- applyEquationalRuleParallel_ initial axiom
        assertEqual "" expect actual

    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: a and g(a)=f(a)
    , testCase "preserve initial condition" $ do
        let expect = Right [ OrPattern.fromPatterns [initial] ]
            predicate =
                makeEqualsPredicate Mock.testSort
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            initial =
                Conditional
                    { term = Mock.a
                    , predicate
                    , substitution = mempty
                    }
        actual <- applyEquationalRuleParallel_ initial axiomId
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
                                makeEqualsPredicate Mock.testSort
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
                        makeEqualsPredicate_
                            (Mock.functional11 (mkElemVar Mock.x))
                            (Mock.functional10 (mkElemVar Mock.x))
                    , substitution = mempty
                    }
        actual <- applyEquationalRuleParallel_ initial axiomSigmaXXY
        assertEqual "" expect actual

    -- x => x ensures g(x)=f(x)
    -- vs
    -- y
    -- Expected: y and g(y)=f(y)
    , testCase "conjoin rule ensures" $ do
        let
            ensures =
                makeEqualsPredicate_
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            expect :: Either
                UnificationOrSubstitutionError [OrPattern Variable]
            expect = Right
                [ OrPattern.fromPatterns
                    [ Conditional
                        { term = mkElemVar Mock.y
                        , predicate = makeEqualsPredicate Mock.testSort
                            (Mock.functional11 (mkElemVar Mock.y))
                            (Mock.functional10 (mkElemVar Mock.y))
                        , substitution = mempty
                        }
                    ]
                ]
            initial = Pattern.fromTermLike (mkElemVar Mock.y)
            axiom = EqualityRule ruleId { ensures }
        actual <- applyEquationalRuleParallel_ initial axiom
        assertEqual "" expect actual
    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "conjoin rule requirement" $ do
        let
            requires =
                makeEqualsPredicate_
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            expect = Right
                [ OrPattern.fromPatterns
                    [ initialTerm
                    `Pattern.withCondition` Condition.fromPredicate requires
                    ]
                ]
            initialTerm = mkElemVar Mock.x
            initial = Pattern.fromTermLike initialTerm
            axiom = EqualityRule ruleId { requires }
        actual <- applyEquationalRuleParallel_ initial axiom
        assertEqual "" expect actual

    , testCase "rule a => \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyEquationalRuleParallel_ initial axiomBottom
        assertEqual "" expect actual

    , testCase "rule a => b ensures \\bottom" $ do
        let expect = Right [ OrPattern.fromPatterns [] ]
            initial = pure Mock.a
        actual <- applyEquationalRuleParallel_ initial axiomEnsuresBottom
        assertEqual "" expect actual
    , testCase "rule a => b requires \\bottom" $ do
        let expect = Right [ ]
            initial = pure Mock.a
        actual <- applyEquationalRuleParallel_ initial axiomRequiresBottom
        assertEqual "" expect actual

    , testCase "rule a => \\bottom does not apply to c" $ do
        let expect = Right [ ]
            initial = pure Mock.c
        actual <- applyEquationalRuleParallel_
                    initial
                    axiomRequiresBottom
        assertEqual "" expect actual
    ]
  where
    applyEquationalRuleParallel_ = applyEquationalRule_ applyEquationalRulesSequence

    ruleId =
        equalityPattern
            (mkElemVar Mock.x)
            (mkElemVar Mock.x)
    axiomId = EqualityRule ruleId

    axiomBottom =
        EqualityRule (equalityPattern Mock.a (mkBottom Mock.testSort))

    axiomEnsuresBottom =
        EqualityRule EqualityPattern
            { left = Mock.a
            , requires = makeTruePredicate_
            , right = Mock.b
            , ensures = makeFalsePredicate_
            , attributes = def
            }

    axiomRequiresBottom =
        EqualityRule EqualityPattern
            { left = Mock.a
            , requires = makeFalsePredicate_
            , right = Mock.b
            , ensures = makeTruePredicate_
            , attributes = def
            }

    axiomSigmaId =
        EqualityRule $ equalityPattern
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
            (mkElemVar Mock.x)

    axiomSigmaTopId =
        EqualityRule $ equalityPattern
            (Mock.sigma (mkElemVar Mock.x) mkTop_)
            (mkElemVar Mock.x)

    axiomSigmaXXYY =
        EqualityRule $ equalityPattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y))
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    axiomSigmaXXY =
        EqualityRule $ equalityPattern
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

checkResults
    :: HasCallStack
    => MultiOr (Pattern Variable)
    -> Step.Results EqualityPattern Variable
    -> Assertion
checkResults expect actual =
    assertEqual "compare results"
        expect
        (Step.gatherResults actual)

checkRemainders
    :: HasCallStack
    => MultiOr (Pattern Variable)
    -> Step.Results EqualityPattern Variable
    -> Assertion
checkRemainders expect actual =
    assertEqual "compare remainders"
        expect
        (Step.remainders actual)

axiomCaseA :: EqualityRule Variable
axiomCaseA =
    EqualityRule $ equalityPattern
        (Mock.functionalConstr30
                Mock.a
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.y)

axiomCaseB :: EqualityRule Variable
axiomCaseB =
    EqualityRule $ equalityPattern
        (Mock.functionalConstr30
                Mock.b
                (mkElemVar Mock.y)
                (mkElemVar Mock.z)
        )
        (mkElemVar Mock.z)

axiomsCase :: [EqualityRule Variable]
axiomsCase = [axiomCaseA, axiomCaseB]

applyEquationalRulesSequence_
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnificationProcedure
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> [EqualityRule variable]
    -- ^ Rewrite rules
    -> unifier (Step.Results EqualityPattern variable)
applyEquationalRulesSequence_
    unificationProcedure
    (Step.toConfigurationVariables -> initialConfig)
    (map getEqualityRule -> rules)
  = do
    results <- Step.applyRulesSequence
        unificationProcedure
        SideCondition.top
        (simplifiedPattern initialConfig)
        rules
    Step.assertFunctionLikeResults (term initialConfig) results
    return results


-- | Apply the 'EquationalRule's to the configuration in sequence.
applyEquationalRulesSequence
    :: Pattern Variable
    -- ^ Configuration
    -> [EqualityRule Variable]
    -- ^ Equational rule
    -> IO
      (Either
          UnificationOrSubstitutionError
          (Step.Results EqualityPattern Variable)
      )
applyEquationalRulesSequence initial rules =
    (fmap . fmap) Result.mergeResults
    $ runSimplifier Mock.env
    $ runUnifierT
    $ applyEquationalRulesSequence_ unificationProcedure initial rules
  where
    unificationProcedure = UnificationProcedure Unification.unificationProcedure

test_applyEquationalRulesSequence :: [TestTree]
test_applyEquationalRulesSequence =
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
                    (makeCeilPredicate Mock.testSort Mock.cf)
                    (makeCeilPredicate_ Mock.cg)
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
                                        (Predicate.makeEqualsPredicate_
                                            (mkElemVar Mock.x)
                                            Mock.a
                                        )
                                )
                                (Predicate.makeNotPredicate
                                    $ Predicate.makeAndPredicate
                                        definedBranches
                                        (Predicate.makeEqualsPredicate_
                                            (mkElemVar Mock.x)
                                            Mock.b
                                        )
                                )
                        }
                    ]
            initialTerm =
                Mock.functionalConstr30 (mkElemVar Mock.x) Mock.cf Mock.cg
            initial = pure initialTerm
        Right actual <- applyEquationalRulesSequence initial axiomsCase
        checkResults results actual
        checkRemainders remainders actual
    ]
