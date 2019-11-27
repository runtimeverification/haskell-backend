module Test.Kore.Unification.UnifierT
    ( test_mergeAndNormalizeSubstitutions
    , test_simplifyCondition
    ) where

import Test.Tasty

import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map

import qualified Branch
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Step.Axiom.EvaluationStrategy as EvaluationStrategy
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import Kore.Step.Rule
    ( EqualityRule (..)
    , rulePattern
    )
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.Data
    ( Env (..)
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Error
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.UnifierT as Monad.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty.HUnit.Ext

test_simplifyCondition :: [TestTree]
test_simplifyCondition =
    [ testCase "predicate = \\bottom" $ do
        let expect = mempty
        actual <- normalize Condition.bottomCondition
        assertEqual "Expected empty result" expect actual
        assertNormalizedPredicatesMulti actual
    , testCase "∃ y z. x = σ(y, z)" $ do
        let expect = Condition.fromPredicate existsPredicate
        actual <- normalizeExcept expect
        assertEqual
            "Expected original result"
            (Right $ MultiOr.make [expect])
            actual
        Foldable.traverse_ assertNormalizedPredicatesMulti actual
    , testCase "¬∃ y z. x = σ(y, z)" $ do
        let expect =
                Condition.fromPredicate
                $ Predicate.makeNotPredicate existsPredicate
        actual <- normalizeExcept expect
        assertEqual
            "Expected original result"
            (Right $ MultiOr.make [expect])
            actual
        Foldable.traverse_ assertNormalizedPredicatesMulti actual
    , testCase "x = f(x)" $ do
        let x = ElemVar Mock.x
            expect = (Left . SubstitutionError) (SimplifiableCycle [x])
            input =
                (Condition.fromSubstitution . Substitution.wrap)
                    [(x, Mock.f (mkVar x))]
        actual <- normalizeExcept input
        assertEqual "Expected SubstitutionError" expect actual
    , testCase "x = id(x)" $ do
        let x = ElemVar Mock.x
            expect = Right (OrCondition.fromCondition Condition.top)
            input =
                (Condition.fromSubstitution . Substitution.wrap)
                    [(x, Mock.functional10 (mkVar x))]
        actual <- normalizeExcept input
        assertEqual "Expected \\top" expect actual
    ]
  where
    existsPredicate =
        Predicate.makeMultipleExists [Mock.y, Mock.z]
        $ Predicate.makeEqualsPredicate_
            (mkElemVar Mock.x)
            (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z))

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions =
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        $ do
            let expect = Right
                    [ Condition.fromSubstitution $ Substitution.unsafeWrap
                        [ ( ElemVar Mock.x , Mock.constr10 Mock.a ) ]
                    ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor normalization with variables"
        -- [x=constructor(y)] + [x=constructor(y)]  === [x=constructor(y)]
        $ do
            let expect = Right
                    [ Condition.fromSubstitution $ Substitution.unsafeWrap
                        [(ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))]
                    ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Double constructor is bottom"
        -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
        $ do
            let expect = Right []
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.constr10 Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Double constructor is bottom with variables"
        -- [x=constructor(y)] + [x=constructor(constructor(y))]  === bottom?
        $ do
            let expect = Left $ UnificationError $ unsupportedPatterns
                    "Unknown unification case."
                    (Mock.constr10 (mkElemVar Mock.y))
                    (mkElemVar Mock.y)
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.constr10 (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of function"
        -- [x=constructor(a)] + [x=constructor(f(a))]
        $ do
            let expect =
                    Right
                        [ Conditional
                            { term = ()
                            , predicate =
                                Predicate.makeEqualsPredicate_
                                    Mock.a
                                    (Mock.f Mock.a)
                            , substitution = Substitution.unsafeWrap
                                [   ( ElemVar Mock.x
                                    , Mock.constr10 Mock.a
                                    )
                                ]
                            }
                        ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.f Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of function with variables"
        -- [x=constructor(y)] + [x=constructor(f(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (SimplifiableCycle [ElemVar Mock.y])
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.f (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of functional symbol"
        -- [x=constructor(y)] + [x=constructor(functional(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (SimplifiableCycle [ElemVar Mock.y])
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.functional10 (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor circular dependency?"
        -- [x=y] + [y=constructor(x)]  === error
        $ do
            let expect = Left $ UnificationError $ unsupportedPatterns
                    "Unknown unification case."
                    (Mock.constr10 (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , mkElemVar Mock.y
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Non-ctor circular dependency"
        -- [x=y] + [y=f(x)]  === error
        $ do
            let expect =
                    Left
                    $ SubstitutionError
                    $ SimplifiableCycle
                        [ ElemVar Mock.x, ElemVar Mock.y ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , mkElemVar Mock.y
                        )
                    ]
                    [   ( ElemVar Mock.y
                        , Mock.f (mkElemVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Normalizes substitution"
        $ do
            let expect =
                    [ Condition.fromSubstitution $ Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                        , (ElemVar Mock.y, Mock.a)
                        ]
                    ]
            actual <-
                normalize
                $ Condition.fromSubstitution $ Substitution.wrap
                    [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                    , (ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual

    , testCase "Predicate from normalizing substitution"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeEqualsPredicate_ Mock.cf Mock.cg
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.cf) ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate = Predicate.makeTruePredicate_
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.cf)
                            , (ElemVar Mock.x, Mock.constr10 Mock.cg)
                            ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual

    , testCase "Normalizes substitution and substitutes in predicate"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeCeilPredicate_
                            $ Mock.f Mock.a
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                            , (ElemVar Mock.y, Mock.a)
                            ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeCeilPredicate_
                            $ Mock.f (mkElemVar Mock.y)
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                            , (ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))
                            ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    ]

merge
    :: [(UnifiedVariable Variable, TermLike Variable)]
    -> [(UnifiedVariable Variable, TermLike Variable)]
    -> IO (Either UnificationOrSubstitutionError [Condition Variable])
merge s1 s2 =
    Test.runSimplifier mockEnv
    $ Monad.Unify.runUnifierT
    $ mergeSubstitutionsExcept $ Substitution.wrap <$> [s1, s2]
  where
    mergeSubstitutionsExcept =
        Branch.alternate
        . Simplifier.simplifyCondition
        . Condition.fromSubstitution
        . mconcat
    mockEnv = Mock.env

normalize :: Conditional Variable term -> IO [Conditional Variable term]
normalize = Test.runSimplifierBranch mockEnv . Condition.simplifyCondition
  where
    mockEnv = Mock.env

normalizeExcept
    :: Conditional Variable ()
    -> IO
        (Either
            UnificationOrSubstitutionError
            (MultiOr (Conditional Variable ()))
        )
normalizeExcept predicated =
    (fmap . fmap) MultiOr.make
    $ Test.runSimplifier mockEnv
    $ Monad.Unify.runUnifierT
    $ Branch.alternate
    $ Simplifier.simplifyCondition predicated
  where
    mockEnv = Mock.env { simplifierAxioms }
    simplifierAxioms =
        -- Use Mock.functional10 as the identity function.
        Map.fromList
            [   ( Axiom.Identifier.Application Mock.functional10Id
                , EvaluationStrategy.definitionEvaluation
                    [ EqualityRule $ rulePattern
                        (Mock.functional10 (mkElemVar Mock.x))
                        (mkElemVar Mock.x)
                    ]
                )
            ]


-- | Check that 'Condition.substitution' is normalized for all arguments.
assertNormalizedPredicates :: Foldable f => f [Condition Variable] -> Assertion
assertNormalizedPredicates =
    Foldable.traverse_ assertNormalizedPredicatesMulti

-- | Check that 'Condition.substitution' is normalized for all arguments.
assertNormalizedPredicatesMulti
    :: Foldable f => f (Condition Variable) -> Assertion
assertNormalizedPredicatesMulti =
    Foldable.traverse_ assertNormalizedPredicatesSingle

-- | Check that 'Condition.substitution' is normalized for all arguments.
assertNormalizedPredicatesSingle :: Condition Variable -> Assertion
assertNormalizedPredicatesSingle =
    assertBool "Substitution is normalized"
    . Substitution.isNormalized
    . Condition.substitution
