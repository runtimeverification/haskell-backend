module Test.Kore.Step.Simplification.Condition
    ( test_predicateSimplification
    ) where

import Test.Tasty

import qualified Data.Map as Map

import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate_
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
import Kore.Step.Axiom.EvaluationStrategy
    ( firstFullEvaluation
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty.HUnit.Ext

test_predicateSimplification :: [TestTree]
test_predicateSimplification =
    [ testCase "Identity for top and bottom" $ do
        actualBottom <- runSimplifier Map.empty Conditional.bottomCondition
        assertEqual "" mempty actualBottom
        actualTop <- runSimplifier Map.empty Conditional.topCondition
        assertEqual ""
            (MultiOr.singleton Conditional.topCondition)
            actualTop

    , testCase "Applies substitution to predicate" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f Mock.a)
                            (Mock.g Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            Mock.functional00
                            Mock.functional01
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.constr10 (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate_ Mock.functional00 Mock.a
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [   ( Mock.f Mock.functional00
                                    , Mock.functional00
                                    )
                                , (Mock.f Mock.functional01, Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate_
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a) ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Reapplies substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f Mock.a)
                            (Mock.g Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate_
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate_
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies after reapplying substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.g Mock.b)
                            (Mock.g Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                , (Mock.f Mock.a, Mock.g Mock.b)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate_
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate_
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    ]

runSimplifier
    :: BuiltinAndAxiomSimplifierMap
    -> Condition Variable
    -> IO (OrCondition Variable)
runSimplifier patternSimplifierMap predicate =
    fmap MultiOr.make
    $ Test.runSimplifierBranch env
    $ simplifier predicate
  where
    env = Mock.env { Test.simplifierAxioms = patternSimplifierMap }
    ConditionSimplifier simplifier =
        Condition.create SubstitutionSimplifier.substitutionSimplifier

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeEvaluator
    :: (forall variable. SimplifierVariable variable
        => [(TermLike variable, TermLike variable)]
        )
    -> BuiltinAndAxiomSimplifier
makeEvaluator mapping = BuiltinAndAxiomSimplifier $ simpleEvaluator mapping

simpleEvaluator
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => [(TermLike variable, TermLike variable)]
    -> TermLike variable
    -> Condition variable
    -> simplifier (AttemptedAxiom variable)
simpleEvaluator [] _  _ = return NotApplicable
simpleEvaluator ((from, to) : ps) patt predicate
  | from == patt =
    return $ Applied AttemptedAxiomResults
        { results = OrPattern.fromTermLike to
        , remainders = OrPattern.bottom
        }
  | otherwise =
    simpleEvaluator ps patt predicate
