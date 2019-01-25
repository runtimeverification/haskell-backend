module Test.Kore.Step.Simplification.Integration
    ( test_simplificationIntegration
    , test_substituteMap
    , test_substituteList
    , test_substitute
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( Default (..) )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import           Data.These
                 ( These (..) )

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Builtin.Map as Map
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
import           Kore.Step.Function.Registry
                 ( axiomPatternsToEvaluators )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplificationIntegration :: [TestTree]
test_simplificationIntegration =
    [ testCase "owise condition - main case" $ do
        let expect = OrOfExpandedPattern.make []
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr10 Mock.a)
                                                    )
                                                )
                                                mkTop_
                                            )
                                        )
                                    )
                                    mkBottom_
                                )
                            )
                            mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "owise condition - owise case" $ do
        let expect = OrOfExpandedPattern.make [ExpandedPattern.top]
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr11 Mock.a)
                                                    )
                                                )
                                                mkTop_
                                            )
                                        )
                                    )
                                    mkBottom_
                                )
                            )
                            mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual

     , testCase "map-like simplification" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop_
                        , predicate = makeCeilPredicate
                            (mkAnd
                                (Mock.plain10 Mock.cf)
                                (Mock.plain10 (mkVar Mock.x))
                            )
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, Mock.b)]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term = mkCeil_
                        (mkAnd
                            (Mock.constr20
                                (Mock.plain10 Mock.cf)
                                Mock.b
                            )
                            (Mock.constr20
                                (Mock.plain10 (mkVar Mock.x))
                                (mkVar Mock.y)
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual
    , testCase "map function, non-matching" $ do
        let
            expect = OrOfExpandedPattern.make
                [ Predicated
                    { term = Mock.function20MapTest (Mock.builtinMap []) Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                mockMetadataTools
                (axiomPatternsToEvaluators
                    (Map.fromList
                        [   ( Mock.function20MapTestId
                            ,   [ EqualityRule RulePattern
                                    { left =
                                        Mock.function20MapTest
                                            (Mock.concatMap
                                                (Mock.elementMap
                                                    (mkVar Mock.x)
                                                    (mkVar Mock.y)
                                                )
                                                (mkVar Mock.m)
                                            )
                                            (mkVar Mock.x)
                                    , right = mkVar Mock.y
                                    , requires = makeTruePredicate
                                    , attributes = def
                                    }
                                ]
                            )
                        ]
                    )
                )
                Predicated
                    { term = Mock.function20MapTest (Mock.builtinMap []) Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual
    , testCase "map function, matching" $ do
        let
            expect = OrOfExpandedPattern.make
                [ Predicated
                    { term = Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                mockMetadataTools
                (axiomPatternsToEvaluators
                    (Map.fromList
                        [   ( Mock.function20MapTestId
                            ,   [ EqualityRule RulePattern
                                    { left =
                                        Mock.function20MapTest
                                            (Mock.concatMap
                                                (Mock.elementMap
                                                    (mkVar Mock.x)
                                                    (mkVar Mock.y)
                                                )
                                                (mkVar Mock.m)
                                            )
                                            (mkVar Mock.x)
                                    , right = mkVar Mock.y
                                    , requires = makeTruePredicate
                                    , attributes = def
                                    }
                                ]
                            )
                        ]
                    )
                )
                Predicated
                    { term =
                        Mock.function20MapTest
                            (Mock.builtinMap [(Mock.a, Mock.c)]) Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual
    ]

test_substitute :: [TestTree]
test_substitute =
    [ testCase "Substitution under unary functional constructor" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (Mock.functionalConstr10 (mkVar Mock.x))
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.a)
                            , (Mock.y, Mock.functionalConstr10 Mock.a)
                            ]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                (ExpandedPattern.fromPurePattern
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkVar Mock.x)
                            (Mock.functionalConstr10 (mkVar Mock.x))
                        )
                        (Mock.functionalConstr20 Mock.a (mkVar Mock.y))
                    )
                )
        assertEqualWithExplanation
            "Expected substitution under unary functional constructor"
            expect
            actual

    , testCase "Substitution" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term = Mock.functionalConstr20 Mock.a (mkVar Mock.y)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.a)
                            , (Mock.y, Mock.a)
                            ]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                (ExpandedPattern.fromPurePattern
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkVar Mock.x)
                            (mkVar Mock.x)
                        )
                        (Mock.functionalConstr20 Mock.a (mkVar Mock.y))
                    )
                )
        assertEqualWithExplanation "Expected substitution" expect actual
    ]

test_substituteMap :: [TestTree]
test_substituteMap =
    [ testCase "Substitution applied to Map elements" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (mkDomainBuiltinMap [(Mock.a, mkVar Mock.x)])
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.a)
                            , (Mock.y, mkDomainBuiltinMap [(Mock.a, Mock.a)])
                            ]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                (ExpandedPattern.fromPurePattern
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkVar Mock.x)
                            (mkDomainBuiltinMap [(Mock.a, mkVar Mock.x)])
                        )
                        (Mock.functionalConstr20 Mock.a (mkVar Mock.y))
                    )
                )
        assertEqualWithExplanation
            "Expected substitution applied to Map elements"
            expect
            actual
    ]
  where
    mkDomainBuiltinMap =
        mkDomainValue Mock.testSort . Domain.BuiltinMap . Map.fromList

test_substituteList :: [TestTree]
test_substituteList =
    [ testCase "Substitution applied to List elements" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (mkDomainBuiltinList [Mock.a, mkVar Mock.x])
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.a)
                            , (Mock.y, mkDomainBuiltinList [Mock.a, Mock.a])
                            ]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                ( ExpandedPattern.fromPurePattern
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkVar Mock.x)
                            (mkDomainBuiltinList [Mock.a, mkVar Mock.x])
                        )
                        (Mock.functionalConstr20 Mock.a (mkVar Mock.y))
                    )
                )
        assertEqualWithExplanation
            "Expected substitution applied to List elements"
            expect
            actual
    ]
  where
    mkDomainBuiltinList =
        mkDomainValue Mock.testSort . Domain.BuiltinList . Seq.fromList

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

evaluate
    :: MetadataTools Object StepperAttributes
    -> CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
evaluate tools patt =
    evaluateWithAxioms tools Map.empty patt

evaluateWithAxioms
    :: MetadataTools Object StepperAttributes
    -> Map.Map (Id Object) (FunctionEvaluators Object)
    -> CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
evaluateWithAxioms tools axioms patt =
    (<$>) fst $ SMT.runSMT SMT.defaultConfig $ evalSimplifier $
        ExpandedPattern.simplify
            tools
            (PredicateSubstitution.create tools simplifier)
            simplifier
            patt
  where
    simplifier
        ::  ( FreshVariable variable
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , Unparse (variable Object)
            , SortedVariable variable
            )
        => StepPatternSimplifier Object variable
    simplifier =
        Simplifier.create
            tools
            (Map.unionWith
                (\(This x) (That y) -> These x y)
                builtinAxioms
                (Map.map That axioms)
            )
    builtinAxioms :: BuiltinAndAxiomsFunctionEvaluatorMap Object
    builtinAxioms =
        Map.fromList
            [ (Mock.concatMapId, This Map.evalConcat)
            , (Mock.elementMapId, This Map.evalElement)
            ]
