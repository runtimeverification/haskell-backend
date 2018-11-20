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
import           Data.Reflection
                 ( give )
import qualified Data.Sequence as Seq
import           Data.These
                 ( These (..) )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import qualified Kore.Builtin.Map as Map
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( AxiomPattern (..) )
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
                 ( PureMLPatternSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplificationIntegration :: [TestTree]
test_simplificationIntegration = give mockSymbolOrAliasSorts
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
                                            mkTop
                                            (mkAnd
                                                (mkCeil
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr10 Mock.a)
                                                    )
                                                )
                                                mkTop
                                            )
                                        )
                                    )
                                    mkBottom
                                )
                            )
                            mkTop
                    , predicate = makeTruePredicate
                    , substitution = []
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
                                            mkTop
                                            (mkAnd
                                                (mkCeil
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr11 Mock.a)
                                                    )
                                                )
                                                mkTop
                                            )
                                        )
                                    )
                                    mkBottom
                                )
                            )
                            mkTop
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
        assertEqualWithExplanation "" expect actual

     , testCase "map-like simplification" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate
                            (mkAnd
                                (Mock.plain10 Mock.cf)
                                (Mock.plain10 (mkVar Mock.x))
                            )
                        , substitution = [(Mock.y, Mock.b)]
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term = mkCeil
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
                    , substitution = []
                    }
        assertEqualWithExplanation "" expect actual
    , testCase "zzzmap function" $ do
        let expect = OrOfExpandedPattern.make []
        actual <-
            evaluateWithAxioms
                mockMetadataTools
                (axiomPatternsToEvaluators
                    (Map.fromList
                        [   ( Mock.function20MapTestId
                            ,   [ AxiomPattern
                                    { axiomPatternLeft =
                                        Mock.function20MapTest
                                            (Mock.concatMap
                                                (Mock.elementMap
                                                    (mkVar Mock.x)
                                                    (mkVar Mock.y)
                                                )
                                                (mkVar Mock.m)
                                            )
                                            (mkVar Mock.x)
                                    , axiomPatternRight = mkVar Mock.y
                                    , axiomPatternRequires = makeTruePredicate
                                    , axiomPatternAttributes = def
                                    }
                                ]
                            )
                        ]
                    )
                )
                Predicated
                    { term = Mock.function20MapTest (Mock.builtinMap []) Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
        assertEqualWithExplanation "" expect actual
    ]

test_substitute :: [TestTree]
test_substitute =
    give mockSymbolOrAliasSorts
    [ testCase "Substitution under unary functional constructor" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (Mock.functionalConstr10 (mkVar Mock.x))
                        , predicate = makeTruePredicate
                        , substitution =
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
                        , substitution =
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
    give mockSymbolOrAliasSorts
    [ testCase "Substitution applied to Map elements" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (mkBuiltinDomainMap [(Mock.a, mkVar Mock.x)])
                        , predicate = makeTruePredicate
                        , substitution =
                            [ (Mock.x, Mock.a)
                            , (Mock.y, mkBuiltinDomainMap [(Mock.a, Mock.a)])
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
                            (mkBuiltinDomainMap [(Mock.a, mkVar Mock.x)])
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
    mkBuiltinDomainMap =
        give mockSymbolOrAliasSorts
            mkDomainValue Mock.testSort . BuiltinDomainMap . Map.fromList

test_substituteList :: [TestTree]
test_substituteList =
    give mockSymbolOrAliasSorts
    [ testCase "Substitution applied to List elements" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ ExpandedPattern.Predicated
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (mkBuiltinDomainList [Mock.a, mkVar Mock.x])
                        , predicate = makeTruePredicate
                        , substitution =
                            [ (Mock.x, Mock.a)
                            , (Mock.y, mkBuiltinDomainList [Mock.a, Mock.a])
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
                            (mkBuiltinDomainList [Mock.a, mkVar Mock.x])
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
    mkBuiltinDomainList =
        give mockSymbolOrAliasSorts
            mkDomainValue Mock.testSort . BuiltinDomainList . Seq.fromList

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts =
    Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        mockSymbolOrAliasSorts
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.subsorts

evaluate
    :: MetadataTools Object StepperAttributes
    -> CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
evaluate tools patt =
    evaluateWithAxioms tools Map.empty patt

evaluateWithAxioms
    :: MetadataTools Object StepperAttributes
    -> Map.Map (Id Object) [ApplicationFunctionEvaluator Object]
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
            , Hashable variable
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , SortedVariable variable
            )
        => PureMLPatternSimplifier Object variable
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
