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
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )
import qualified Data.Sequence as Seq

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
                 ( ApplicationFunctionEvaluator )
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

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplificationIntegration :: [TestTree]
test_simplificationIntegration = give mockSymbolOrAliasSorts
    [ testCase "owise condition - main case"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluate
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
            )
        )
    , testCase "owise condition - owise case"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ExpandedPattern.top])
            (evaluate
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
            )
        )
    , testCase "map-like simplification"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate = makeCeilPredicate
                        (mkAnd
                            (Mock.plain10 Mock.cf)
                            (Mock.plain10 (mkVar Mock.x))
                        )
                    , substitution = [(Mock.y, Mock.b)]
                    }
                ])
            (evaluate
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
            )
        )
    , testCase "zzzmap function"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluateWithAxioms
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
            )
        )
    ]

test_substitute :: [TestTree]
test_substitute =
    give mockSymbolOrAliasSorts
    [ testCase "Substitution under unary functional constructor"
        (assertEqualWithExplanation
            "Expected substitution under unary functional constructor"
            (OrOfExpandedPattern.make
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
            )
            (evaluate
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
            )
        )
    , testCase "Substitution"
        (assertEqualWithExplanation
            "Expected substitution"
            (OrOfExpandedPattern.make
                [ ExpandedPattern.Predicated
                    { term = Mock.functionalConstr20 Mock.a (mkVar Mock.y)
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.a)
                        ]
                    }
                ]
            )
            (evaluate
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
            )
        )
    ]

test_substituteMap :: [TestTree]
test_substituteMap =
    give mockSymbolOrAliasSorts
    [ testCase "Substitution applied to Map elements"
        (assertEqualWithExplanation
            "Expected substitution applied to Map elements"
            (OrOfExpandedPattern.make
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
            )
            (evaluate
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
            )
        )
    ]
  where
    mkBuiltinDomainMap =
        give mockSymbolOrAliasSorts
            mkDomainValue Mock.testSort . BuiltinDomainMap . Map.fromList

test_substituteList :: [TestTree]
test_substituteList =
    give mockSymbolOrAliasSorts
    [ testCase "Substitution applied to List elements"
        (assertEqualWithExplanation
            "Expected substitution applied to List elements"
            ( OrOfExpandedPattern.make
                [ ExpandedPattern.Predicated
                    { term =
                        Mock.functionalConstr20
                            Mock.a
                            (mkBuiltinDomainList [Mock.a, mkVar Mock.x])
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a), (Mock.y, mkBuiltinDomainList [Mock.a, Mock.a])]
                    }
                ]
            )
            (evaluate
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
            )
        )
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
    -> CommonOrOfExpandedPattern Object
evaluate tools patt =
    evaluateWithAxioms tools Map.empty patt

evaluateWithAxioms
    :: MetadataTools Object StepperAttributes
    -> Map.Map (Id Object) [ApplicationFunctionEvaluator Object]
    -> CommonExpandedPattern Object
    -> CommonOrOfExpandedPattern Object
evaluateWithAxioms tools axioms patt =
    fst $ evalSimplifier $
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
            (Map.unionWith (++) axioms builtinAxioms)
    builtinAxioms =
        Map.fromList
            [ (Mock.concatMapId, [Map.evalConcat])
            , (Mock.elementMapId, [Map.evalElement])
            ]

