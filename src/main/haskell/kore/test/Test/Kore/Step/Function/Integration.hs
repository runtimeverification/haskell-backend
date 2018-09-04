module Test.Kore.Step.Function.Integration (test_functionIntegration) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Application (..), Id (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkOr, mkVar )
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.BaseStep
                 ( AxiomPattern (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..),
                 CommonApplicationFunctionEvaluator, CommonAttemptedFunction )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.UserDefined
                 ( axiomFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier, SimplificationProof (..),
                 Simplifier, evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import           Kore.Step.StepperAttributes

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_functionIntegration :: [TestTree]
test_functionIntegration = give mockSortTools
    [ testCase "Simple evaluation"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = Mock.g Mock.c
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.functionalConstr10Id
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.g (mkVar Mock.x))
                    ]
                )
                (Mock.functionalConstr10 Mock.c)
            )
        )
    , testCase "Evaluates inside functions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = Mock.functional10 (Mock.functional10 Mock.c)
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.functionalConstr10Id
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    ]
                )
                (Mock.functionalConstr10 (Mock.functionalConstr10 Mock.c))
            )
        )
    , testCase "Evaluates 'or'"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term =
                    mkOr
                        (Mock.functional10 (Mock.functional10 Mock.c))
                        (Mock.functional10 (Mock.functional10 Mock.d))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.functionalConstr10Id
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    ]
                )
                (Mock.functionalConstr10
                    (mkOr
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.d)
                    )
                )
            )
        )
    , testCase "Evaluates on multiple branches"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term =
                    Mock.functional10
                        (Mock.functional20
                            (Mock.functional10 Mock.c)
                            (Mock.functional10 Mock.c)
                        )
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.functionalConstr10Id
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    ]
                )
                (Mock.functionalConstr10
                    (Mock.functional20
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.c)
                    )
                )
            )
        )
    , testCase "Returns conditions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = Mock.f Mock.d
                , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.cId
                    [ appliedMockEvaluator ExpandedPattern
                        { term   = Mock.d
                        , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                        , substitution = []
                        }
                    ]
                )
                (Mock.f Mock.c)
            )
        )
    , testCase "Merges conditions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                , predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cg)
                        (makeCeilPredicate Mock.cf)
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( Mock.cId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = Mock.e
                                , predicate = makeCeilPredicate Mock.cg
                                , substitution = []
                                }
                            ]
                        )
                    ,   ( Mock.dId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = Mock.e
                                , predicate = makeCeilPredicate Mock.cf
                                , substitution = []
                                }
                            ]
                        )
                    ,   (Mock.functionalConstr10Id
                        ,   [ axiomEvaluator
                                (Mock.functionalConstr10 (mkVar Mock.x))
                                (Mock.functional11 (mkVar Mock.x))
                            ]
                        )
                    ]
                )
                (Mock.functionalConstr10 (Mock.functional20 Mock.c Mock.d))
            )
        )
    , testCase "Reevaluates user-defined function results."
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = Mock.f Mock.e
                , predicate = makeEqualsPredicate (Mock.f Mock.e) Mock.e
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( Mock.cId
                        ,   [ axiomEvaluator Mock.c Mock.d ]
                        )
                    ,   ( Mock.dId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = Mock.e
                                , predicate =
                                    makeEqualsPredicate (Mock.f Mock.e) Mock.e
                                , substitution = []
                                }
                            ]
                        )
                    ]
                )
                (Mock.f Mock.c)
            )
        )
    ]


axiomEvaluator
    :: CommonPurePattern Object domain
    -> CommonPurePattern Object domain
    -> CommonApplicationFunctionEvaluator Object
axiomEvaluator left right =
    ApplicationFunctionEvaluator
        (axiomFunctionEvaluator
            AxiomPattern
                { axiomPatternLeft  = left
                , axiomPatternRight = right
                , axiomPatternRequires = makeTruePredicate
                , axiomAttributes = def
                }
        )

appliedMockEvaluator
    :: CommonExpandedPattern level domain -> CommonApplicationFunctionEvaluator level
appliedMockEvaluator result =
    ApplicationFunctionEvaluator
        (mockEvaluator
            (AttemptedFunction.Applied (OrOfExpandedPattern.make [result]))
        )

mockEvaluator
    :: CommonAttemptedFunction level
    -> MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -> Application level (CommonPurePattern level domain)
    -> Simplifier
        (CommonAttemptedFunction level, SimplificationProof level)
mockEvaluator evaluation _ _ _ =
    return (evaluation, SimplificationProof)

evaluate
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
    -> CommonPurePattern level domain
    -> CommonExpandedPattern level domain
evaluate metadataTools functionIdToEvaluator patt =
    either (error . printError) fst
        $ evalSimplifier
        $ Pattern.simplify metadataTools functionIdToEvaluator patt

mockSortTools :: SortTools Object
mockSortTools = Mock.makeSortTools Mock.sortToolsMapping

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools = Mock.makeMetadataTools mockSortTools Mock.attributesMapping
