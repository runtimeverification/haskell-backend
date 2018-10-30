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
                 ( Application (..), CommonPurePattern, Id (..), PureMLPattern,
                 SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkOr, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.BaseStep
                 ( AxiomPattern (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern,
                 Predicated (Predicated) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), mapVariables )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..) )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.UserDefined
                 ( axiomFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 PureMLPatternSimplifier, SimplificationProof (..), Simplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh
                 ( FreshVariable, freshVariableFromVariable )


import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_functionIntegration :: [TestTree]
test_functionIntegration = give mockSymbolOrAliasSorts
    [ testCase "Simple evaluation"
        (assertEqualWithExplanation ""
            Predicated
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
            Predicated
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
            Predicated
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
            Predicated
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
            Predicated
                { term = Mock.f Mock.d
                , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton Mock.cId
                    [ appliedMockEvaluator Predicated
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
            Predicated
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
                        ,   [ appliedMockEvaluator Predicated
                                { term = Mock.e
                                , predicate = makeCeilPredicate Mock.cg
                                , substitution = []
                                }
                            ]
                        )
                    ,   ( Mock.dId
                        ,   [ appliedMockEvaluator Predicated
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
            Predicated
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
                        ,   [ appliedMockEvaluator Predicated
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
    , testCase "Simplifies substitution-predicate."
        -- Mock.plain10 below prevents:
        -- 1. unification without substitution.
        -- 2. Transforming the 'and' in an equals predicate,
        --    as it would happen for functions.
        (assertEqualWithExplanation ""
            Predicated
                { term = Mock.a
                , predicate =
                    makeCeilPredicate
                        (Mock.plain10 Mock.cf)
                , substitution =
                    [ (Mock.var_x_1, Mock.cf), (Mock.var_y_1, Mock.b) ]
                }
            (evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( Mock.fId
                        ,   [ appliedMockEvaluator Predicated
                                { term = Mock.a
                                , predicate =
                                    makeCeilPredicate
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
                                , substitution = [(Mock.x, Mock.cf)]
                                }
                            ]
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
            )
        )
    ]

axiomEvaluator
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> ApplicationFunctionEvaluator Object
axiomEvaluator left right =
    ApplicationFunctionEvaluator
        (axiomFunctionEvaluator
            AxiomPattern
                { axiomPatternLeft  = left
                , axiomPatternRight = right
                , axiomPatternRequires = makeTruePredicate
                , axiomPatternAttributes = def
                }
        )

appliedMockEvaluator
    :: CommonExpandedPattern level -> ApplicationFunctionEvaluator level
appliedMockEvaluator result =
    ApplicationFunctionEvaluator
        (mockEvaluator
            (AttemptedFunction.Applied
                (OrOfExpandedPattern.make [mapVariables result])
            )
        )

mapVariables
    ::  ( FreshVariable variable
        , MetaOrObject level
        )
    => CommonExpandedPattern level
    -> ExpandedPattern level variable
mapVariables =
    ExpandedPattern.mapVariables (\v -> freshVariableFromVariable v 1)

mockEvaluator
    :: AttemptedFunction level variable
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> PureMLPatternSimplifier level variable
    -> Application level (PureMLPattern level variable)
    -> Simplifier
        (AttemptedFunction level variable, SimplificationProof level)
mockEvaluator evaluation _ _ _ _ =
    return (evaluation, SimplificationProof)

evaluate
    :: forall level . MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> CommonPurePattern level
    -> CommonExpandedPattern level
evaluate metadataTools functionIdToEvaluator patt =
    fst
        $ evalSimplifier
        $ Pattern.simplify
            metadataTools substitutionSimplifier functionIdToEvaluator patt
  where
    substitutionSimplifier :: PredicateSubstitutionSimplifier level Simplifier
    substitutionSimplifier =
        PredicateSubstitution.create metadataTools patternSimplifier
    patternSimplifier
        ::  ( MetaOrObject level
            , SortedVariable variable
            , Ord (variable level)
            , Show (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , FreshVariable variable
            , Hashable variable
            )
        => PureMLPatternSimplifier level variable
    patternSimplifier =
        Simplifier.create metadataTools functionIdToEvaluator

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
