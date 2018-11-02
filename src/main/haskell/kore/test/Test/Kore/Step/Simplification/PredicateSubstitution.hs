module Test.Kore.Step.Simplification.PredicateSubstitution
    ( test_predicateSubstitutionSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Functor.Foldable
                 ( embed )
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Application, Id (..), Pattern (..), PureMLPattern,
                 SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..), AttemptedFunction (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.PredicateSubstitution
                 ( CommonPredicateSubstitution,
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), bottom, top )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.PredicateSubstitution as PSSimplifier
                 ( create )
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

test_predicateSubstitutionSimplification :: [TestTree]
test_predicateSubstitutionSimplification = give mockSymbolOrAliasSorts
    [ testCase "Identity for top and bottom"
        (do
            assertEqualWithExplanation ""
                PredicateSubstitution.bottom
                (runSimplifier Map.empty PredicateSubstitution.bottom)
            assertEqualWithExplanation ""
                PredicateSubstitution.top
                (runSimplifier Map.empty PredicateSubstitution.top)
        )
    , testCase "Applies substitution to predicate"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate = makeEqualsPredicate
                    (Mock.f Mock.a)
                    (Mock.g Mock.b)
                , substitution =
                    [ (Mock.x, Mock.a)
                    , (Mock.y, Mock.b)
                    ]
                }
            (runSimplifier Map.empty
                PredicateSubstitution
                    { predicate = makeEqualsPredicate
                        (Mock.f (mkVar Mock.x))
                        (Mock.g (mkVar Mock.y))
                    , substitution =
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
            )
        )
    , testCase "Simplifies predicate after substitution"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate = makeEqualsPredicate
                    Mock.functional00
                    Mock.functional01
                , substitution =
                    [ (Mock.x, Mock.functional00)
                    , (Mock.y, Mock.functional01)
                    ]
                }
            (runSimplifier Map.empty
                PredicateSubstitution
                    { predicate = makeEqualsPredicate
                        (Mock.constr10 (mkVar Mock.x))
                        (Mock.constr10 (mkVar Mock.y))
                    , substitution =
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
            )
        )
    , testCase "Simplifies predicate after substitution"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate = makeEqualsPredicate
                    Mock.functional00
                    Mock.a
                , substitution =
                    [ (Mock.x, Mock.functional00)
                    , (Mock.y, Mock.functional01)
                    ]
                }
            (runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        ,   [ makeEvaluator
                                [ (Mock.f Mock.functional00, Mock.functional00)
                                , (Mock.f Mock.functional01, Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                PredicateSubstitution
                    { predicate = makeEqualsPredicate
                        (Mock.f (mkVar Mock.x))
                        (Mock.f (mkVar Mock.y))
                    , substitution =
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
            )
        )
    , testCase "Merges substitution from predicate simplification"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution =
                    [ (Mock.x, Mock.a)
                    , (Mock.y, Mock.b)
                    ]
                }
            (runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        ,   [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                PredicateSubstitution
                    { predicate = makeEqualsPredicate
                        (Mock.constr10 (mkVar Mock.x))
                        (Mock.f (mkVar Mock.y))
                    , substitution =
                        [ (Mock.y, Mock.b)
                        ]
                    }
            )
        )
    , testCase "Reapplies substitution from predicate simplification"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate
                        (Mock.f Mock.a)
                        (Mock.g Mock.a)
                , substitution =
                    [ (Mock.x, Mock.a)
                    , (Mock.y, Mock.b)
                    ]
                }
            (runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        ,   [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                PredicateSubstitution
                    { predicate =
                        makeAndPredicate
                            (makeEqualsPredicate
                                (Mock.constr10 (mkVar Mock.x))
                                (Mock.f (mkVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution =
                        [ (Mock.y, Mock.b)
                        ]
                    }
            )
        )
    , testCase "Simplifies after reapplying substitution"
        (assertEqualWithExplanation ""
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate
                        (Mock.g Mock.b)
                        (Mock.g Mock.a)
                , substitution =
                    [ (Mock.x, Mock.a)
                    , (Mock.y, Mock.b)
                    ]
                }
            (runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        ,   [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                , (Mock.f Mock.a, Mock.g Mock.b)
                                ]
                            ]
                        )
                    ]
                )
                PredicateSubstitution
                    { predicate =
                        makeAndPredicate
                            (makeEqualsPredicate
                                (Mock.constr10 (mkVar Mock.x))
                                (Mock.f (mkVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution =
                        [ (Mock.y, Mock.b)
                        ]
                    }
            )
        )
    ]

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

runSimplifier
    :: Map.Map
        (Id Object)
        [ApplicationFunctionEvaluator Object]
    -> CommonPredicateSubstitution Object
    -> CommonPredicateSubstitution Object
runSimplifier patternSimplifierMap predicateSubstitution =
    case simplifier of
        (PredicateSubstitutionSimplifier unwrapped) ->
            fst $ evalSimplifier
            $ unwrapped predicateSubstitution
  where
    simplifier =
        PSSimplifier.create
            mockMetadataTools
            (Simplifier.create mockMetadataTools patternSimplifierMap)

makeEvaluator
    ::  (forall variable
        .   ( FreshVariable variable
            , Hashable variable
            , OrdMetaOrObject variable
            , SortedVariable variable
            , ShowMetaOrObject variable
            )
        => [(PureMLPattern Object variable, PureMLPattern Object variable)]
        )
    -> ApplicationFunctionEvaluator Object
makeEvaluator mapping =
    ApplicationFunctionEvaluator
        $ const $ const $ const $ simpleEvaluator mapping

simpleEvaluator
    ::  ( FreshVariable variable
        , Hashable variable
        , OrdMetaOrObject variable
        , SortedVariable variable
        , ShowMetaOrObject variable
        )
    => [(PureMLPattern Object variable, PureMLPattern Object variable)]
    -> Application Object (PureMLPattern Object variable)
    -> Simplifier
        ( AttemptedFunction Object variable
        , SimplificationProof Object
        )
simpleEvaluator [] _ = return (NotApplicable, SimplificationProof)
simpleEvaluator ((from, to) : ps) app
  | from == embed (ApplicationPattern app) =
    return
        ( Applied
            (OrOfExpandedPattern.make
                [ExpandedPattern.fromPurePattern to]
            )
        , SimplificationProof
        )
  | otherwise =
    simpleEvaluator ps app
