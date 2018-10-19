module Test.Kore.Step.Simplification.And
    (test_andSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( And (..), Sort (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( getSort, mkAnd, mkBottom, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.And
                 ( makeEvaluate, simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Kore.Step.Simplifier
import           Test.Tasty.HUnit.Extensions

test_andSimplification :: [TestTree]
test_andSimplification = give mockSymbolOrAliasSorts
    [ testCase "And truth table"
        (do
            assertEqualWithExplanation "false and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [])
                )
            assertEqualWithExplanation "false and true = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [ExpandedPattern.top])
                )
            assertEqualWithExplanation "true and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [])
                )
            assertEqualWithExplanation "true and true = true"
                (OrOfExpandedPattern.make [ExpandedPattern.top])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [ExpandedPattern.top])
                )
        )
    , testCase "And with booleans"
        (do
            assertEqualWithExplanation "false and something = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [fOfXExpanded])
                )
            assertEqualWithExplanation "something and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [fOfXExpanded] [])
                )
            assertEqualWithExplanation "true and something = something"
                (OrOfExpandedPattern.make [fOfXExpanded])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [fOfXExpanded])
                )
            assertEqualWithExplanation "something and true = something"
                (OrOfExpandedPattern.make [fOfXExpanded])
                (evaluate
                    (makeAnd [fOfXExpanded] [ExpandedPattern.top])
                )
        )
    , testCase "And with partial booleans"
        (do
            assertEqualWithExplanation "false term and something = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    bottomTerm fOfXExpanded
                )
            assertEqualWithExplanation "something and false term = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    fOfXExpanded bottomTerm
                )
            assertEqualWithExplanation "false predicate and something = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    falsePredicate fOfXExpanded
                )
            assertEqualWithExplanation "something and false predicate = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    fOfXExpanded falsePredicate
                )
        )
    , testCase "And with normal patterns"
        (do
            assertEqualWithExplanation "And random terms"
                Predicated
                    { term = mkAnd plain0OfX plain1OfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                (evaluatePatterns
                    plain0OfXExpanded plain1OfXExpanded
                )
            assertEqualWithExplanation "And function terms"
                Predicated
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                (evaluatePatterns
                    fOfXExpanded gOfXExpanded
                )
            assertEqualWithExplanation "And predicates"
                Predicated
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = []
                    }
                (evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = []
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = []
                        }
                )
            assertEqualWithExplanation "And substitutions - simple"
                Predicated
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.y, fOfX), (Mock.z, gOfX)]
                    }
                (evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.y, fOfX)]
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.z, gOfX)]
                        }
                )
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation "And substitutions - separate predicate"
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, Mock.functionAttributes)
                    , (gSymbol, Mock.functionAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
            assertEqualWithExplanation "And substitutions - failure"
                Predicated
                    { term = mkTop
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
                (evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( Mock.y
                                , Mock.functionalConstr10 (mkVar Mock.x)
                                )
                            ]
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( Mock.y
                                , Mock.functionalConstr11 (mkVar Mock.x)
                                )
                            ]
                        }
                )
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation
                "Combines conditions with substitution merge condition"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (fst $ makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                            )
                            (givemakeEqualsPredicate fOfX gOfX)
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, mock.functionAttributes)
                    , (gSymbol, mock.functionAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
        )
    , testCase "Variable-function and"
        (do
            assertEqualWithExplanation "variable-term"
                Predicated
                    { term = fOfX
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.y, fOfX)]
                    }
                (evaluatePatterns
                    yExpanded fOfXExpanded
                )
            assertEqualWithExplanation "term-variable"
                Predicated
                    { term = fOfX
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.y, fOfX)]
                    }
                (evaluatePatterns
                    fOfXExpanded yExpanded
                )
        )
    , testCase "constructor and"
        (do
            assertEqualWithExplanation "same constructors"
                Predicated
                    { term = Mock.constr10 fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                (evaluatePatterns
                    Predicated
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    Predicated
                        { term = Mock.constr10 gOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
            assertEqualWithExplanation "different constructors"
                ExpandedPattern.bottom
                (evaluatePatterns
                    Predicated
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    Predicated
                        { term = Mock.constr11 gOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
        )
    -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
    , testCase "And-Or distribution"
        (assertEqualWithExplanation "Distributes or"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                , Predicated
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfX
                    , substitution = []
                    }
                , Predicated
                    { term = gOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = []
                    }
                , Predicated
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (makeAnd
                    [ fOfXExpanded
                    , Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = []
                        }
                    ]
                    [ gOfXExpanded
                    , Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = []
                        }
                    ]
                )
            )
        )
    ]
  where
    yExpanded = Predicated
        { term = give mockSymbolOrAliasSorts $ mkVar Mock.y
        , predicate = makeTruePredicate
        , substitution = []
        }
    fOfX = give mockSymbolOrAliasSorts $ Mock.f (mkVar Mock.x)
    fOfXExpanded = Predicated
        { term = fOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    gOfX = give mockSymbolOrAliasSorts $ Mock.g (mkVar Mock.x)
    gOfXExpanded = Predicated
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    plain0OfX = give mockSymbolOrAliasSorts $ Mock.plain10 (mkVar Mock.x)
    plain0OfXExpanded = Predicated
        { term = plain0OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    plain1OfX = give mockSymbolOrAliasSorts $ Mock.plain11 (mkVar Mock.x)
    plain1OfXExpanded = Predicated
        { term = plain1OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    bottomTerm = Predicated
        { term = mkBottom
        , predicate = makeTruePredicate
        , substitution = []
        }
    falsePredicate = Predicated
        { term = mkTop
        , predicate = makeFalsePredicate
        , substitution = []
        }

makeAnd
    :: [CommonExpandedPattern Object]
    -> [CommonExpandedPattern Object]
    -> And Object (CommonOrOfExpandedPattern Object)
makeAnd first second =
    And
        { andSort = findSort (first ++ second)
        , andFirst = OrOfExpandedPattern.make first
        , andSecond = OrOfExpandedPattern.make second
        }

findSort :: [CommonExpandedPattern Object] -> Sort Object
findSort [] = testSort
findSort
    ( Predicated {term} : _ )
  =
    give mockSymbolOrAliasSorts $ getSort term

evaluate
    :: And Object (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate patt =
    fst $ evalSimplifierTest $ simplify mockMetadataTools patt

evaluatePatterns
    :: CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
evaluatePatterns first second =
    fst $ evalSimplifierTest $ makeEvaluate mockMetadataTools first second

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSymbolOrAliasSorts Mock.attributesMapping Mock.subsorts

testSort :: MetaOrObject level => Sort level
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"
