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
                 ( MetadataTools, SymSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.And
                 ( makeEvaluate, simplify )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andSimplification :: [TestTree]
test_andSimplification = give mockSymSorts
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
                ExpandedPattern
                    { term = mkAnd plain0OfX plain1OfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                (evaluatePatterns
                    plain0OfXExpanded plain1OfXExpanded
                )
            assertEqualWithExplanation "And function terms"
                ExpandedPattern
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                (evaluatePatterns
                    fOfXExpanded gOfXExpanded
                )
            assertEqualWithExplanation "And predicates"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = []
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = []
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = []
                        }
                )
            assertEqualWithExplanation "And substitutions - simple"
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.y, fOfX), (Mock.z, gOfX)]
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.y, fOfX)]
                        }
                    ExpandedPattern
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
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( Mock.y
                                , Mock.functionalConstr10 (mkVar Mock.x)
                                )
                            ]
                        }
                    ExpandedPattern
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
                ExpandedPattern
                    { term = fOfX
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.y, fOfX)]
                    }
                (evaluatePatterns
                    yExpanded fOfXExpanded
                )
            assertEqualWithExplanation "term-variable"
                ExpandedPattern
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
                ExpandedPattern
                    { term = Mock.constr10 fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ExpandedPattern
                        { term = Mock.constr10 gOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
            assertEqualWithExplanation "different constructors"
                ExpandedPattern.bottom
                (evaluatePatterns
                    ExpandedPattern
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ExpandedPattern
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
                [ ExpandedPattern
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfX
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfX
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = gOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = []
                    }
                , ExpandedPattern
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
                    , ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = []
                        }
                    ]
                    [ gOfXExpanded
                    , ExpandedPattern
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
    yExpanded = ExpandedPattern
        { term = give mockSymSorts $ mkVar Mock.y
        , predicate = makeTruePredicate
        , substitution = []
        }
    fOfX = give mockSymSorts $ Mock.f (mkVar Mock.x)
    fOfXExpanded = ExpandedPattern
        { term = fOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    gOfX = give mockSymSorts $ Mock.g (mkVar Mock.x)
    gOfXExpanded = ExpandedPattern
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    plain0OfX = give mockSymSorts $ Mock.plain10 (mkVar Mock.x)
    plain0OfXExpanded = ExpandedPattern
        { term = plain0OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    plain1OfX = give mockSymSorts $ Mock.plain11 (mkVar Mock.x)
    plain1OfXExpanded = ExpandedPattern
        { term = plain1OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    bottomTerm = ExpandedPattern
        { term = mkBottom
        , predicate = makeTruePredicate
        , substitution = []
        }
    falsePredicate = ExpandedPattern
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
    ( ExpandedPattern {term} : _ )
  =
    give mockSymSorts $ getSort term

evaluate
    :: And Object (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate patt =
    fst $ evalSimplifier $ simplify mockMetadataTools patt

evaluatePatterns
    :: CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
evaluatePatterns first second =
    fst $ evalSimplifier $ makeEvaluate mockMetadataTools first second

mockSymSorts :: SymSorts Object
mockSymSorts = Mock.makeSymSorts Mock.symSortsMapping
mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSymSorts Mock.attributesMapping Mock.subsorts

testSort :: MetaOrObject level => Sort level
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"
