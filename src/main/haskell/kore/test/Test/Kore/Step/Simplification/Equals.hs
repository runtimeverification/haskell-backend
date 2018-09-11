module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( AstLocation (..), CharLiteral (..), Equals (..), Id (..),
                 Sort (..), SortActual (..), StringLiteral (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkCharLiteral, mkDomainValue, mkStringLiteral,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeIffPredicate, makeNotPredicate, makeOrPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Simplification.Equals
                 ( makeEvaluate, simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_equalsSimplification :: [TestTree]
test_equalsSimplification = give mockSortTools
    [ testCase "bottom == bottom for Or patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make []
                    , equalsSecond = OrOfExpandedPattern.make []
                    }
            )
        )
    , testCase "a == a for Or patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make
                        [ ExpandedPattern
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ ExpandedPattern
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    }
            )
        )
    , testCase "a != bottom for Or patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make []
                    , equalsSecond = OrOfExpandedPattern.make
                        [ ExpandedPattern
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    }
            )
        )
    , testCase "f(a) vs g(a) for or patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = []
                    }
                ]
            )
            (evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make
                        [ ExpandedPattern
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ ExpandedPattern
                            { term = gOfA
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    }
            )
        )
    , testCase "bottom == bottom for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluate
                mockMetadataTools
                ExpandedPattern.bottom
                ExpandedPattern.bottom
            )
        )
    , testCase "domain-value == domain-value for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort
                            (mkStringLiteral (StringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort
                            (mkStringLiteral (StringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "domain-value != domain-value for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort
                            (mkStringLiteral (StringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort
                            (mkStringLiteral (StringLiteral "b"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "domain-value != domain-value because of sorts for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort
                            (mkStringLiteral (StringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term =
                        mkDomainValue
                            testSort2
                            (mkStringLiteral (StringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "\"a\" == \"a\" for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluateGeneric
                mockMetaMetadataTools
                ExpandedPattern
                    { term = mkStringLiteral (StringLiteral "a")
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkStringLiteral (StringLiteral "a")
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "\"a\" != \"b\" for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluateGeneric
                mockMetaMetadataTools
                ExpandedPattern
                    { term = mkStringLiteral (StringLiteral "a")
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkStringLiteral (StringLiteral "b")
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "'a' == 'a' for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluateGeneric
                mockMetaMetadataTools
                ExpandedPattern
                    { term = mkCharLiteral (CharLiteral 'a')
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkCharLiteral (CharLiteral 'a')
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "'a' != 'b' for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluateGeneric
                mockMetaMetadataTools
                ExpandedPattern
                    { term = mkCharLiteral (CharLiteral 'a')
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkCharLiteral (CharLiteral 'b')
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "a != bottom for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                ExpandedPattern.bottom
                ExpandedPattern
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "a == a for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ ExpandedPattern.top ])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "f(a) vs g(a) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = gOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "constructor1(a) vs constructor1(a) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern.top ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = constructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = constructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                []
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = functionalConstructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = functionalConstructor2OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "constructor1(a) vs constructor2(a) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (fst $ makeNotPredicate
                                (makeCeilPredicate constructor1OfA)
                            )
                            (fst $ makeNotPredicate
                                (makeCeilPredicate constructor2OfA)
                            )
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = constructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = constructor2OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a)) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = Mock.constr10 fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = Mock.constr10 fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b)) for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeOrPredicate
                            (fst $ makeAndPredicate
                                (fst $ makeAndPredicate
                                    (makeEqualsPredicate fOfA gOfA)
                                    (makeEqualsPredicate fOfB gOfB)
                                )
                                (fst $ makeAndPredicate
                                    (fst $ makeAndPredicate
                                        (makeCeilPredicate fOfA)
                                        (makeCeilPredicate fOfB)
                                    )
                                    (fst $ makeAndPredicate
                                        (makeCeilPredicate gOfA)
                                        (makeCeilPredicate gOfB)
                                    )
                                )
                            )
                            (fst $ makeAndPredicate
                                (fst $ makeNotPredicate
                                    (fst $ makeAndPredicate
                                        (makeCeilPredicate fOfA)
                                        (makeCeilPredicate fOfB)
                                    )
                                )
                                (fst $ makeNotPredicate
                                    (fst $ makeAndPredicate
                                        (makeCeilPredicate gOfA)
                                        (makeCeilPredicate gOfB)
                                    )
                                )
                            )
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = Mock.functionalConstr20 fOfA fOfB
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = Mock.functionalConstr20 gOfA gOfB
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "predicate-substitution vs predicate-substitution for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeIffPredicate
                            (makeEqualsPredicate fOfA fOfB)
                            (makeEqualsPredicate gOfA gOfB)
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = []
                    }
            )
        )
    , testCase "constructor-patt vs constructor-patt for patterns"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeOrPredicate
                            ( fst $ makeAndPredicate
                                (makeEqualsPredicate hOfA hOfB)
                                (fst $ makeAndPredicate
                                    (fst $ makeAndPredicate
                                        (makeEqualsPredicate fOfA fOfB)
                                        (makeCeilPredicate hOfA)
                                    )
                                    (fst $ makeAndPredicate
                                        (makeEqualsPredicate gOfA gOfB)
                                        (makeCeilPredicate hOfB)
                                    )
                                )
                            )
                            (fst $ makeAndPredicate
                                (fst $ makeNotPredicate
                                    (fst $ makeAndPredicate
                                        (makeEqualsPredicate fOfA fOfB)
                                        (makeCeilPredicate hOfA)
                                    )
                                )
                                (fst $ makeNotPredicate
                                    (fst $ makeAndPredicate
                                        (makeEqualsPredicate gOfA gOfB)
                                        (makeCeilPredicate hOfB)
                                    )
                                )
                            )
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = Mock.functionalConstr10 hOfA
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = []
                    }
                ExpandedPattern
                    { term = Mock.functionalConstr10 hOfB
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = []
                    }
            )
        )
    , testCase "equals(x, functional) becomes a substitution"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, functionalOfA)]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = functionalOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, functionalOfA)]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = functionalOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeCeilPredicate fOfA
                    , substitution = [(Mock.x, fOfA)]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeCeilPredicate fOfA
                    , substitution = [(Mock.x, fOfA)]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(x, constructor) becomes a predicate"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        makeEqualsPredicate (mkVar Mock.x) constructor1OfA
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = constructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(something, x) becomes a predicate"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        makeEqualsPredicate constructor1OfA (mkVar Mock.x)
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = constructor1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = mkVar Mock.x
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "equals(function, constructor) is not simplifiable"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term = Mock.f Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ExpandedPattern
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    ]
  where
    fOfA = give mockSortTools $ Mock.f Mock.a
    fOfB = give mockSortTools $ Mock.f Mock.b
    gOfA = give mockSortTools $ Mock.g Mock.a
    gOfB = give mockSortTools $ Mock.g Mock.b
    hOfA = give mockSortTools $ Mock.h Mock.a
    hOfB = give mockSortTools $ Mock.h Mock.b
    functionalOfA = give mockSortTools $ Mock.functional10 Mock.a
    constructor1OfA = give mockSortTools $ Mock.constr10 Mock.a
    constructor2OfA = give mockSortTools $ Mock.constr11 Mock.a
    functionalConstructor1OfA =
        give mockSortTools $ Mock.functionalConstr10 Mock.a
    functionalConstructor2OfA =
        give mockSortTools $ Mock.functionalConstr11 Mock.a
    mockSortTools = Mock.makeSortTools Mock.sortToolsMapping
    mockMetadataTools =
        Mock.makeMetadataTools mockSortTools Mock.attributesMapping
    mockMetaSortTools :: SortTools Meta
    mockMetaSortTools = Mock.makeSortTools []
    mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
    mockMetaMetadataTools = Mock.makeMetadataTools mockMetaSortTools []

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

testSort2 :: Sort Object
testSort2 =
    SortActualSort SortActual
        { sortActualName  = Id "testSort2" AstLocationTest
        , sortActualSorts = []
        }

evaluateOr
    :: MetadataTools Object StepperAttributes
    -> Equals Object (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluateOr tools equals =
    fst $ evalSimplifier $ simplify tools equals

evaluate
    :: MetadataTools Object StepperAttributes
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> CommonOrOfExpandedPattern Object
evaluate = evaluateGeneric

evaluateGeneric
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level
    -> CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
evaluateGeneric tools first second =
    fst $ evalSimplifier $ makeEvaluate tools first second

