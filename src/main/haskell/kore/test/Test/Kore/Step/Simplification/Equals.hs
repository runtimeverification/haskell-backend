module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_ExpandedPatterns
    , test_equalsSimplification_OrOfExpandedPatterns
    , test_equalsSimplification_Patterns
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( HasCallStack, testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( AstLocation (..), BuiltinDomain (..), Equals (..), Id (..),
                 Sort (..), SortActual (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkCharLiteral, mkDomainValue, mkStringLiteral,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SortTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeAndPredicate, makeCeilPredicate,
                 makeEqualsPredicate, makeIffPredicate, makeNotPredicate,
                 makeOrPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.PredicateSubstitution
                 ( CommonPredicateSubstitution,
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), bottom, top )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Simplification.Equals
                 ( makeEvaluate, makeEvaluateTermsToPredicateSubstitution,
                 simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_equalsSimplification_OrOfExpandedPatterns :: [TestTree]
test_equalsSimplification_OrOfExpandedPatterns = give mockSortTools
    [ testCase "bottom == bottom"
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
    , testCase "a == a"
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
    , testCase "a != bottom"
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
    , testCase "f(a) vs g(a)"
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
    ]

test_equalsSimplification_ExpandedPatterns :: [TestTree]
test_equalsSimplification_ExpandedPatterns = give mockSortTools
    [ testCase "predicate-substitution vs predicate-substitution"
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
    , testCase "constructor-patt vs constructor-patt"
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
    ]

test_equalsSimplification_Patterns :: [TestTree]
test_equalsSimplification_Patterns = give mockSortTools
    [ testCase "bottom == bottom"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.top
            mkBottom
            mkBottom
        )
    , testCase "domain-value == domain-value"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.top
            (mkDomainValue
                testSort
                (BuiltinDomainPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort
                (BuiltinDomainPattern (mkStringLiteral "a"))
            )
        )
    , testCase "domain-value != domain-value"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.bottom
            (mkDomainValue
                testSort
                (BuiltinDomainPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort
                (BuiltinDomainPattern (mkStringLiteral "b"))
            )
        )
    , testCase "domain-value != domain-value because of sorts"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.bottom
            (mkDomainValue
                testSort
                (BuiltinDomainPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort2
                (BuiltinDomainPattern (mkStringLiteral "a"))
            )
        )
    , testCase "\"a\" == \"a\""
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            PredicateSubstitution.top
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase "\"a\" != \"b\""
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            PredicateSubstitution.bottom
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase "'a' == 'a'"
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            PredicateSubstitution.top
            (mkCharLiteral 'a')
            (mkCharLiteral 'a')
        )
    , testCase "'a' != 'b'"
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            PredicateSubstitution.bottom
            (mkCharLiteral 'a')
            (mkCharLiteral 'b')
        )
    , testCase "a != bottom"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.bottom
            mkBottom
            Mock.a
        )
    , testCase "a == a"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.top
            Mock.a
            Mock.a
        )
    , testCase "f(a) vs g(a)"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeEqualsPredicate fOfA gOfA
                , substitution = []
                }
            fOfA
            gOfA
        )
    , testCase "constructor1(a) vs constructor1(a)"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.top
            constructor1OfA
            constructor1OfA
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a)"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.bottom
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase "constructor1(a) vs constructor2(a)"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.bottom
            constructor1OfA
            constructor2OfA
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a))"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution.top
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate =
                    fst $ makeOrPredicate
                        (fst $ makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeEqualsPredicate fOfB gOfB)
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
            (Mock.functionalConstr20 fOfA fOfB)
            (Mock.functionalConstr20 gOfA gOfB)
        )
    , testCase "equals(x, functional) becomes a substitution"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, functionalOfA)]
                }
                (mkVar Mock.x)
                functionalOfA
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, functionalOfA)]
                }
                functionalOfA
                (mkVar Mock.x)
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeCeilPredicate fOfA
                , substitution = [(Mock.x, fOfA)]
                }
            (mkVar Mock.x)
            fOfA
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeCeilPredicate fOfA
                , substitution = [(Mock.x, fOfA)]
                }
            fOfA
            (mkVar Mock.x)
        )
    , testCase "equals(x, constructor) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate (mkVar Mock.x) constructor1OfA
                , substitution = []
                }
            (mkVar Mock.x)
            constructor1OfA
        )
    , testCase "equals(constructor, x) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate constructor1OfA (mkVar Mock.x)
                , substitution = []
                }
            constructor1OfA
            (mkVar Mock.x)
        )
    , testCase "equals(x, something) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate (mkVar Mock.x) plain1OfA
                , substitution = []
                }
            (mkVar Mock.x)
            plain1OfA
        )
    , testCase "equals(something, x) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate =
                    makeEqualsPredicate plain1OfA (mkVar Mock.x)
                , substitution = []
                }
            plain1OfA
            (mkVar Mock.x)
        )
    , testCase "equals(function, constructor) is not simplifiable"
        (assertTermEquals
            mockMetadataTools
            PredicateSubstitution
                { predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                , substitution = []
                }
                (Mock.f Mock.a)
                Mock.a
        )
    ]

assertTermEquals
    :: HasCallStack
    => MetadataTools Object StepperAttributes
    -> CommonPredicateSubstitution Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
    -> IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric
    :: (MetaOrObject level, HasCallStack)
    => MetadataTools level StepperAttributes
    -> CommonPredicateSubstitution level
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> IO ()
assertTermEqualsGeneric tools expected first second =
    give (MetadataTools.sortTools tools) $ do
        assertEqualWithExplanation "ExpandedPattern"
            (OrOfExpandedPattern.make [ predSubstToExpandedPattern expected ])
            (evaluateGeneric
                tools
                (termToExpandedPattern first)
                (termToExpandedPattern second)
            )
        assertEqualWithExplanation "PureMLPattern"
            expected
            (evaluateTermsGeneric tools first second)
  where
    termToExpandedPattern
        :: MetaOrObject level
        => CommonPurePattern level
        -> CommonExpandedPattern level
    termToExpandedPattern (Bottom_ _) =
        ExpandedPattern.bottom
    termToExpandedPattern term =
        ExpandedPattern
            { term = term
            , predicate = makeTruePredicate
            , substitution = []
            }
    predSubstToExpandedPattern
        :: MetaOrObject level
        => CommonPredicateSubstitution level
        -> CommonExpandedPattern level
    predSubstToExpandedPattern
        PredicateSubstitution {predicate = PredicateFalse}
      =
        ExpandedPattern.bottom
    predSubstToExpandedPattern
        PredicateSubstitution {predicate, substitution}
      =
        ExpandedPattern
            { term = mkTop
            , predicate = predicate
            , substitution = substitution
            }

fOfA :: CommonPurePattern Object
fOfA = give mockSortTools $ Mock.f Mock.a

fOfB :: CommonPurePattern Object
fOfB = give mockSortTools $ Mock.f Mock.b

gOfA :: CommonPurePattern Object
gOfA = give mockSortTools $ Mock.g Mock.a

gOfB :: CommonPurePattern Object
gOfB = give mockSortTools $ Mock.g Mock.b

hOfA :: CommonPurePattern Object
hOfA = give mockSortTools $ Mock.h Mock.a

hOfB :: CommonPurePattern Object
hOfB = give mockSortTools $ Mock.h Mock.b

functionalOfA :: CommonPurePattern Object
functionalOfA = give mockSortTools $ Mock.functional10 Mock.a

constructor1OfA :: CommonPurePattern Object
constructor1OfA = give mockSortTools $ Mock.constr10 Mock.a

constructor2OfA :: CommonPurePattern Object
constructor2OfA = give mockSortTools $ Mock.constr11 Mock.a

functionalConstructor1OfA :: CommonPurePattern Object
functionalConstructor1OfA =
    give mockSortTools $ Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: CommonPurePattern Object
functionalConstructor2OfA =
    give mockSortTools $ Mock.functionalConstr11 Mock.a

plain1OfA :: CommonPurePattern Object
plain1OfA = give mockSortTools $ Mock.plain10 Mock.a

mockSortTools :: SortTools Object
mockSortTools = Mock.makeSortTools Mock.sortToolsMapping

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSortTools Mock.attributesMapping Mock.subsorts

mockMetaSortTools :: SortTools Meta
mockMetaSortTools = Mock.makeSortTools []

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools = Mock.makeMetadataTools mockMetaSortTools [] []

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

evaluateTermsGeneric
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonPredicateSubstitution level
evaluateTermsGeneric tools first second =
    fst $ evalSimplifier $
        makeEvaluateTermsToPredicateSubstitution tools first second
