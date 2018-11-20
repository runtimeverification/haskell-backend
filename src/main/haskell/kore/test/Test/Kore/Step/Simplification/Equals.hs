module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_ExpandedPatterns
    , test_equalsSimplification_OrOfExpandedPatterns
    , test_equalsSimplification_Patterns
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( HasCallStack, testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( AstLocation (..), BuiltinDomain (..), CommonPurePattern,
                 Equals (..), Id (..), Sort (..), SortActual (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkCharLiteral, mkDomainValue, mkStringLiteral,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeAndPredicate, makeCeilPredicate,
                 makeEqualsPredicate, makeIffPredicate, makeNotPredicate,
                 makeOrPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, CommonPredicateSubstitution,
                 Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Simplification.Equals
                 ( makeEvaluate, makeEvaluateTermsToPredicateSubstitution,
                 simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_equalsSimplification_OrOfExpandedPatterns :: [TestTree]
test_equalsSimplification_OrOfExpandedPatterns = give mockSymbolOrAliasSorts
    [ testCase "bottom == bottom"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ Predicated.top ])
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
            (OrOfExpandedPattern.make [ Predicated.top ])
            (evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ Predicated
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
                        [ Predicated
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
                [ Predicated
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
                        [ Predicated
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ Predicated
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
test_equalsSimplification_ExpandedPatterns = give mockSymbolOrAliasSorts
    [ testCase "predicate-substitution vs predicate-substitution"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeIffPredicate
                            (makeEqualsPredicate fOfA fOfB)
                            (makeEqualsPredicate gOfA gOfB)
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = []
                    }
                Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = []
                    }
            )
        )
    , testCase "constructor-patt vs constructor-patt"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeOrPredicate
                            ( makeAndPredicate
                                (makeEqualsPredicate hOfA hOfB)
                                (makeAndPredicate
                                    (makeAndPredicate
                                        (makeEqualsPredicate fOfA fOfB)
                                        (makeCeilPredicate hOfA)
                                    )
                                    (makeAndPredicate
                                        (makeEqualsPredicate gOfA gOfB)
                                        (makeCeilPredicate hOfB)
                                    )
                                )
                            )
                            (makeAndPredicate
                                (makeNotPredicate
                                    (makeAndPredicate
                                        (makeEqualsPredicate fOfA fOfB)
                                        (makeCeilPredicate hOfA)
                                    )
                                )
                                (makeNotPredicate
                                    (makeAndPredicate
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
                Predicated
                    { term = Mock.functionalConstr10 hOfA
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = []
                    }
                Predicated
                    { term = Mock.functionalConstr10 hOfB
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = []
                    }
            )
        )
    ]

test_equalsSimplification_Patterns :: [TestTree]
test_equalsSimplification_Patterns = give mockSymbolOrAliasSorts
    [ testCase "bottom == bottom"
        (assertTermEquals
            mockMetadataTools
            Predicated.topPredicate
            mkBottom
            mkBottom
        )
    , testCase "domain-value == domain-value"
        (assertTermEquals
            mockMetadataTools
            Predicated.topPredicate
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
            Predicated.bottomPredicate
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
            Predicated.bottomPredicate
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
            Predicated.topPredicate
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase "\"a\" != \"b\""
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            Predicated.bottomPredicate
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase "'a' == 'a'"
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            Predicated.topPredicate
            (mkCharLiteral 'a')
            (mkCharLiteral 'a')
        )
    , testCase "'a' != 'b'"
        (assertTermEqualsGeneric
            mockMetaMetadataTools
            Predicated.bottomPredicate
            (mkCharLiteral 'a')
            (mkCharLiteral 'b')
        )
    , testCase "a != bottom"
        (assertTermEquals
            mockMetadataTools
            Predicated.bottomPredicate
            mkBottom
            Mock.a
        )
    , testCase "a == a"
        (assertTermEquals
            mockMetadataTools
            Predicated.topPredicate
            Mock.a
            Mock.a
        )
    , testCase "f(a) vs g(a)"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = []
                }
            fOfA
            gOfA
        )
    , testCase "constructor1(a) vs constructor1(a)"
        (assertTermEquals
            mockMetadataTools
            Predicated.topPredicate
            constructor1OfA
            constructor1OfA
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a)"
        (assertTermEquals
            mockMetadataTools
            Predicated.bottomPredicate
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase "constructor1(a) vs constructor2(a)"
        (assertTermEquals
            mockMetadataTools
            Predicated.bottomPredicate
            constructor1OfA
            constructor2OfA
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a))"
        (assertTermEquals
            mockMetadataTools
            Predicated.topPredicate
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate =
                    makeOrPredicate
                        (makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeEqualsPredicate fOfB gOfB)
                        )
                        (makeAndPredicate
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                            )
                            (makeNotPredicate
                                (makeAndPredicate
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
            Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, functionalOfA)]
                }
                (mkVar Mock.x)
                functionalOfA
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, functionalOfA)]
                }
                functionalOfA
                (mkVar Mock.x)
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution = [(Mock.x, fOfA)]
                }
            (mkVar Mock.x)
            fOfA
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution = [(Mock.x, fOfA)]
                }
            fOfA
            (mkVar Mock.x)
        )
    , testCase "equals(x, constructor) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate (mkVar Mock.x) constructor1OfA
                , substitution = []
                }
            (mkVar Mock.x)
            constructor1OfA
        )
    , testCase "equals(constructor, x) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate constructor1OfA (mkVar Mock.x)
                , substitution = []
                }
            constructor1OfA
            (mkVar Mock.x)
        )
    , testCase "equals(x, something) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate (mkVar Mock.x) plain1OfA
                , substitution = []
                }
            (mkVar Mock.x)
            plain1OfA
        )
    , testCase "equals(something, x) becomes a predicate"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate plain1OfA (mkVar Mock.x)
                , substitution = []
                }
            plain1OfA
            (mkVar Mock.x)
        )
    , testCase "equals(function, constructor) is not simplifiable"
        (assertTermEquals
            mockMetadataTools
            Predicated
                { term = ()
                , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                , substitution = []
                }
                (Mock.f Mock.a)
                Mock.a
        )
    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys"
            (assertTermEquals
                mockMetadataTools
                Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    }
                (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
            )
        , testCase "concrete Map, different keys"
            (assertTermEquals
                mockMetadataTools
                Predicated.bottomPredicate
                (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                (Mock.builtinMap [(Mock.bConcrete, mkVar Mock.x)])
            )
        , testCase "concrete Map with framed Map"
            (assertTermEquals
                mockMetadataTools
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                (Mock.builtinMap
                    [ (Mock.aConcrete, fOfA)
                    , (Mock.bConcrete, fOfB)
                    ]
                )
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    (mkVar Mock.m)
                )
            )
        , testCase "concrete Map with framed Map"
            (assertTermEquals
                mockMetadataTools
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                (Mock.builtinMap
                    [ (Mock.aConcrete, fOfA)
                    , (Mock.bConcrete, fOfB)
                    ]
                )
                (Mock.concatMap
                    (mkVar Mock.m)
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                )
            )
        , testCase "framed Map with concrete Map"
            (assertTermEquals
                mockMetadataTools
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    (mkVar Mock.m)
                )
                (Mock.builtinMap
                    [ (Mock.aConcrete, fOfA)
                    , (Mock.bConcrete, fOfB)
                    ]
                )
            )
        , testCase "framed Map with concrete Map"
            (assertTermEquals
                mockMetadataTools
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                (Mock.concatMap
                    (mkVar Mock.m)
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                )
                (Mock.builtinMap
                    [ (Mock.aConcrete, fOfA)
                    , (Mock.bConcrete, fOfB)
                    ]
                )
            )
        -- TODO: Add tests with non-trivial predicates.
        ]
    , testGroup "builtin List domain"
        [
            let term1 =
                    Mock.builtinList
                        [ Mock.constr10 Mock.cf
                        , Mock.constr11 Mock.cf
                        ]
            in
                testCase "[same head, same head]"
                    (assertTermEquals
                        mockMetadataTools
                        Predicated
                            { term = ()
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        term1
                        term1
                    )
        ,
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                unified34 = Predicated.bottomPredicate
            in
                testCase "[same head, different head]"
                    (assertTermEquals
                        mockMetadataTools
                        unified34
                        term3
                        term4
                    )
        ,
            let term5 = Mock.concatList
                        (Mock.builtinList [Mock.a])
                        (mkVar Mock.x)
                term6 = Mock.builtinList $ [Mock.a, Mock.b]
            in
                testCase "[a] `concat` x /\\ [a, b] "
                    (assertTermEquals
                        mockMetadataTools
                        Predicated
                            { term = ()
                            , predicate = makeTruePredicate
                            , substitution =
                                [(Mock.x, Mock.builtinList [Mock.b])]
                            }
                        term5
                        term6
                    )
        ,
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
            in
                testCase "different lengths"
                    (assertTermEquals
                        mockMetadataTools
                        Predicated.bottomPredicate
                        term7
                        term8
                    )
        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set equality.
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
    give (MetadataTools.symbolOrAliasSorts tools) $ do
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
        Predicated.bottom
    termToExpandedPattern term =
        Predicated
            { term = term
            , predicate = makeTruePredicate
            , substitution = []
            }
    predSubstToExpandedPattern
        :: MetaOrObject level
        => CommonPredicateSubstitution level
        -> CommonExpandedPattern level
    predSubstToExpandedPattern
        Predicated {predicate = PredicateFalse}
      =
        Predicated.bottom
    predSubstToExpandedPattern
        Predicated {predicate, substitution}
      =
        Predicated
            { term = mkTop
            , predicate = predicate
            , substitution = substitution
            }

fOfA :: CommonPurePattern Object
fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a

fOfB :: CommonPurePattern Object
fOfB = give mockSymbolOrAliasSorts $ Mock.f Mock.b

gOfA :: CommonPurePattern Object
gOfA = give mockSymbolOrAliasSorts $ Mock.g Mock.a

gOfB :: CommonPurePattern Object
gOfB = give mockSymbolOrAliasSorts $ Mock.g Mock.b

hOfA :: CommonPurePattern Object
hOfA = give mockSymbolOrAliasSorts $ Mock.h Mock.a

hOfB :: CommonPurePattern Object
hOfB = give mockSymbolOrAliasSorts $ Mock.h Mock.b

functionalOfA :: CommonPurePattern Object
functionalOfA = give mockSymbolOrAliasSorts $ Mock.functional10 Mock.a

constructor1OfA :: CommonPurePattern Object
constructor1OfA = give mockSymbolOrAliasSorts $ Mock.constr10 Mock.a

constructor2OfA :: CommonPurePattern Object
constructor2OfA = give mockSymbolOrAliasSorts $ Mock.constr11 Mock.a

functionalConstructor1OfA :: CommonPurePattern Object
functionalConstructor1OfA =
    give mockSymbolOrAliasSorts $ Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: CommonPurePattern Object
functionalConstructor2OfA =
    give mockSymbolOrAliasSorts $ Mock.functionalConstr11 Mock.a

plain1OfA :: CommonPurePattern Object
plain1OfA = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.a

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        mockSymbolOrAliasSorts
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.subsorts

mockMetaSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockMetaSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools =
    Mock.makeMetadataTools mockMetaSymbolOrAliasSorts [] [] []

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
    fst $ evalSimplifier
        $ simplify tools (Mock.substitutionSimplifier tools) equals

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
    fst $ evalSimplifier
        $ makeEvaluate tools (Mock.substitutionSimplifier tools) first second

evaluateTermsGeneric
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonPredicateSubstitution level
evaluateTermsGeneric tools first second =
    fst $ evalSimplifier $
        makeEvaluateTermsToPredicateSubstitution
            tools (Mock.substitutionSimplifier tools) first second
