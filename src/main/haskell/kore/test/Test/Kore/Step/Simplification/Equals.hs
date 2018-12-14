module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_ExpandedPatterns
    , test_equalsSimplification_OrOfExpandedPatterns
    , test_equalsSimplification_Patterns
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Reflection
       ( give )

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkCharLiteral, mkDomainValue, mkStringLiteral,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeAndPredicate, makeCeilPredicate,
                 makeEqualsPredicate, makeIffPredicate, makeImpliesPredicate,
                 makeMultipleAndPredicate, makeNotPredicate, makeOrPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, CommonPredicateSubstitution,
                 Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Simplification.Equals
                 ( makeEvaluate, makeEvaluateTermsToPredicateSubstitution,
                 simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_equalsSimplification_OrOfExpandedPatterns :: [TestTree]
test_equalsSimplification_OrOfExpandedPatterns = give mockSymbolOrAliasSorts
    [ testCase "bottom == bottom" $ do
        let expect = OrOfExpandedPattern.make [ Predicated.top ]
        actual <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make []
                    , equalsSecond = OrOfExpandedPattern.make []
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "a == a" $ do
        let expect = OrOfExpandedPattern.make [ Predicated.top ]
        actual <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "a != bottom" $ do
        let expect = OrOfExpandedPattern.make []
        actual <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make []
                    , equalsSecond = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "f(a) vs g(a)" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrOfExpandedPattern.make
                        [ Predicated
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrOfExpandedPattern.make
                        [ Predicated
                            { term = gOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "f vs g or h" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate =
                            makeMultipleAndPredicate
                                [ makeCeilPredicate Mock.cf
                                , makeOrPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeCeilPredicate Mock.ch)
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                ]
                        , substitution = mempty
                        }
                    ,  Predicated
                        { term = mkTop
                        , predicate =
                            makeMultipleAndPredicate
                                [ makeNotPredicate $ makeCeilPredicate Mock.cf
                                , makeNotPredicate $ makeCeilPredicate Mock.cg
                                , makeNotPredicate $ makeCeilPredicate Mock.ch
                                ]
                        , substitution = mempty
                        }
                    ]
            first =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.cf
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            second =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.cg
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Predicated
                        { term = Mock.ch
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual1 <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = first
                    , equalsSecond = second
                    }
        assertEqualWithExplanation "f vs g or h" expect actual1
        actual2 <-
            evaluateOr
                mockMetadataTools
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = second
                    , equalsSecond = first
                    }
        assertEqualWithExplanation "g or h or f" expect actual2
    ]

test_equalsSimplification_ExpandedPatterns :: [TestTree]
test_equalsSimplification_ExpandedPatterns = give mockSymbolOrAliasSorts
    [ testCase "predicate-substitution vs predicate-substitution" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate =
                            makeIffPredicate
                                (makeEqualsPredicate fOfA fOfB)
                                (makeEqualsPredicate gOfA gOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = mempty
                    }
                Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "constructor-patt vs constructor-patt" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate =
                            makeOrPredicate
                                ( makeAndPredicate
                                    (makeAndPredicate
                                        (makeAndPredicate
                                            (makeAndPredicate
                                                (makeEqualsPredicate hOfA hOfB)
                                                (makeEqualsPredicate fOfA fOfB)
                                            )
                                            (makeCeilPredicate hOfA)
                                        )
                                        (makeEqualsPredicate gOfA gOfB)
                                    )
                                    (makeCeilPredicate hOfB)
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
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                mockMetadataTools
                Predicated
                    { term = Mock.functionalConstr10 hOfA
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = mempty
                    }
                Predicated
                    { term = Mock.functionalConstr10 hOfB
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = mempty
                    }
        assertEqualWithExplanation "" expect actual
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
                (Domain.BuiltinPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort
                (Domain.BuiltinPattern (mkStringLiteral "a"))
            )
        )
    , testCase "domain-value != domain-value"
        (assertTermEquals
            mockMetadataTools
            Predicated.bottomPredicate
            (mkDomainValue
                testSort
                (Domain.BuiltinPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort
                (Domain.BuiltinPattern (mkStringLiteral "b"))
            )
        )
    , testCase "domain-value != domain-value because of sorts"
        (assertTermEquals
            mockMetadataTools
            Predicated.bottomPredicate
            (mkDomainValue
                testSort
                (Domain.BuiltinPattern (mkStringLiteral "a"))
            )
            (mkDomainValue
                testSort2
                (Domain.BuiltinPattern (mkStringLiteral "a"))
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
                , substitution = mempty
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
                , substitution = mempty
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
                , substitution = Substitution.wrap [(Mock.x, functionalOfA)]
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
                , substitution = Substitution.wrap [(Mock.x, functionalOfA)]
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
                , substitution = Substitution.wrap [(Mock.x, fOfA)]
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
                , substitution = Substitution.wrap [(Mock.x, fOfA)]
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
                , substitution = mempty
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
                , substitution = mempty
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
                , substitution = mempty
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
                , substitution = mempty
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
                , substitution = mempty
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
                    , substitution = Substitution.wrap [(Mock.x, Mock.b)]
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
                    , substitution = Substitution.unsafeWrap
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
                    , substitution = Substitution.unsafeWrap
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
                    , substitution = Substitution.unsafeWrap
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
                    , substitution = Substitution.unsafeWrap
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
                            , substitution = mempty
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
                            , substitution = Substitution.wrap
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
    -> CommonStepPattern Object
    -> CommonStepPattern Object
    -> IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric
    :: (MetaOrObject level, HasCallStack)
    => MetadataTools level StepperAttributes
    -> CommonPredicateSubstitution level
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> Assertion
assertTermEqualsGeneric tools expectPure first second =
    give (MetadataTools.symbolOrAliasSorts tools) $ do
        let expectExpanded =
                OrOfExpandedPattern.make
                    [ predSubstToExpandedPattern expectPure ]
        actualExpanded <-
            evaluateGeneric
                tools
                (termToExpandedPattern first)
                (termToExpandedPattern second)
        assertEqualWithExplanation
            "ExpandedPattern"
            expectExpanded
            actualExpanded
        actualPure <- evaluateTermsGeneric tools first second
        assertEqualWithExplanation
            "PureMLPattern"
            expectPure
            actualPure
  where
    termToExpandedPattern
        :: MetaOrObject level
        => CommonStepPattern level
        -> CommonExpandedPattern level
    termToExpandedPattern (Bottom_ _) =
        Predicated.bottom
    termToExpandedPattern term =
        Predicated
            { term = term
            , predicate = makeTruePredicate
            , substitution = mempty
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

fOfA :: CommonStepPattern Object
fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a

fOfB :: CommonStepPattern Object
fOfB = give mockSymbolOrAliasSorts $ Mock.f Mock.b

gOfA :: CommonStepPattern Object
gOfA = give mockSymbolOrAliasSorts $ Mock.g Mock.a

gOfB :: CommonStepPattern Object
gOfB = give mockSymbolOrAliasSorts $ Mock.g Mock.b

hOfA :: CommonStepPattern Object
hOfA = give mockSymbolOrAliasSorts $ Mock.h Mock.a

hOfB :: CommonStepPattern Object
hOfB = give mockSymbolOrAliasSorts $ Mock.h Mock.b

functionalOfA :: CommonStepPattern Object
functionalOfA = give mockSymbolOrAliasSorts $ Mock.functional10 Mock.a

constructor1OfA :: CommonStepPattern Object
constructor1OfA = give mockSymbolOrAliasSorts $ Mock.constr10 Mock.a

constructor2OfA :: CommonStepPattern Object
constructor2OfA = give mockSymbolOrAliasSorts $ Mock.constr11 Mock.a

functionalConstructor1OfA :: CommonStepPattern Object
functionalConstructor1OfA =
    give mockSymbolOrAliasSorts $ Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: CommonStepPattern Object
functionalConstructor2OfA =
    give mockSymbolOrAliasSorts $ Mock.functionalConstr11 Mock.a

plain1OfA :: CommonStepPattern Object
plain1OfA = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.a

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        mockSymbolOrAliasSorts
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

mockMetaSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockMetaSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools =
    Mock.makeMetadataTools mockMetaSymbolOrAliasSorts [] [] [] []

testSort :: Sort Object
testSort =
    case mkBottom :: CommonStepPattern Object of
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
    -> IO (CommonOrOfExpandedPattern Object)
evaluateOr tools equals =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ simplify tools (Mock.substitutionSimplifier tools) equals

evaluate
    :: MetadataTools Object StepperAttributes
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
evaluate = evaluateGeneric

evaluateGeneric
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level
    -> CommonExpandedPattern level
    -> IO (CommonOrOfExpandedPattern level)
evaluateGeneric tools first second =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ makeEvaluate tools (Mock.substitutionSimplifier tools) first second

evaluateTermsGeneric
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (CommonPredicateSubstitution level)
evaluateTermsGeneric tools first second =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ makeEvaluateTermsToPredicateSubstitution
        tools
        (Mock.substitutionSimplifier tools)
        first
        second
