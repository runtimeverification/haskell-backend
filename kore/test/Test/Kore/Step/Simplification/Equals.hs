module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_TermLike
    , test_equalsSimplification_Or_Pattern
    , test_equalsSimplification_Pattern
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.Predicate
    ( pattern PredicateFalse
    , makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeIffPredicate
    , makeImpliesPredicate
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate_
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Step.Simplification.Equals
    ( makeEvaluate
    , makeEvaluateTermsToPredicate
    , simplify
    )
import Kore.Unparser

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_equalsSimplification_Or_Pattern :: [TestTree]
test_equalsSimplification_Or_Pattern =
    [ testCase "bottom == bottom" $ do
        let expect = OrPattern.fromPatterns [ Conditional.top ]
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns []
                    , equalsSecond = OrPattern.fromPatterns []
                    }
        assertEqual "" expect actual

    , testCase "a == a" $ do
        let expect = OrPattern.fromPatterns [ Conditional.top ]
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "a != bottom" $ do
        let expect = OrPattern.fromPatterns []
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns []
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "f(a) vs g(a)" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate_ fOfA gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns
                        [ Conditional
                            { term = fOfA
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = gOfA
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "f vs g or h" $ do
        let expectEvaluateEquals =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeCeilPredicate_ Mock.cf
                            , makeCeilPredicate_ Mock.cg
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.cg)
                                (makeEqualsPredicate_ Mock.cf Mock.cg)
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.ch)
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeCeilPredicate_ Mock.cf
                            , makeCeilPredicate_ Mock.ch
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.cg)
                                (makeEqualsPredicate_ Mock.cf Mock.cg)
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.ch)
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            ]
                        , substitution = mempty
                        }
                    ,  Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeNotPredicate $ makeCeilPredicate_ Mock.cf
                            , makeNotPredicate $ makeCeilPredicate_ Mock.cg
                            , makeNotPredicate $ makeCeilPredicate_ Mock.ch
                            ]
                        , substitution = mempty
                        }
                    ]
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cg
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult "f" "g or h"
            expectEvaluateEquals
            Equals
                { equalsOperandSort = testSort
                , equalsResultSort = testSort
                , equalsFirst = first
                , equalsSecond = second
                }

    , testCase "f vs g or h where f /= g" $ do
        let expectEvaluateEquals =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeCeilPredicate_ Mock.cf
                            , makeCeilPredicate_ Mock.cg
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.ch)
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            , makeNotPredicate (makeCeilPredicate_ Mock.cg)
                            ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeCeilPredicate_ Mock.cf
                            , makeCeilPredicate_ Mock.ch
                            , makeImpliesPredicate
                                (makeCeilPredicate_ Mock.ch)
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            , makeNotPredicate $ makeCeilPredicate_ Mock.cg
                            ]
                        , substitution = mempty
                        }
                    ,  Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeNotPredicate $ makeCeilPredicate_ Mock.cf
                            , makeNotPredicate $ makeCeilPredicate_ Mock.cg
                            , makeNotPredicate $ makeCeilPredicate_ Mock.ch
                            ]
                        , substitution = mempty
                        }
                    ]
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.functionalConstr10 Mock.cf
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.functionalConstr11 Mock.cg
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.functionalConstr10 Mock.ch
                        , predicate = makeTruePredicate_
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult "f" "g or h"
            expectEvaluateEquals
            Equals
                { equalsOperandSort = testSort
                , equalsResultSort = testSort
                , equalsFirst = first
                , equalsSecond = second
                }

    , testCase "f vs g[x = a] or h" $ do
        let definedF = makeCeilPredicate_ Mock.cf
            definedG = makeCeilPredicate_ Mock.cg
            predicateSubstitution =
                makeEqualsPredicate_ (mkElemVar Mock.x) Mock.a
            definedGWithSubstitution =
                makeAndPredicate
                    definedG
                    predicateSubstitution
            definedH = makeCeilPredicate_ Mock.ch
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = makeTruePredicate Mock.testSort
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cg
                        , predicate = makeTruePredicate Mock.testSort
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = makeTruePredicate Mock.testSort
                        , substitution = mempty
                        }
                    ]
            expectEvaluateEquals =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ definedF
                            , definedG
                            , makeImpliesPredicate
                                definedGWithSubstitution
                                (makeEqualsPredicate_ Mock.cf Mock.cg)
                            , makeImpliesPredicate
                                definedH
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            ]
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ definedF
                            , definedH
                            , makeImpliesPredicate
                                definedGWithSubstitution
                                (makeEqualsPredicate_ Mock.cf Mock.cg)
                            , makeImpliesPredicate
                                definedH
                                (makeEqualsPredicate_ Mock.cf Mock.ch)
                            ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeNotPredicate definedGWithSubstitution
                            , makeNotPredicate definedF
                            , makeNotPredicate definedH
                            ]
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult "f" "g[x = a] or h"
            expectEvaluateEquals
            Equals
                { equalsOperandSort = testSort
                , equalsResultSort = testSort
                , equalsFirst = first
                , equalsSecond = second
                }
    ]

test_equalsSimplification_Pattern :: [TestTree]
test_equalsSimplification_Pattern =
    [ testCase "predicate-substitution vs predicate-substitution" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeIffPredicate
                                (makeEqualsPredicate_ fOfA fOfB)
                                (makeEqualsPredicate_ gOfA gOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate_ fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate_ gOfA gOfB
                    , substitution = mempty
                    }
        assertEqual "" expect actual

    , testCase "sorted equals predicate" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeIffPredicate
                                (makeEqualsPredicate Mock.testSort fOfA fOfB)
                                (makeEqualsPredicate_ gOfA gOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeEqualsPredicate_ fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeEqualsPredicate_ gOfA gOfB
                    , substitution = mempty
                    }
        assertEqual "" expect actual

    , testCase "constructor-patt vs constructor-patt" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ makeCeilPredicate_ hOfA
                            , makeCeilPredicate_ hOfB
                            , makeEqualsPredicate_ fOfA fOfB
                            , makeEqualsPredicate_ gOfA gOfB
                            , makeEqualsPredicate_ hOfA hOfB
                            ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeNotPredicate
                                    (makeAndPredicate
                                        (makeCeilPredicate_ hOfA)
                                        (makeEqualsPredicate_ fOfA fOfB)
                                    )
                                )
                                (makeNotPredicate
                                    (makeAndPredicate
                                        (makeCeilPredicate_ hOfB)
                                        (makeEqualsPredicate_ gOfA gOfB)
                                    )
                                )
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = Mock.functionalConstr10 hOfA
                    , predicate = makeEqualsPredicate_ fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.functionalConstr10 hOfB
                    , predicate = makeEqualsPredicate_ gOfA gOfB
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    ]

test_equalsSimplification_TermLike :: [TestTree]
test_equalsSimplification_TermLike =
    [ testCase "bottom == bottom"
        (assertTermEquals
            Condition.topCondition
            mkBottom_
            mkBottom_
        )
    , testCase "domain-value == domain-value"
        (assertTermEquals
            Condition.topCondition
            (mkDomainValue DomainValue
                { domainValueSort = testSort
                , domainValueChild = mkStringLiteral "a"
                }
            )
            (mkDomainValue DomainValue
                { domainValueSort = testSort
                , domainValueChild = mkStringLiteral "a"
                }
            )
        )
    , testCase "domain-value != domain-value"
        (assertTermEquals
            Condition.bottomCondition
            (mkDomainValue DomainValue
                { domainValueSort = testSort
                , domainValueChild = mkStringLiteral "a"
                }
            )
            (mkDomainValue DomainValue
                { domainValueSort = testSort
                , domainValueChild = mkStringLiteral "b"
                }
            )
        )
    , testCase "\"a\" == \"a\""
        (assertTermEqualsGeneric
            Condition.topCondition
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase "\"a\" != \"b\""
        (assertTermEqualsGeneric
            Condition.bottomCondition
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase "a != bottom"
        (assertTermEquals
            Condition.bottomCondition
            mkBottom_
            Mock.a
        )
    , testCase "a == a"
        (assertTermEquals
            Condition.topCondition
            Mock.a
            Mock.a
        )
    , testCase "f(a) vs g(a)"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate_ fOfA gOfA
                , substitution = mempty
                }
            fOfA
            gOfA
        )
    , testCase "constructor1(a) vs constructor1(a)"
        (assertTermEquals
            Condition.topCondition
            constructor1OfA
            constructor1OfA
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a)"
        (assertTermEquals
            Condition.bottomCondition
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase "constructor1(a) vs constructor2(a)"
        (assertTermEquals
            Condition.bottomCondition
            constructor1OfA
            constructor2OfA
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a))"
        (assertTermEquals
            Condition.topCondition
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
        (assertTermEqualsMulti
            [ Conditional
                { term = ()
                , predicate =
                    makeAndPredicate
                        (makeEqualsPredicate Mock.testSort fOfA gOfA)
                        (makeEqualsPredicate_ fOfB gOfB)
                , substitution = mempty
                }
            , Conditional
                { term = ()
                , predicate =
                    makeAndPredicate
                        (makeNotPredicate
                            (makeAndPredicate
                                (makeCeilPredicate_ fOfA)
                                (makeCeilPredicate_ fOfB)
                            )
                        )
                        (makeNotPredicate
                            (makeAndPredicate
                                (makeCeilPredicate_ gOfA)
                                (makeCeilPredicate_ gOfB)
                            )
                        )
                , substitution = mempty
                }
            ]
            (Mock.functionalConstr20 fOfA fOfB)
            (Mock.functionalConstr20 gOfA gOfB)
        )
    , testCase "equals(x, functional) becomes a substitution"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeTruePredicate Mock.testSort
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.x, functionalOfA)]
                }
                (mkElemVar Mock.x)
                functionalOfA
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeTruePredicate Mock.testSort
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.x, functionalOfA)]
                }
                functionalOfA
                (mkElemVar Mock.x)
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate Mock.testSort fOfA
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.x, fOfA)]
                }
            (mkElemVar Mock.x)
            fOfA
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate Mock.testSort fOfA
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.x, fOfA)]
                }
            fOfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(x, constructor) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate_ (mkElemVar Mock.x) constructor1OfA
                , substitution = mempty
                }
            (mkElemVar Mock.x)
            constructor1OfA
        )
    , testCase "equals(constructor, x) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate_ constructor1OfA (mkElemVar Mock.x)
                , substitution = mempty
                }
            constructor1OfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(x, something) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate_ (mkElemVar Mock.x) plain1OfA
                , substitution = mempty
                }
            (mkElemVar Mock.x)
            plain1OfA
        )
    , testCase "equals(something, x) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate_ plain1OfA (mkElemVar Mock.x)
                , substitution = mempty
                }
            plain1OfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(function, constructor) is not simplifiable"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate_ (Mock.f Mock.a) Mock.a
                , substitution = mempty
                }
                (Mock.f Mock.a)
                Mock.a
        )
    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys"
            (assertTermEquals
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate Mock.mapSort
                    , substitution =
                        Substitution.unsafeWrap [(inject Mock.x, Mock.b)]
                    }
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            )
        , testCase "concrete Map, different keys"
            (assertTermEquals
                Condition.bottomCondition
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.b, mkElemVar Mock.x)])
            )
        , testCase "concrete Map with framed Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate_ fOfA)
                                    (makeCeilPredicate_ fOfB)
                                )
                            )
                            (makeNotPredicate
                                (makeCeilPredicate_
                                    (Mock.concatMap
                                        (Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.x)]
                                        )
                                        (mkElemVar Mock.m)
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.mapSort fOfB)
                            (makeCeilPredicate Mock.mapSort fOfA)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [ (inject Mock.x, fOfA)
                        , (inject Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                ]
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    (mkElemVar Mock.m)
                )
            )
        , testCase "concrete Map with framed Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate_ fOfA)
                                    (makeCeilPredicate_ fOfB)
                                )
                            )
                            (makeNotPredicate
                                (makeCeilPredicate_
                                    (Mock.concatMap
                                        (mkElemVar Mock.m)
                                        (Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.x)]
                                        )
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.mapSort fOfB)
                            (makeCeilPredicate Mock.mapSort fOfA)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [ (inject Mock.x, fOfA)
                        , (inject Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                ]
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                (Mock.concatMap
                    (mkElemVar Mock.m)
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                )
            )
        , testCase "framed Map with concrete Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate_ fOfA)
                                    (makeCeilPredicate_ fOfB)
                                )
                            )
                            (makeNotPredicate
                                (makeCeilPredicate_
                                    (Mock.concatMap
                                        (Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.x)]
                                        )
                                        (mkElemVar Mock.m)
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.mapSort fOfB)
                            (makeCeilPredicate Mock.mapSort fOfA)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [ (inject Mock.x, fOfA)
                        , (inject Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                ]
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    (mkElemVar Mock.m)
                )
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            )
        , testCase "framed Map with concrete Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate_ fOfA)
                                    (makeCeilPredicate_ fOfB)
                                )
                            )
                            (makeNotPredicate
                                (makeCeilPredicate_
                                    (Mock.concatMap
                                        (mkElemVar Mock.m)
                                        (Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.x)]
                                        )
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.mapSort fOfB)
                            (makeCeilPredicate Mock.mapSort fOfA)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [ (inject Mock.x, fOfA)
                        , (inject Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                ]
                (Mock.concatMap
                    (mkElemVar Mock.m)
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                )
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
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
                        Conditional
                            { term = ()
                            , predicate = makeTruePredicate_
                            , substitution = mempty
                            }
                        term1
                        term1
                    )
        ,
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                unified34 = Condition.bottomCondition
            in
                testCase "[same head, different head]"
                    (assertTermEquals
                        unified34
                        term3
                        term4
                    )
        ,
            let x = mkElementVariable "x" Mock.listSort
                term5 =
                    Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
            in
                testCase "[a] `concat` x /\\ [a, b] "
                    (assertTermEquals
                        Conditional
                            { term = ()
                            -- TODO(virgil): This sort should be listSort.
                            , predicate = makeTruePredicate Mock.testSort
                            , substitution = Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                [(inject x, Mock.builtinList [Mock.b])]
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
                        Condition.bottomCondition
                        term7
                        term8
                    )
        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set equality.
    ]

assertBidirectionalEqualityResult
    :: String
    -> String
    -> OrPattern VariableName
    -> Equals Sort (OrPattern VariableName)
    -> IO ()
assertBidirectionalEqualityResult
    firstName
    secondName
    expectEvaluateEquals
    equality@Equals{equalsFirst, equalsSecond}
  = do
    testOneDirection equality
    let reverseEquality = equality
            { equalsFirst = equalsSecond
            , equalsSecond = equalsFirst
            }
    testOneDirection reverseEquality
  where
    testOneDirection orderedEquality = do
        actualEvaluateEquals <- evaluateOr orderedEquality
        let assertEqual' name expect actual =
                let message =
                        unlines
                        [ firstName ++ " vs " ++ secondName ++ ":"
                        , "Expected " <> name
                        , unparseToString (OrPattern.toPattern <$> orderedEquality)
                        , "would simplify to:"
                        , unlines (unparseToString <$> toList expect)
                        , "but instead found:"
                        , unlines (unparseToString <$> toList actual)
                        ]
                 in assertEqual message expect actual
        assertEqual' "evaluate equals"
            expectEvaluateEquals
            actualEvaluateEquals

assertTermEquals
    :: HasCallStack
    => Condition VariableName
    -> TermLike VariableName
    -> TermLike VariableName
    -> IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric
    :: HasCallStack
    => Condition VariableName
    -> TermLike VariableName
    -> TermLike VariableName
    -> Assertion
assertTermEqualsGeneric expectPure =
    assertTermEqualsMultiGeneric [expectPure]


assertTermEqualsMulti
    :: HasCallStack
    => [Condition VariableName]
    -> TermLike VariableName
    -> TermLike VariableName
    -> IO ()
assertTermEqualsMulti = assertTermEqualsMultiGeneric

assertTermEqualsMultiGeneric
    :: HasCallStack
    => [Condition VariableName]
    -> TermLike VariableName
    -> TermLike VariableName
    -> Assertion
assertTermEqualsMultiGeneric expectPure first second = do
    let expectExpanded =
            OrPattern.fromPatterns
                (map predSubstToPattern expectPure)
    actualExpanded <- evaluate (termToPattern first) (termToPattern second)
    assertEqual
        "Pattern"
        expectExpanded
        actualExpanded
    actualPure <- evaluateTermsGeneric first second
    assertEqual
        "PureMLPattern"
        (MultiOr.make expectPure)
        actualPure
  where
    termToPattern :: TermLike VariableName -> Pattern VariableName
    termToPattern (Bottom_ _) =
        Conditional.bottom
    termToPattern term =
        Conditional
            { term = term
            , predicate = makeTruePredicate_
            , substitution = mempty
            }
    predSubstToPattern :: Condition VariableName -> Pattern VariableName
    predSubstToPattern
        Conditional {predicate = PredicateFalse}
      =
        Conditional.bottom
    predSubstToPattern
        Conditional {predicate, substitution}
      =
        Conditional
            { term = mkTop_
            , predicate = predicate
            , substitution = substitution
            }

fOfA :: TermLike VariableName
fOfA = Mock.f Mock.a

fOfB :: TermLike VariableName
fOfB = Mock.f Mock.b

gOfA :: TermLike VariableName
gOfA = Mock.g Mock.a

gOfB :: TermLike VariableName
gOfB = Mock.g Mock.b

hOfA :: TermLike VariableName
hOfA = Mock.h Mock.a

hOfB :: TermLike VariableName
hOfB = Mock.h Mock.b

functionalOfA :: TermLike VariableName
functionalOfA = Mock.functional10 Mock.a

constructor1OfA :: TermLike VariableName
constructor1OfA = Mock.constr10 Mock.a

constructor2OfA :: TermLike VariableName
constructor2OfA = Mock.constr11 Mock.a

functionalConstructor1OfA :: TermLike VariableName
functionalConstructor1OfA = Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: TermLike VariableName
functionalConstructor2OfA = Mock.functionalConstr11 Mock.a

plain1OfA :: TermLike VariableName
plain1OfA = Mock.plain10 Mock.a

testSort :: Sort
testSort = Mock.testSort

evaluateOr
    :: Equals Sort (OrPattern VariableName)
    -> IO (OrPattern VariableName)
evaluateOr =
    runSimplifier mockEnv
    . simplify SideCondition.top
    . fmap simplifiedOrPattern
  where
    mockEnv = Mock.env

evaluate
    :: Pattern VariableName
    -> Pattern VariableName
    -> IO (OrPattern VariableName)
evaluate first second =
    runSimplifier mockEnv
    $ makeEvaluate
        (simplifiedPattern first)
        (simplifiedPattern second)
        SideCondition.top
  where
    mockEnv = Mock.env

evaluateTermsGeneric
    :: TermLike VariableName
    -> TermLike VariableName
    -> IO (OrCondition VariableName)
evaluateTermsGeneric first second =
    runSimplifier mockEnv
    $ makeEvaluateTermsToPredicate
        (simplifiedTerm first)
        (simplifiedTerm second)
        SideCondition.top
  where
    mockEnv = Mock.env
