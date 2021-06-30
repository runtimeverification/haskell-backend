module Test.Kore.Simplify.Equals (
    test_equalsSimplification_TermLike,
    test_equalsSimplification_Or_Pattern,
    test_equalsSimplification_Pattern,
) where

import Kore.Internal.Condition (
    Condition,
    Conditional (..),
 )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeIffPredicate,
    makeImpliesPredicate,
    makeNotPredicate,
    makeTruePredicate,
    pattern PredicateFalse,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.Equals (
    makeEvaluate,
    makeEvaluateTermsToPredicate,
    simplify,
 )
import Kore.Unparser
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_equalsSimplification_Or_Pattern :: [TestTree]
test_equalsSimplification_Or_Pattern =
    [ testCase "bottom == bottom" $ do
        let expect = OrPattern.fromPatterns [Conditional.top]
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
        let expect = OrPattern.fromPatterns [Conditional.top]
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst =
                        OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                    , equalsSecond =
                        OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.a
                                , predicate = makeTruePredicate
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
                    , equalsSecond =
                        OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.a
                                , predicate = makeTruePredicate
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
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst =
                        OrPattern.fromPatterns
                            [ Conditional
                                { term = fOfA
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                    , equalsSecond =
                        OrPattern.fromPatterns
                            [ Conditional
                                { term = gOfA
                                , predicate = makeTruePredicate
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
                                [ makeCeilPredicate Mock.cf
                                , makeCeilPredicate Mock.cg
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                                [ makeCeilPredicate Mock.cf
                                , makeCeilPredicate Mock.ch
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                                [ makeNotPredicate $ makeCeilPredicate Mock.cf
                                , makeNotPredicate $ makeCeilPredicate Mock.cg
                                , makeNotPredicate $ makeCeilPredicate Mock.ch
                                ]
                        , substitution = mempty
                        }
                    ]
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cg
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult
            "f"
            "g or h"
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
                                [ makeCeilPredicate Mock.cf
                                , makeCeilPredicate Mock.cg
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                , makeNotPredicate (makeCeilPredicate Mock.cg)
                                ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                                [ makeCeilPredicate Mock.cf
                                , makeCeilPredicate Mock.ch
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                , makeNotPredicate $ makeCeilPredicate Mock.cg
                                ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                                [ makeNotPredicate $ makeCeilPredicate Mock.cf
                                , makeNotPredicate $ makeCeilPredicate Mock.cg
                                , makeNotPredicate $ makeCeilPredicate Mock.ch
                                ]
                        , substitution = mempty
                        }
                    ]
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.functionalConstr10 Mock.cf
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.functionalConstr11 Mock.cg
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.functionalConstr10 Mock.ch
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult
            "f"
            "g or h"
            expectEvaluateEquals
            Equals
                { equalsOperandSort = testSort
                , equalsResultSort = testSort
                , equalsFirst = first
                , equalsSecond = second
                }
    , testCase "f vs g[x = a] or h" $ do
        let definedF = makeCeilPredicate Mock.cf
            definedG = makeCeilPredicate Mock.cg
            predicateSubstitution =
                makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.a
            definedGWithSubstitution =
                makeAndPredicate
                    definedG
                    predicateSubstitution
            definedH = makeCeilPredicate Mock.ch
            first =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cf
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            second =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.cg
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.xConfig, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = makeTruePredicate
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
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    definedH
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                ]
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.xConfig, Mock.a)]
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                                [ definedF
                                , definedH
                                , makeImpliesPredicate
                                    definedGWithSubstitution
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    definedH
                                    (makeEqualsPredicate Mock.cf Mock.ch)
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
        assertBidirectionalEqualityResult
            "f"
            "g[x = a] or h"
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
                                (makeEqualsPredicate fOfA fOfB)
                                (makeEqualsPredicate gOfA gOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate gOfA gOfB
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
                                (makeEqualsPredicate fOfA fOfB)
                                (makeEqualsPredicate gOfA gOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeEqualsPredicate gOfA gOfB
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
                                [ makeCeilPredicate hOfA
                                , makeCeilPredicate hOfB
                                , makeEqualsPredicate fOfA fOfB
                                , makeEqualsPredicate gOfA gOfB
                                , makeEqualsPredicate hOfA hOfB
                                ]
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                ( makeNotPredicate
                                    ( makeAndPredicate
                                        (makeCeilPredicate hOfA)
                                        (makeEqualsPredicate fOfA fOfB)
                                    )
                                )
                                ( makeNotPredicate
                                    ( makeAndPredicate
                                        (makeCeilPredicate hOfB)
                                        (makeEqualsPredicate gOfA gOfB)
                                    )
                                )
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = Mock.functionalConstr10 hOfA
                    , predicate = makeEqualsPredicate fOfA fOfB
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.functionalConstr10 hOfB
                    , predicate = makeEqualsPredicate gOfA gOfB
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    ]

test_equalsSimplification_TermLike :: [TestTree]
test_equalsSimplification_TermLike =
    [ testCase
        "bottom == bottom"
        ( assertTermEquals
            Condition.topCondition
            mkBottom_
            mkBottom_
        )
    , testCase
        "domain-value == domain-value"
        ( assertTermEquals
            Condition.topCondition
            ( mkDomainValue
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "a"
                    }
            )
            ( mkDomainValue
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "a"
                    }
            )
        )
    , testCase
        "domain-value != domain-value"
        ( assertTermEquals
            Condition.bottomCondition
            ( mkDomainValue
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "a"
                    }
            )
            ( mkDomainValue
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "b"
                    }
            )
        )
    , testCase
        "\"a\" == \"a\""
        ( assertTermEqualsGeneric
            Condition.topCondition
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase
        "\"a\" != \"b\""
        ( assertTermEqualsGeneric
            Condition.bottomCondition
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase
        "a != bottom"
        ( assertTermEquals
            Condition.bottomCondition
            mkBottom_
            Mock.a
        )
    , testCase
        "a == a"
        ( assertTermEquals
            Condition.topCondition
            Mock.a
            Mock.a
        )
    , testCase
        "f(a) vs g(a)"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = mempty
                }
            fOfA
            gOfA
        )
    , testCase
        "constructor1(a) vs constructor1(a)"
        ( assertTermEquals
            Condition.topCondition
            constructor1OfA
            constructor1OfA
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a)"
        ( assertTermEquals
            Condition.bottomCondition
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase
        "constructor1(a) vs constructor2(a)"
        ( assertTermEquals
            Condition.bottomCondition
            constructor1OfA
            constructor2OfA
        )
    , testCase
        "constructor1(f(a)) vs constructor1(f(a))"
        ( assertTermEquals
            Condition.topCondition
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , testCase
        "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
        ( assertTermEqualsMulti
            [ Conditional
                { term = ()
                , predicate =
                    makeAndPredicate
                        (makeEqualsPredicate fOfA gOfA)
                        (makeEqualsPredicate fOfB gOfB)
                , substitution = mempty
                }
            , Conditional
                { term = ()
                , predicate =
                    makeAndPredicate
                        ( makeNotPredicate
                            ( makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                            )
                        )
                        ( makeNotPredicate
                            ( makeAndPredicate
                                (makeCeilPredicate gOfA)
                                (makeCeilPredicate gOfB)
                            )
                        )
                , substitution = mempty
                }
            ]
            (Mock.functionalConstr20 fOfA fOfB)
            (Mock.functionalConstr20 gOfA gOfB)
        )
    , testCase
        "equals(x, functional) becomes a substitution"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.xConfig, functionalOfA)]
                }
            (mkElemVar Mock.xConfig)
            functionalOfA
        )
    , testCase
        "equals(functional, x) becomes a substitution"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap
                        [(inject Mock.xConfig, functionalOfA)]
                }
            functionalOfA
            (mkElemVar Mock.xConfig)
        )
    , testCase
        "equals(x, function) becomes a substitution + ceil"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.xConfig, fOfA)]
                }
            (mkElemVar Mock.xConfig)
            fOfA
        )
    , testCase
        "equals(function, x) becomes a substitution + ceil"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(inject Mock.xConfig, fOfA)]
                }
            fOfA
            (mkElemVar Mock.xConfig)
        )
    , testCase
        "equals(x, constructor) becomes a predicate"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate (mkElemVar Mock.xConfig) constructor1OfA
                , substitution = mempty
                }
            (mkElemVar Mock.xConfig)
            constructor1OfA
        )
    , testCase
        "equals(constructor, x) becomes a predicate"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate constructor1OfA (mkElemVar Mock.xConfig)
                , substitution = mempty
                }
            constructor1OfA
            (mkElemVar Mock.xConfig)
        )
    , testCase
        "equals(x, something) becomes a predicate"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate (mkElemVar Mock.xConfig) plain1OfA
                , substitution = mempty
                }
            (mkElemVar Mock.xConfig)
            plain1OfA
        )
    , testCase
        "equals(something, x) becomes a predicate"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate plain1OfA (mkElemVar Mock.xConfig)
                , substitution = mempty
                }
            plain1OfA
            (mkElemVar Mock.xConfig)
        )
    , testCase
        "equals(function, constructor) is not simplifiable"
        ( assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                , substitution = mempty
                }
            (Mock.f Mock.a)
            Mock.a
        )
    , testGroup
        "builtin Map domain"
        [ testCase
            "concrete Map, same keys"
            ( assertTermEquals
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(inject Mock.xConfig, Mock.b)]
                    }
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
            )
        , testCase
            "concrete Map, different keys"
            ( assertTermEquals
                Condition.bottomCondition
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.b, mkElemVar Mock.xConfig)])
            )
        , testCase
            "concrete Map with framed Map"
            ( assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeNotPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                            )
                            ( makeNotPredicate
                                ( makeCeilPredicate
                                    ( Mock.concatMap
                                        ( Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.xConfig)]
                                        )
                                        (mkElemVar Mock.mConfig)
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, fOfA)
                                , (inject Mock.mConfig, Mock.builtinMap [(Mock.b, fOfB)])
                                ]
                    }
                ]
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                ( Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                    (mkElemVar Mock.mConfig)
                )
            )
        , testCase
            "concrete Map with framed Map"
            ( assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeNotPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                            )
                            ( makeNotPredicate
                                ( makeCeilPredicate
                                    ( Mock.concatMap
                                        (mkElemVar Mock.mConfig)
                                        ( Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.xConfig)]
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
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, fOfA)
                                , (inject Mock.mConfig, Mock.builtinMap [(Mock.b, fOfB)])
                                ]
                    }
                ]
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                ( Mock.concatMap
                    (mkElemVar Mock.mConfig)
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                )
            )
        , testCase
            "framed Map with concrete Map"
            ( assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeNotPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                            )
                            ( makeNotPredicate
                                ( makeCeilPredicate
                                    ( Mock.concatMap
                                        ( Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.xConfig)]
                                        )
                                        (mkElemVar Mock.mConfig)
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, fOfA)
                                , (inject Mock.mConfig, Mock.builtinMap [(Mock.b, fOfB)])
                                ]
                    }
                ]
                ( Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                    (mkElemVar Mock.mConfig)
                )
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            )
        , testCase
            "framed Map with concrete Map"
            ( assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeNotPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                            )
                            ( makeNotPredicate
                                ( makeCeilPredicate
                                    ( Mock.concatMap
                                        (mkElemVar Mock.mConfig)
                                        ( Mock.builtinMap
                                            [(Mock.a, mkElemVar Mock.xConfig)]
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
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, fOfA)
                                , (inject Mock.mConfig, Mock.builtinMap [(Mock.b, fOfB)])
                                ]
                    }
                ]
                ( Mock.concatMap
                    (mkElemVar Mock.mConfig)
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                )
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            )
            -- TODO: Add tests with non-trivial predicates.
        ]
    , testGroup
        "builtin List domain"
        [ let term1 =
                Mock.builtinList
                    [ Mock.constr10 Mock.cf
                    , Mock.constr11 Mock.cf
                    ]
           in testCase
                "[same head, same head]"
                ( assertTermEquals
                    Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    term1
                    term1
                )
        , let term3 = Mock.builtinList [Mock.a, Mock.a]
              term4 = Mock.builtinList [Mock.a, Mock.b]
              unified34 = Condition.bottomCondition
           in testCase
                "[same head, different head]"
                ( assertTermEquals
                    unified34
                    term3
                    term4
                )
        , let x =
                Variable
                    { variableName =
                        ElementVariableName
                            (mkConfigVariable $ mkVariableName "x")
                    , variableSort = Mock.listSort
                    }
              term5 =
                Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
              term6 = Mock.builtinList [Mock.a, Mock.b]
           in testCase
                "[a] `concat` x /\\ [a, b] "
                ( assertTermEquals
                    Conditional
                        { term = ()
                        , -- TODO(virgil): This sort should be listSort.
                          predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject x, Mock.builtinList [Mock.b])]
                        }
                    term5
                    term6
                )
        , let term7 = Mock.builtinList [Mock.a, Mock.a]
              term8 = Mock.builtinList [Mock.a]
           in testCase
                "different lengths"
                ( assertTermEquals
                    Condition.bottomCondition
                    term7
                    term8
                )
                -- TODO: Add tests with non-trivial unifications and predicates.
        ]
        -- TODO: Add tests for set equality.
    ]

assertBidirectionalEqualityResult ::
    String ->
    String ->
    OrPattern RewritingVariableName ->
    Equals Sort (OrPattern RewritingVariableName) ->
    IO ()
assertBidirectionalEqualityResult
    firstName
    secondName
    expectEvaluateEquals
    equality@Equals{equalsFirst, equalsSecond} =
        do
            testOneDirection equality
            let reverseEquality =
                    equality
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
                                , unparseToString
                                    (OrPattern.toTermLike <$> orderedEquality)
                                , "would simplify to:"
                                , unlines (unparseToString <$> toList expect)
                                , "but instead found:"
                                , unlines (unparseToString <$> toList actual)
                                ]
                     in assertEqual message expect actual
            assertEqual'
                "evaluate equals"
                expectEvaluateEquals
                actualEvaluateEquals

assertTermEquals ::
    HasCallStack =>
    Condition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric ::
    HasCallStack =>
    Condition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Assertion
assertTermEqualsGeneric expectPure =
    assertTermEqualsMultiGeneric [expectPure]

assertTermEqualsMulti ::
    HasCallStack =>
    [Condition RewritingVariableName] ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO ()
assertTermEqualsMulti = assertTermEqualsMultiGeneric

assertTermEqualsMultiGeneric ::
    HasCallStack =>
    [Condition RewritingVariableName] ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Assertion
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
    termToPattern ::
        TermLike RewritingVariableName -> Pattern RewritingVariableName
    termToPattern (Bottom_ _) =
        Conditional.bottom
    termToPattern term =
        Conditional
            { term = term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    predSubstToPattern ::
        Condition RewritingVariableName -> Pattern RewritingVariableName
    predSubstToPattern
        Conditional{predicate = PredicateFalse} =
            Conditional.bottom
    predSubstToPattern
        Conditional{predicate, substitution} =
            Conditional
                { term = mkTop_
                , predicate = predicate
                , substitution = substitution
                }

fOfA :: TermLike RewritingVariableName
fOfA = Mock.f Mock.a

fOfB :: TermLike RewritingVariableName
fOfB = Mock.f Mock.b

gOfA :: TermLike RewritingVariableName
gOfA = Mock.g Mock.a

gOfB :: TermLike RewritingVariableName
gOfB = Mock.g Mock.b

hOfA :: TermLike RewritingVariableName
hOfA = Mock.h Mock.a

hOfB :: TermLike RewritingVariableName
hOfB = Mock.h Mock.b

functionalOfA :: TermLike RewritingVariableName
functionalOfA = Mock.functional10 Mock.a

constructor1OfA :: TermLike RewritingVariableName
constructor1OfA = Mock.constr10 Mock.a

constructor2OfA :: TermLike RewritingVariableName
constructor2OfA = Mock.constr11 Mock.a

functionalConstructor1OfA :: TermLike RewritingVariableName
functionalConstructor1OfA = Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: TermLike RewritingVariableName
functionalConstructor2OfA = Mock.functionalConstr11 Mock.a

plain1OfA :: TermLike RewritingVariableName
plain1OfA = Mock.plain10 Mock.a

testSort :: Sort
testSort = Mock.testSort

evaluateOr ::
    Equals Sort (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
evaluateOr =
    runSimplifier mockEnv
        . simplify SideCondition.top
        . fmap simplifiedOrPattern
  where
    mockEnv = Mock.env

evaluate ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
evaluate first second =
    runSimplifier mockEnv $
        makeEvaluate
            (simplifiedPattern first)
            (simplifiedPattern second)
            SideCondition.top
  where
    mockEnv = Mock.env

evaluateTermsGeneric ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO (OrCondition RewritingVariableName)
evaluateTermsGeneric first second =
    runSimplifier mockEnv $
        makeEvaluateTermsToPredicate
            (simplifiedTerm first)
            (simplifiedTerm second)
            SideCondition.top
  where
    mockEnv = Mock.env
