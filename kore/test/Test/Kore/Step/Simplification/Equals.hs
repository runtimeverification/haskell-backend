module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_TermLike
    , test_equalsSimplification_Or_Pattern
    , test_equalsSimplification_Pattern
    ) where

import Test.Tasty

import qualified Data.Foldable as Foldable

import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Conditional
import qualified Kore.Internal.Pattern as Pattern
    ( fromCondition
    )
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Equals
    ( makeEvaluate
    , makeEvaluateTermsToPredicate
    , simplify
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_equalsSimplification_Or_Pattern :: [TestTree]
test_equalsSimplification_Or_Pattern =
    [ testCase "bottom == bottom" $ do
        let expect = OrPattern.top
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
        let expect = OrPattern.top
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "a != bottom" $ do
        let expect = OrPattern.fromPattern Conditional
                { term = mkOr
                    (mkAnd
                        (mkNot (mkCeil_ Mock.a))
                        mkTop_
                    )
                    (mkAnd
                        mkBottom_
                        (mkCeil_ Mock.a)
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns []
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "f(a) vs g(a)" $ do
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = mempty
                    }
        actual <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = OrPattern.fromPatterns
                        [ Conditional
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , equalsSecond = OrPattern.fromPatterns
                        [ Conditional
                            { term = gOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    }
        assertEqual "" expect actual

    , testCase "f vs g or h" $ do
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkOr
                        (mkAnd
                            (mkNot (mkCeil_ Mock.cf))
                            (mkAnd
                                (mkNot (mkCeil_ Mock.cg))
                                (mkAnd
                                    (mkNot (mkCeil_ Mock.ch))
                                    mkTop_
                                )
                            )

                        )
                        (mkAnd
                            (mkOr
                                (mkOr
                                    mkBottom_
                                    (mkCeil_ Mock.cg)
                                )
                                (mkCeil_ Mock.ch)
                            )
                            (mkAnd
                                (mkImplies (mkCeil_ Mock.cg)
                                    (mkEquals_ Mock.cf Mock.cg)
                                )
                                (mkAnd
                                    (mkImplies (mkCeil_ Mock.ch)
                                        (mkEquals_ Mock.cf Mock.ch)
                                    )
                                    (mkCeil_ Mock.cf)
                                )
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
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
        actual1 <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = first
                    , equalsSecond = second
                    }
        assertEqual "f vs g or h" expect actual1
        actual2 <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = second
                    , equalsSecond = first
                    }
        assertEqual "g or h or f" expect actual2

    , testCase "f vs g[x = a] or h" $ do
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkOr
                        (mkAnd
                            (mkNot (mkCeil_ Mock.cf))
                            (mkAnd
                                (mkNot
                                    (mkCeil_
                                        (mkAnd
                                            Mock.cg
                                            (mkEquals_
                                                (mkElemVar Mock.x)
                                                Mock.a
                                            )
                                        )
                                    )
                                )
                                (mkAnd
                                    (mkNot (mkCeil_ Mock.ch))
                                    mkTop_
                                )
                            )
                        )
                        (mkAnd
                            (mkOr
                                (mkOr
                                    mkBottom_
                                    (mkCeil_
                                        (mkAnd
                                            Mock.cg
                                            (mkEquals_ (mkElemVar Mock.x) Mock.a)
                                        )
                                    )
                                )
                                (mkCeil_ Mock.ch)
                            )
                            (mkAnd
                                (mkImplies
                                    (mkCeil_
                                        (mkAnd
                                            Mock.cg
                                            (mkEquals_
                                                (mkElemVar Mock.x)
                                                Mock.a
                                            )
                                        )
                                    )
                                    (mkEquals_ Mock.cf Mock.cg)
                                )
                                (mkAnd
                                    (mkImplies
                                        (mkCeil_ Mock.ch)
                                        (mkEquals_ Mock.cf Mock.ch)
                                    )
                                    (mkCeil_ Mock.cf)
                                )
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
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
                            Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            test1 =
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = first
                    , equalsSecond = second
                    }
        actual1 <- evaluateOr test1
        let message1 =
                unlines
                    [ "Expected"
                    , unparseToString (OrPattern.toPattern <$> test1)
                    , "would simplify to:"
                    , unlines (unparseToString <$> Foldable.toList expect)
                    , "but instead found:"
                    , unlines (unparseToString <$> Foldable.toList actual1)
                    ]
        assertEqual message1 expect actual1
        actual2 <-
            evaluateOr
                Equals
                    { equalsOperandSort = testSort
                    , equalsResultSort = testSort
                    , equalsFirst = second
                    , equalsSecond = first
                    }
        assertEqual "g[x = a] or h or f" expect actual2
    ]

test_equalsSimplification_Pattern :: [TestTree]
test_equalsSimplification_Pattern =
    [ testCase "predicate-substitution vs predicate-substitution" $ do
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkIff
                        (mkEquals_ fOfA fOfB)
                        (mkEquals_ gOfA gOfB)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
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
        assertBool "" (not (OrPattern.isSimplified actual))

    , testCase "sorted equals predicate" $ do
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkIff
                        (mkEquals_ fOfA fOfB)
                        (mkEquals_ gOfA gOfB)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
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
        let expect = OrPattern.fromPattern
                Conditional
                    { term = mkOr
                        (mkAnd
                            (mkEquals_ hOfA hOfB)
                            (mkAnd
                                (mkCeil_
                                    (mkAnd
                                        (Mock.functionalConstr10 hOfA)
                                        (mkEquals_ fOfA fOfB)
                                    )
                                )
                                (mkCeil_
                                    (mkAnd
                                        (Mock.functionalConstr10 hOfB)
                                        (mkEquals_ gOfA gOfB)
                                    )
                                )
                            )
                        )
                        (mkAnd
                            (mkNot
                                (mkCeil_
                                    (mkAnd
                                        (Mock.functionalConstr10 hOfA)
                                        (mkEquals_ fOfA fOfB)
                                    )
                                )
                            )
                            (mkNot
                                (mkCeil_
                                    (mkAnd
                                        (Mock.functionalConstr10 hOfB)
                                        (mkEquals_ gOfA gOfB)
                                    )
                                )
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
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
    , let
        dv1 = mkDomainValue DomainValue
            { domainValueSort = testSort
            , domainValueChild = mkStringLiteral "a"
            }
        dv2 = mkDomainValue DomainValue
            { domainValueSort = testSort
            , domainValueChild = mkStringLiteral "b"
            }
      in testCase "domain-value != domain-value"
        (assertTermEquals
            (Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate dv1))
                    (makeNotPredicate (makeCeilPredicate dv2))
                )
            )
            dv1
            dv2
        )
    , let
        dv1 = mkDomainValue DomainValue
            { domainValueSort = testSort
            , domainValueChild = mkStringLiteral "a"
            }
        dv2 = mkDomainValue DomainValue
            { domainValueSort = testSort2
            , domainValueChild = mkStringLiteral "a"
            }
      in testCase "domain-value != domain-value because of sorts"
        (assertTermEquals
            (Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate dv1))
                    (makeNotPredicate (makeCeilPredicate dv2))
                )
            )
            dv1
            dv2
        )
    , testCase "\"a\" == \"a\""
        (assertTermEqualsGeneric
            Condition.topCondition
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase "\"a\" != \"b\""
        (assertTermEqualsGeneric
            (Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate (mkStringLiteral "a")))
                    (makeNotPredicate (makeCeilPredicate (mkStringLiteral "b")))
                )
            )
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase "a != bottom"
        (assertTermEqualsPattern
            Conditional
                { term = mkOr
                    (mkAnd
                        mkBottom_
                        (mkAnd
                            (mkCeil_ mkBottom_)
                            (mkCeil_ Mock.a)
                        )
                    )
                    (mkAnd
                        (mkNot (mkCeil_ mkBottom_))
                        (mkNot (mkCeil_ Mock.a))
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            Conditional
                { term = ()
                , predicate = makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate mkBottom_))
                    (makeNotPredicate (makeCeilPredicate Mock.a))
                , substitution = mempty
                }
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
                , predicate = makeEqualsPredicate fOfA gOfA
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
            (Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate
                        (makeCeilPredicate functionalConstructor1OfA)
                    )
                    (makeNotPredicate
                        (makeCeilPredicate functionalConstructor2OfA)
                    )
                )
            )
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase "constructor1(a) vs constructor2(a)"
        (assertTermEquals
            (Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate constructor1OfA))
                    (makeNotPredicate (makeCeilPredicate constructor2OfA))
                )
            )
            constructor1OfA
            constructor2OfA
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a))"
        (assertTermEquals
            Condition.topCondition
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , let
        term1 = Mock.functionalConstr20 fOfA fOfB
        term2 = Mock.functionalConstr20 gOfA gOfB
      in testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
        (assertTermEqualsMulti
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
                        (makeNotPredicate (makeCeilPredicate term1))
                        (makeNotPredicate (makeCeilPredicate term2))
                , substitution = mempty
                }
            ]
            term1
            term2
        )
    , testCase "equals(x, functional) becomes a substitution"
        (assertTermEqualsMulti
            [ Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate (mkElemVar Mock.x)))
                    (makeNotPredicate (makeCeilPredicate functionalOfA))
                )
            , Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, functionalOfA)]
                }
            ]
            (mkElemVar Mock.x)
            functionalOfA
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertTermEqualsMulti
            [ Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate functionalOfA))
                    (makeNotPredicate (makeCeilPredicate (mkElemVar Mock.x)))
                )
            , Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, functionalOfA)]
                }
            ]
            functionalOfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertTermEqualsMulti
            [ Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate (mkElemVar Mock.x)))
                    (makeNotPredicate (makeCeilPredicate fOfA))
                )
            , Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                }
            ]
            (mkElemVar Mock.x)
            fOfA
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertTermEqualsMulti
            [ Condition.fromPredicate
                (makeAndPredicate
                    (makeNotPredicate (makeCeilPredicate fOfA))
                    (makeNotPredicate (makeCeilPredicate (mkElemVar Mock.x)))
                )
            , Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                }
            ]
            fOfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(x, constructor) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate =
                    makeEqualsPredicate (mkElemVar Mock.x) constructor1OfA
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
                    makeEqualsPredicate constructor1OfA (mkElemVar Mock.x)
                , substitution = mempty
                }
            constructor1OfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(x, something) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate (mkElemVar Mock.x) plain1OfA
                , substitution = mempty
                }
            (mkElemVar Mock.x)
            plain1OfA
        )
    , testCase "equals(something, x) becomes a predicate"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate plain1OfA (mkElemVar Mock.x)
                , substitution = mempty
                }
            plain1OfA
            (mkElemVar Mock.x)
        )
    , testCase "equals(function, constructor) is not simplifiable"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                , substitution = mempty
                }
                (Mock.f Mock.a)
                Mock.a
        )
    , testGroup "builtin Map domain"
        [ let
            map1 = Mock.builtinMap [(Mock.a, Mock.b)]
            map2 = Mock.builtinMap [(Mock.a, mkElemVar Mock.x)]
          in testCase "concrete Map, same keys"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                    }
                , Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate map1))
                        (makeNotPredicate (makeCeilPredicate map2))
                    )
                ]
                map1
                map2
            )
        , let
            map1 = Mock.builtinMap [(Mock.a, Mock.b)]
            map2 = Mock.builtinMap [(Mock.b, mkElemVar Mock.x)]
          in testCase "concrete Map, different keys"
            (assertTermEquals
                (Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate map1))
                        (makeNotPredicate (makeCeilPredicate map2))
                    )
                )
                map1
                map2
            )
        , let
            framedMap = Mock.concatMap
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                (mkElemVar Mock.m)
            concreteMap =
                Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
          in testCase "concrete Map with framed Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap
                        [ (ElemVar Mock.x, fOfA)
                        , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                , Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate concreteMap))
                        (makeNotPredicate (makeCeilPredicate framedMap))
                    )
                ]
                concreteMap
                framedMap
            )
        , let
            framedMap = Mock.concatMap
                (mkElemVar Mock.m)
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            concreteMap = Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
          in testCase "concrete Map with framed Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap
                        [ (ElemVar Mock.x, fOfA)
                        , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                , Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate concreteMap))
                        (makeNotPredicate (makeCeilPredicate framedMap))
                    )
                ]
                concreteMap
                framedMap
            )
        , let
            framedMap = Mock.concatMap
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                (mkElemVar Mock.m)
            concreteMap = Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
          in testCase "framed Map with concrete Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap
                        [ (ElemVar Mock.x, fOfA)
                        , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                , Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate framedMap))
                        (makeNotPredicate (makeCeilPredicate concreteMap))
                    )
                ]
                framedMap
                concreteMap
            )
        , let
            framedMap = Mock.concatMap
                (mkElemVar Mock.m)
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            concreteMap = Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
          in testCase "framed Map with concrete Map"
            (assertTermEqualsMulti
                [ Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap
                        [ (ElemVar Mock.x, fOfA)
                        , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                        ]
                    }
                , Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate framedMap))
                        (makeNotPredicate (makeCeilPredicate concreteMap))
                    )
                ]
                framedMap
                concreteMap
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
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        term1
                        term1
                    )
        ,
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                unified34 = Condition.fromPredicate
                    (makeAndPredicate
                        (makeNotPredicate (makeCeilPredicate term3))
                        (makeNotPredicate (makeCeilPredicate term4))
                    )
            in
                testCase "[same head, different head]"
                    (assertTermEquals
                        unified34
                        term3
                        term4
                    )
        ,
            let x = elemVarS "x" Mock.listSort
                term5 =
                    Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
            in
                testCase "[a] `concat` x /\\ [a, b] "
                    (assertTermEqualsMulti
                        [ Condition.fromSingleSubstitution
                            (ElemVar x, Mock.builtinList [Mock.b])
                        , Condition.fromPredicate
                            (makeAndPredicate
                                (makeNotPredicate (makeCeilPredicate term5))
                                (makeNotPredicate (makeCeilPredicate term6))
                            )
                        ]
                        term5
                        term6
                    )
        ,
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
            in
                testCase "different lengths"
                    (assertTermEquals
                        (Condition.fromPredicate
                            (makeAndPredicate
                                (makeNotPredicate (makeCeilPredicate term7))
                                (makeNotPredicate (makeCeilPredicate term8))
                            )
                        )
                        term7
                        term8
                    )
        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set equality.
    ]

assertTermEquals
    :: HasCallStack
    => Condition Variable
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric
    :: HasCallStack
    => Condition Variable
    -> TermLike Variable
    -> TermLike Variable
    -> Assertion
assertTermEqualsGeneric expectPure =
    assertTermEqualsMultiGeneric [Pattern.fromCondition expectPure] [expectPure]

assertTermEqualsMulti
    :: HasCallStack
    => [Condition Variable]
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEqualsMulti conditions =
    assertTermEqualsMultiGeneric
        (Pattern.fromCondition <$> conditions)
        conditions

assertTermEqualsPattern
    :: HasCallStack
    => Pattern Variable
    -> Condition Variable
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEqualsPattern = assertTermEqualsGenericPattern

assertTermEqualsGenericPattern
    :: HasCallStack
    => Pattern Variable
    -> Condition Variable
    -> TermLike Variable
    -> TermLike Variable
    -> Assertion
assertTermEqualsGenericPattern expectPure expectPureCondition =
    assertTermEqualsMultiPattern [expectPure] [expectPureCondition]

assertTermEqualsMultiPattern
    :: HasCallStack
    => [Pattern Variable]
    -> [Condition Variable]
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEqualsMultiPattern = assertTermEqualsMultiGeneric

assertTermEqualsMultiGeneric
    :: HasCallStack
    => [Pattern Variable]
    -> [Condition Variable]
    -> TermLike Variable
    -> TermLike Variable
    -> Assertion
assertTermEqualsMultiGeneric expectPure expectPureCondition first second = do
    let expectExpanded :: OrPattern Variable
        expectExpanded = OrPattern.fromPatterns expectPure
    actualExpanded <- evaluate (termToPattern first) (termToPattern second)
    assertEqual
        "Pattern"
        expectExpanded
        actualExpanded
    actualPure <- evaluateTermsGeneric first second
    assertEqual
        "PureMLPattern"
        (OrCondition.fromConditions expectPureCondition)
        actualPure
  where
    termToPattern :: TermLike Variable -> Pattern Variable
    termToPattern (Bottom_ _) =
        Conditional.bottom
    termToPattern term =
        Conditional
            { term = term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    {-
    predSubstToPattern :: Condition Variable -> Pattern Variable
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
            -}

fOfA :: TermLike Variable
fOfA = Mock.f Mock.a

fOfB :: TermLike Variable
fOfB = Mock.f Mock.b

gOfA :: TermLike Variable
gOfA = Mock.g Mock.a

gOfB :: TermLike Variable
gOfB = Mock.g Mock.b

hOfA :: TermLike Variable
hOfA = Mock.h Mock.a

hOfB :: TermLike Variable
hOfB = Mock.h Mock.b

functionalOfA :: TermLike Variable
functionalOfA = Mock.functional10 Mock.a

constructor1OfA :: TermLike Variable
constructor1OfA = Mock.constr10 Mock.a

constructor2OfA :: TermLike Variable
constructor2OfA = Mock.constr11 Mock.a

functionalConstructor1OfA :: TermLike Variable
functionalConstructor1OfA = Mock.functionalConstr10 Mock.a

functionalConstructor2OfA :: TermLike Variable
functionalConstructor2OfA = Mock.functionalConstr11 Mock.a

plain1OfA :: TermLike Variable
plain1OfA = Mock.plain10 Mock.a

testSort :: Sort
testSort = Mock.testSort

testSort2 :: Sort
testSort2 =
    SortActualSort SortActual
        { sortActualName  = Id "testSort2" AstLocationTest
        , sortActualSorts = []
        }

evaluateOr
    :: Equals Sort (OrPattern Variable)
    -> IO (OrPattern Variable)
evaluateOr =
    runSimplifier mockEnv . simplify
  where
    mockEnv = Mock.env

evaluate
    :: Pattern Variable
    -> Pattern Variable
    -> IO (OrPattern Variable)
evaluate first second =
    runSimplifier mockEnv
    $ makeEvaluate first second
  where
    mockEnv = Mock.env

evaluateTermsGeneric
    :: TermLike Variable
    -> TermLike Variable
    -> IO (OrCondition Variable)
evaluateTermsGeneric first second =
    runSimplifier mockEnv
    $ makeEvaluateTermsToPredicate first second
  where
    mockEnv = Mock.env
