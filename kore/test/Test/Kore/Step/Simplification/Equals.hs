module Test.Kore.Step.Simplification.Equals
    ( test_equalsSimplification_TermLike
    , test_equalsSimplification_Or_Pattern
    , test_equalsSimplification_Pattern
    ) where

import Test.Tasty

import qualified Data.Foldable as Foldable

import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.Predicate
    ( Conditional (..)
    , Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( pattern PredicateFalse
    , makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeIffPredicate
    , makeImpliesPredicate
    , makeMultipleAndPredicate
    , makeNotPredicate
    , makeOrPredicate
    , makeTruePredicate
    )
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
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeMultipleAndPredicate
                                [ makeCeilPredicate Mock.cf
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    (makeCeilPredicate Mock.ch)
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                , makeOrPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeCeilPredicate Mock.ch)
                                ]
                        , substitution = mempty
                        }
                    ,  Conditional
                        { term = mkTop_
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
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeMultipleAndPredicate
                                [ definedF
                                , definedG
                                , makeImpliesPredicate
                                    definedGWithSubstitution
                                    (makeEqualsPredicate Mock.cf Mock.cg)
                                , makeImpliesPredicate
                                    definedH
                                    (makeEqualsPredicate Mock.cf Mock.ch)
                                ]
                        , substitution = Substitution.unsafeWrap
                            [(ElemVar Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            makeMultipleAndPredicate
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
                            makeMultipleAndPredicate
                                [ makeNotPredicate definedGWithSubstitution
                                , makeNotPredicate definedF
                                , makeNotPredicate definedH
                                ]
                        , substitution = mempty
                        }
                    ]
              where
                definedF = makeCeilPredicate Mock.cf
                definedG = makeCeilPredicate Mock.cg
                definedGWithSubstitution =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cg)
                        (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
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

    , testCase "constructor-patt vs constructor-patt" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeOrPredicate
                                (makeAndPredicate
                                    (makeAndPredicate
                                        (makeAndPredicate
                                            (makeAndPredicate
                                                (makeCeilPredicate hOfA)
                                                (makeCeilPredicate hOfB)
                                            )
                                            (makeEqualsPredicate fOfA fOfB)
                                        )
                                        (makeEqualsPredicate gOfA gOfB)
                                    )
                                    (makeEqualsPredicate hOfA hOfB)
                                )
                                (makeAndPredicate
                                    (makeNotPredicate
                                        (makeAndPredicate
                                            (makeCeilPredicate hOfA)
                                            (makeEqualsPredicate fOfA fOfB)
                                        )
                                    )
                                    (makeNotPredicate
                                        (makeAndPredicate
                                            (makeCeilPredicate hOfB)
                                            (makeEqualsPredicate gOfA gOfB)
                                        )
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
    [ testCase "bottom == bottom"
        (assertTermEquals
            Predicate.topPredicate
            mkBottom_
            mkBottom_
        )
    , testCase "domain-value == domain-value"
        (assertTermEquals
            Predicate.topPredicate
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
            Predicate.bottomPredicate
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
    , testCase "domain-value != domain-value because of sorts"
        (assertTermEquals
            Predicate.bottomPredicate
            (mkDomainValue DomainValue
                { domainValueSort = testSort
                , domainValueChild = mkStringLiteral "a"
                }
            )
            (mkDomainValue DomainValue
                { domainValueSort = testSort2
                , domainValueChild = mkStringLiteral "a"
                }
            )
        )
    , testCase "\"a\" == \"a\""
        (assertTermEqualsGeneric
            Predicate.topPredicate
            (mkStringLiteral "a")
            (mkStringLiteral "a")
        )
    , testCase "\"a\" != \"b\""
        (assertTermEqualsGeneric
            Predicate.bottomPredicate
            (mkStringLiteral "a")
            (mkStringLiteral "b")
        )
    , testCase "a != bottom"
        (assertTermEquals
            Predicate.bottomPredicate
            mkBottom_
            Mock.a
        )
    , testCase "a == a"
        (assertTermEquals
            Predicate.topPredicate
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
            Predicate.topPredicate
            constructor1OfA
            constructor1OfA
        )
    , testCase
        "functionalconstructor1(a) vs functionalconstructor2(a)"
        (assertTermEquals
            Predicate.bottomPredicate
            functionalConstructor1OfA
            functionalConstructor2OfA
        )
    , testCase "constructor1(a) vs constructor2(a)"
        (assertTermEquals
            Predicate.bottomPredicate
            constructor1OfA
            constructor2OfA
        )
    , testCase "constructor1(f(a)) vs constructor1(f(a))"
        (assertTermEquals
            Predicate.topPredicate
            (Mock.constr10 fOfA)
            (Mock.constr10 fOfA)
        )
    , testCase "sigma(f(a), f(b)) vs sigma(g(a), g(b))"
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
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, functionalOfA)]
                }
                (mkElemVar Mock.x)
                functionalOfA
        )
    , testCase "equals(functional, x) becomes a substitution"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, functionalOfA)]
                }
                functionalOfA
                (mkElemVar Mock.x)
        )
    , testCase "equals(x, function) becomes a substitution + ceil"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                }
            (mkElemVar Mock.x)
            fOfA
        )
    , testCase "equals(function, x) becomes a substitution + ceil"
        (assertTermEquals
            Conditional
                { term = ()
                , predicate = makeCeilPredicate fOfA
                , substitution =
                    Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                }
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
        [ testCase "concrete Map, same keys"
            (assertTermEquals
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                    }
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            )
        , testCase "concrete Map, different keys"
            (assertTermEquals
                Predicate.bottomPredicate
                (Mock.builtinMap [(Mock.a, Mock.b)])
                (Mock.builtinMap [(Mock.b, mkElemVar Mock.x)])
            )
        , testCase "concrete Map with framed Map"
            (assertTermEquals
                Conditional
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
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    (mkElemVar Mock.m)
                )
            )
        , testCase "concrete Map with framed Map"
            (assertTermEquals
                Conditional
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
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                (Mock.concatMap
                    (mkElemVar Mock.m)
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                )
            )
        , testCase "framed Map with concrete Map"
            (assertTermEquals
                Conditional
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
                (Mock.concatMap
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    (mkElemVar Mock.m)
                )
                (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            )
        , testCase "framed Map with concrete Map"
            (assertTermEquals
                Conditional
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
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        term1
                        term1
                    )
        ,
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                unified34 = Predicate.bottomPredicate
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
                    (assertTermEquals
                        (Predicate.fromSingleSubstitution
                            (ElemVar x, Mock.builtinList [Mock.b])
                        )
                        term5
                        term6
                    )
        ,
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
            in
                testCase "different lengths"
                    (assertTermEquals
                        Predicate.bottomPredicate
                        term7
                        term8
                    )
        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set equality.
    ]

assertTermEquals
    :: HasCallStack
    => Predicate Variable
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEquals = assertTermEqualsGeneric

assertTermEqualsGeneric
    :: HasCallStack
    => Predicate Variable
    -> TermLike Variable
    -> TermLike Variable
    -> Assertion
assertTermEqualsGeneric expectPure =
    assertTermEqualsMultiGeneric [expectPure]


assertTermEqualsMulti
    :: HasCallStack
    => [Predicate Variable]
    -> TermLike Variable
    -> TermLike Variable
    -> IO ()
assertTermEqualsMulti = assertTermEqualsMultiGeneric

assertTermEqualsMultiGeneric
    :: HasCallStack
    => [Predicate Variable]
    -> TermLike Variable
    -> TermLike Variable
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
    termToPattern :: TermLike Variable -> Pattern Variable
    termToPattern (Bottom_ _) =
        Conditional.bottom
    termToPattern term =
        Conditional
            { term = term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    predSubstToPattern :: Predicate Variable -> Pattern Variable
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
    runSimplifier mockEnv . simplify Predicate.top
  where
    mockEnv = Mock.env

evaluate
    :: Pattern Variable
    -> Pattern Variable
    -> IO (OrPattern Variable)
evaluate first second =
    runSimplifier mockEnv
    $ makeEvaluate first second Predicate.top
  where
    mockEnv = Mock.env

evaluateTermsGeneric
    :: TermLike Variable
    -> TermLike Variable
    -> IO (OrPredicate Variable)
evaluateTermsGeneric first second =
    runSimplifier mockEnv
    $ makeEvaluateTermsToPredicate first second Predicate.top
  where
    mockEnv = Mock.env
