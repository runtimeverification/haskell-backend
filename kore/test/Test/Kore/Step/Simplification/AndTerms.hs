{-# LANGUAGE Strict #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Step.Simplification.AndTerms
    ( test_andTermsSimplification
    , test_equalsTermsSimplification
    , test_functionAnd
    , test_Defined
    ) where

import Prelude.Kore

import Test.Tasty

import Control.Error
    ( MaybeT (..)
    )
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromJust
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )

import qualified Kore.Builtin.AssociativeCommutative as Ac
import Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toRepresentation
    , top
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.And
    ( termAnd
    )
import Kore.Step.Simplification.AndTerms
    ( functionAnd
    , termUnification
    )
import Kore.Step.Simplification.Equals
    ( termEquals
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Sentence
    ( SentenceAlias
    )
import qualified Kore.Unification.UnifierT as Monad.Unify

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification =
    [ testGroup "Predicates"
        [ testCase "\\and{s}(f{}(a), \\top{s}())" $ do
            let expected = Pattern.fromTermLike fOfA
            actual <- simplifyUnify fOfA mkTop_
            assertEqual "" ([expected], [expected]) actual

        , testCase "\\and{s}(\\top{s}(), f{}(a))" $ do
            let expected = Pattern.fromTermLike fOfA
            actual <- simplifyUnify mkTop_ fOfA
            assertEqual "" ([expected], [expected]) actual

        , testCase "\\and{s}(f{}(a), \\bottom{s}())" $ do
            let expect =
                    ( [Pattern.bottom]
                    , [Pattern.bottom]
                    )
            actual <- simplifyUnify fOfA mkBottom_
            assertEqual "" expect actual

        , testCase "\\and{s}(\\bottom{s}(), f{}(a))" $ do
            let expect =
                    ( [Pattern.bottom]
                    , [Pattern.bottom]
                    )
            actual <- simplifyUnify mkBottom_ fOfA
            assertEqual "" expect actual
        ]

    , testCase "equal patterns and" $ do
        let expect = Pattern.fromTermLike fOfA
        actual <- simplifyUnify fOfA fOfA
        assertEqual "" ([expect], [expect]) actual

    , testGroup "variable function and"
        [ testCase "\\and{s}(x:s, f{}(a))" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.x, fOfA)]
                        }
            actual <- simplifyUnify (mkElemVar Mock.x) fOfA
            assertEqual "" ([expect], [expect]) actual

        , testCase "\\and{s}(f{}(a), x:s)" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.x, fOfA)]
                        }
            actual <- simplifyUnify fOfA (mkElemVar Mock.x)
            assertEqual "" ([expect], [expect]) actual
        ]

    , testGroup "injective head and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate = makeEqualsPredicate
                            fOfA
                            gOfA
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA) (Mock.injective10 gOfA)
            assertEqual "" ([expect], [expect]) actual
        , testCase "same head, same child" $ do
            let expected = Pattern.fromTermLike (Mock.injective10 fOfA)
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA) (Mock.injective10 fOfA)
            assertEqual "" ([expected], [expected]) actual
        , testCase "different head" $ do
            let expect =
                    (   [ Pattern.fromTermLike
                            (mkAnd
                                (Mock.injective10 fOfA)
                                (Mock.injective11 gOfA)
                            )
                        ]
                    ,   [ Pattern.fromTermLike
                            (mkAnd
                                (Mock.injective10 fOfA)
                                (Mock.injective11 gOfA)
                            )
                        ]
                    )
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA) (Mock.injective11 gOfA)
            assertEqual "" expect actual
        ]

    , testGroup "sort injection and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.sortInjection10 Mock.cfSort0
                        , predicate = makeEqualsPredicate
                            Mock.cfSort0
                            Mock.cgSort0
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cgSort0)
            assertEqual "" ([expect], [expect]) actual
        , testCase "same head, same child" $ do
            let expect =
                    Pattern.fromTermLike (Mock.sortInjection10 Mock.cfSort0)
            actual <-
                simplifyUnify
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cfSort0)
            assertEqual "" ([expect], [expect]) actual
        , testCase "different head, not subsort" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
            assertEqual "" expect actual
        , testCase "different head, simplifiable subsort" $ do
            let sub = Mock.sortInjection Mock.topSort Mock.plain00Subsort
                other = Mock.sortInjection Mock.topSort Mock.plain00OtherSort
                expect =
                    ( [Pattern.fromTermLike $ mkAnd sub other]
                    , [Pattern.fromTermLike $ mkAnd sub other]
                    )
            actual <- simplifyUnify sub other
            assertEqual "" expect actual
        , testCase "different head, subsort first" $ do
            let expect =
                    (   [ Pattern.fromTermLike
                            (Mock.sortInjectionSubToTop
                                (mkAnd
                                    (Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                    Mock.plain00Subsort
                                )
                            )
                        ]
                    ,   [ Pattern.fromTermLike
                            (Mock.sortInjectionSubToTop
                                (mkAnd
                                    (Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                    Mock.plain00Subsort
                                )
                            )
                        ]
                    )
            actual <-
                simplifyUnifySorts
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
            assertEqual "" expect actual
        , testCase "different head, subsort second" $ do
            let expect =
                    (   [ Pattern.fromTermLike
                            (Mock.sortInjectionSubToTop
                                (mkAnd
                                    Mock.plain00Subsort
                                    (Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                )
                            )
                        ]
                    ,   [ Pattern.fromTermLike
                            (Mock.sortInjectionSubToTop
                                (mkAnd
                                    Mock.plain00Subsort
                                    (Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                )
                            )
                        ]
                    )
            actual <-
                simplifyUnifySorts
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors not subsort" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.sortInjection10 Mock.aSort0)
                    (Mock.sortInjection11 Mock.aSort1)
            assertEqual "" expect actual
        , testCase "different head constructors subsort" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors common subsort" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors common subsort reversed" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqual "" expect actual
        ]

    , testGroup "Overloading"
        [ testCase "direct overload, left side" $ do
            let expect =
                    Conditional
                        { term = Mock.topOverload
                            (Mock.sortInjectionOtherToTop
                               Mock.aOtherSort
                            )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.topOverload
                       (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
                    (Mock.sortInjectionOtherToTop
                       (Mock.otherOverload Mock.aOtherSort)
                    )
            assertEqual "" ([expect], [expect]) actual
        , testCase "direct overload, right side" $ do
            let expect =
                    Conditional
                        { term = Mock.topOverload
                            (Mock.sortInjectionOtherToTop
                               Mock.aOtherSort
                            )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop
                       (Mock.otherOverload Mock.aOtherSort)
                    )
                    (Mock.topOverload
                       (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
            assertEqual "" ([expect], [expect]) actual
        , testCase "overload, both sides" $ do
            let expect =
                    Conditional
                        { term = Mock.topOverload
                            (Mock.sortInjectionSubSubToTop
                                Mock.aSubSubsort
                            )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop
                       (Mock.otherOverload
                           (Mock.sortInjectionSubSubToOther
                               Mock.aSubSubsort
                           )
                       )
                    )
                    (Mock.sortInjectionSubToTop
                       (Mock.subOverload
                           (Mock.sortInjectionSubSubToSub
                               Mock.aSubSubsort
                           )
                       )
                    )
            assertEqual "" ([expect], [expect]) actual
        ]
    , testGroup "Overloading -> bottom"
        [ testCase "direct overload, left side" $ do
            actual <-
                simplifyUnify
                    (Mock.topOverload
                       (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqual "" ([], []) actual
        , testCase "direct overload, right side" $ do
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.topOverload
                       (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
            assertEqual "" ([], []) actual
        , testCase "overload, both sides" $ do
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToOtherTop
                       (Mock.otherOverload
                           (Mock.sortInjectionSubSubToOther
                               Mock.aSubSubsort
                           )
                       )
                    )
                    (Mock.sortInjectionSubToOtherTop
                       (Mock.subOverload
                           (Mock.sortInjectionSubSubToSub
                               Mock.aSubSubsort
                           )
                       )
                    )
            assertEqual "" ([], []) actual
        , testCase "injected overload vs. injected domain value, common join"
          $ do
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop
                       (Mock.otherOverload
                           (Mock.sortInjectionSubSubToOther
                               Mock.aSubSubsort
                           )
                       )
                    )
                    (Mock.sortInjectionSubOtherToTop
                       subOtherDomainValue
                    )
            assertEqual "" ([], []) actual
        , testCase "injected overload vs. injected domain value, no common join"
          $ do
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToOtherTop
                       (Mock.otherOverload
                           (Mock.sortInjectionSubSubToOther
                               Mock.aSubSubsort
                           )
                       )
                    )
                    (Mock.sortInjectionSubToOtherTop
                       subDomainValue
                    )
            assertEqual "" ([], []) actual
        ]
    , testGroup "constructor and"
        [ testCase "same head" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = Mock.constr10 Mock.cf
                            , predicate = makeEqualsPredicate
                                Mock.cf
                                Mock.cg
                            , substitution = mempty
                            }
                    in ([expected], [expected])
            actual <-
                simplifyUnify
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cg)
            assertEqual "" expect actual

        , testCase "same head same child" $ do
            let expect =
                    let
                        expected = Pattern.fromTermLike (Mock.constr10 Mock.cf)
                    in ([expected], [expected])
            actual <-
                simplifyUnify
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cf)
            assertEqual "" expect actual

        , testCase "different head" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (Mock.constr10 Mock.cf)
                    (Mock.constr11 Mock.cf)
            assertEqual "" expect actual
        ]

    , testCase "constructor-sortinjection and" $ do
        let expect = ([], [])
        actual <-
            simplifyUnify
                (Mock.constr10 Mock.cf)
                (Mock.sortInjection11 Mock.cfSort1)
        assertEqual "" expect actual

    , testGroup "domain value and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Pattern.fromTermLike aDomainValue
                    in ([expected], [expected])
            actual <- simplifyUnify aDomainValue aDomainValue
            assertEqual "" expect actual

        , testCase "different values" $ do
            let expect = ([], [])
            actual <- simplifyUnify aDomainValue bDomainValue
            assertEqual "" expect actual
        ]

    , testGroup "string literal and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Pattern.fromTermLike (mkStringLiteral "a")
                    in ([expected], [expected])
            actual <-
                simplifyUnify
                    (mkStringLiteral "a")
                    (mkStringLiteral "a")
            assertEqual "" expect actual

        , testCase "different values" $ do
            let expect = ([], [])
            actual <-
                simplifyUnify
                    (mkStringLiteral "a")
                    (mkStringLiteral "b")
            assertEqual "" expect actual
        ]

    , testGroup "function and"
        [ testCase "equal values" $ do
            let expect =
                    let expanded = Pattern.fromTermLike fOfA
                    in ([expanded], [expanded])
            actual <- simplifyUnify fOfA fOfA
            assertEqual "" expect actual

        , testCase "not equal values" $ do
            let expect =
                    makeEqualsPredicate fOfA gOfA
                    & Condition.fromPredicate
                    & Pattern.withCondition fOfA
            (actualAnd, actualUnify) <- simplifyUnify fOfA gOfA
            assertEqual "" [expect] actualAnd
            assertEqual "" [expect] actualUnify
        ]

    , testGroup "unhandled cases"
        [ testCase "top level" $ do
            let expect =
                    ( [ Pattern.fromTermLike (mkAnd plain0OfA plain1OfA) ]
                    , [ Pattern.fromTermLike (mkAnd plain0OfA plain1OfA) ]
                    )
            actual <- simplifyUnify plain0OfA plain1OfA
            assertEqual "" expect actual

        , testCase "one level deep" $ do
            let expect =
                    (   [ Pattern.fromTermLike
                            (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                        ]
                    ,   [ Pattern.fromTermLike
                            (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                        ]
                    )
            actual <-
                simplifyUnify
                    (Mock.constr10 plain0OfA) (Mock.constr10 plain1OfA)
            assertEqual "" expect actual

        , testCase "two levels deep" $ do
            let expect =
                    (   [ Pattern.fromTermLike
                            (Mock.constr10
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            )
                        ]
                    ,   [ Pattern.fromTermLike
                            (Mock.constr10
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            )
                        ]
                    )
            actual <-
                simplifyUnify
                    (Mock.constr10 (Mock.constr10 plain0OfA))
                    (Mock.constr10 (Mock.constr10 plain1OfA))
            assertEqual "" expect actual
        ]

    , testCase "binary constructor of non-specialcased values" $ do
        let expect =
                (   [ Pattern.fromTermLike
                        (Mock.functionalConstr20
                            (mkAnd plain0OfA plain1OfA)
                            (mkAnd plain0OfB plain1OfB)
                        )
                    ]
                ,   [ Pattern.fromTermLike
                        (Mock.functionalConstr20
                            (mkAnd plain0OfA plain1OfA)
                            (mkAnd plain0OfB plain1OfB)
                        )
                    ]
                )
        actual <-
            simplifyUnify
                (Mock.functionalConstr20 plain0OfA plain0OfB)
                (Mock.functionalConstr20 plain1OfA plain1OfB)
        assertEqual "" expect actual

    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, Mock.b)])
                        (Condition.assign (inject Mock.x) Mock.b)
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            assertEqual "" expect actual

        , testCase "concrete Map, different keys" $ do
            let expect =  []
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.b, mkElemVar Mock.x)])
            assertEqual "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        (mconcat
                            [ Condition.assign (inject Mock.x) fOfA
                            , Condition.assign (inject Mock.m)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                        (mkElemVar Mock.m)
                    )
            assertEqual "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        (mconcat
                            [ Condition.assign (inject Mock.x) fOfA
                            , Condition.assign (inject Mock.m)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    (Mock.concatMap
                        (mkElemVar Mock.m)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    )
            assertEqual "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA) , (Mock.b, fOfB)])
                        (mconcat
                            [ Condition.assign (inject Mock.x) fOfA
                            , Condition.assign (inject Mock.m)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                        (mkElemVar Mock.m)
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        (mconcat
                            [ Condition.assign (inject Mock.x) fOfA
                            , Condition.assign (inject Mock.m)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.concatMap
                        (mkElemVar Mock.m)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual

        , testCase "concrete Map with element+unit" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA)])
                        (mconcat
                            [ Condition.assign (inject Mock.x) Mock.a
                            , Condition.assign (inject Mock.y) fOfA
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [ (Mock.a, fOfA) ])
                    (Mock.concatMap
                        (Mock.elementMap (mkElemVar Mock.x) (mkElemVar Mock.y))
                        Mock.unitMap
                    )
            assertEqual "" expect actual
        , testCase "map elem key inj splitting" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinMap
                            [   ( Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        )
                        (mconcat
                            [ Condition.assign (inject Mock.xSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.y) fOfA
                            ]
                        )
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        , fOfA
                        )
                    ]
                )
                (Mock.elementMap
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    (mkElemVar Mock.y)
                )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let
                key = Mock.a
                value = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMap = Mock.builtinMap [(key, value)]
                valueInj = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMapInj = Mock.builtinMap [(key, valueInj)]
                expected =
                    [ Pattern.withCondition
                        testMapInj
                        (mconcat
                            [ Condition.assign (inject Mock.xSubSort)
                                ( Mock.sortInjection
                                    Mock.subSort
                                    Mock.aSubSubsort
                                )
                            , Condition.assign (inject Mock.y) Mock.a
                            ]
                        )
                    ]
            actual <- unify
                testMap
                (Mock.elementMap
                    (mkElemVar Mock.y)
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                )
            assertEqual "" expected actual
        , testCase "map concat key inj splitting" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinMap
                            [   ( Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        )
                        (mconcat
                            [ Condition.assign (inject Mock.xSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.y) fOfA
                            , Condition.assign (inject Mock.m)
                                (Mock.builtinMap [])
                            ]
                        )
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        , fOfA
                        )
                    ]
                )
                (Mock.concatMap
                    (Mock.elementMap
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                        (mkElemVar Mock.y)
                    )
                    (mkElemVar Mock.m)
                )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinMap
                            [   ( Mock.a
                                , Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                )
                            ]
                        )
                        (mconcat
                            [ Condition.assign (inject Mock.xSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.y) Mock.a
                            , Condition.assign (inject Mock.m) (Mock.builtinMap [])
                            ]
                        )
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.a
                        , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        )
                    ]
                )
                (Mock.concatMap
                    (Mock.elementMap
                        (mkElemVar Mock.y)
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    )
                    (mkElemVar Mock.m)
                )
            assertEqual "" expected actual
        , testCase "unifies functions in keys" $ do
            let concrete = Mock.builtinMap [(Mock.a       , Mock.a)]
                symbolic = Mock.builtinMap [(Mock.f Mock.b, Mock.a)]
                expect =
                    makeEqualsPredicate Mock.a (Mock.f Mock.b)
                    & Condition.fromPredicate
                    & Pattern.withCondition concrete
            actual <- simplifyUnify concrete symbolic
            assertEqual "" ([expect], [expect]) actual
        ]

    , testGroup "builtin List domain"
        [ testCase "[same head, same head]" $ do
            let term1 =
                    Mock.builtinList
                        [ Mock.constr10 Mock.cf
                        , Mock.constr11 Mock.cf
                        ]
                expect = [ Pattern.fromTermLike term1 ]
            actual <- unify term1 term1
            assertEqual "" expect actual

        , testCase "[same head, different head]" $ do
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                expect = []
            actual <- unify term3 term4
            assertEqual "" expect actual

        , testCase "[a] `concat` x /\\ [a, b] " $ do
            let x = mkElementVariable "x" Mock.listSort
                term5 =
                    Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
                expect =
                    [ Conditional
                        { term = Mock.builtinList [Mock.a, Mock.b]
                        -- TODO: This predicate should have `listSort`;
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(inject x, Mock.builtinList [Mock.b])]
                        }
                    ]
            actual <- unify term5 term6
            assertEqual "" expect actual

        , testCase "different lengths" $ do
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
                expect = [Pattern.bottom]
            actual <- unify term7 term8
            assertEqual "" expect actual

        , testCase "fallback for external List symbols" $ do
            let expectTerm = mkAnd rhs lhs
                expect =
                    Pattern.fromTermLike expectTerm
                    `Conditional.andPredicate`
                        makeCeilPredicate expectTerm
                x = mkElemVar $ mkElementVariable "x" Mock.testSort
                l = mkElemVar $ mkElementVariable "y" Mock.listSort
                -- List unification does not fully succeed because the
                -- elementList symbol is not simplified to a builtin structure.
                lhs = Mock.concatList (Mock.elementList x) l
                rhs = Mock.builtinList [Mock.a, Mock.b]
            actual <- unify lhs rhs
            assertEqual "" [expect] actual

        , testCase "[a] `concat` unit /\\ x " $ do
            let x = mkElementVariable "x" Mock.listSort
                term9 = Mock.builtinList [Mock.a]
                term10 = Mock.concatList Mock.unitList (mkElemVar x)
                term11 = Mock.concatList (mkElemVar x) Mock.unitList
                expect =
                    [ Conditional
                        { term = Mock.builtinList [Mock.a]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(inject x, Mock.builtinList [Mock.a])]
                        }
                    ]

            actual1 <- unify term9 term10
            assertEqual "" expect actual1

            actual2 <- unify term10 term9
            assertEqual "" expect actual2

            actual3 <- unify term9 term11
            assertEqual "" expect actual3

            actual4 <- unify term11 term9
            assertEqual "" expect actual4

        -- TODO: Add tests with non-trivial unifications and predicates.
        ]

    , testGroup "Builtin Set domain"
        [ testCase "set singleton + unit" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinSet [Mock.a])
                        (Condition.assign (inject Mock.x) Mock.a)
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    Mock.unitSet
                )
                (Mock.builtinSet [Mock.a])
            assertEqual "" expected actual
        ,  testCase "handles set ambiguity" $ do
            let
                expected1 =
                    Pattern.withCondition
                        (Mock.builtinSet [Mock.a, Mock.b])
                        (foldMap (uncurry Condition.assign)
                            [ (inject Mock.x, Mock.a)
                            , (inject Mock.xSet, Mock.builtinSet [Mock.b])
                            ]
                        )
                expected2 =
                    Pattern.withCondition
                        (Mock.builtinSet [Mock.a, Mock.b])
                        (foldMap (uncurry Condition.assign)
                            [ (inject Mock.x, Mock.b)
                            , (inject Mock.xSet, Mock.builtinSet [Mock.a])
                            ]
                        )
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    (mkElemVar Mock.xSet)
                )
                (Mock.builtinSet [Mock.a, Mock.b])
            assertEqual "" [expected1, expected2] actual
        , testCase "set elem inj splitting" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinSet
                            [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                        )
                        (Condition.assign (inject Mock.xSubSort)
                            (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                        )
                    ]
            actual <- unify
                (Mock.elementSet
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                )
                (Mock.builtinSet
                    [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                )
            assertEqual "" expected actual
        , testCase "set concat inj splitting" $ do
            let
                expected =
                    [ Pattern.withCondition
                        (Mock.builtinSet
                            [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                        )
                        (foldMap (uncurry Condition.assign)
                            [   ( inject Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   ( inject Mock.xSet
                                , Mock.builtinSet []
                                )
                            ]
                        )
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    )
                    (mkElemVar Mock.xSet)
                )
                (Mock.builtinSet
                    [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                )
            assertEqual "" expected actual
        , testCase "set concat 2 inj splitting" $ do
            let
                testSet =
                    Mock.builtinSet
                        [ Mock.a
                        , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        ]
                expected =
                    [ Pattern.withCondition testSet
                        (foldMap (uncurry Condition.assign)
                            [   (inject Mock.x, Mock.a)
                            ,   ( inject Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   (inject Mock.xSet, Mock.builtinSet [])
                            ]
                        )
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    (Mock.concatSet
                        (Mock.elementSet
                            (Mock.sortInjection
                                Mock.testSort
                                (mkElemVar Mock.xSubSort)
                            )
                        )
                        (mkElemVar Mock.xSet)
                    )
                )
                testSet
            assertEqual "" expected actual
        ]
    , testGroup "alias expansion"
        [ testCase "alias() vs top" $ do
            let
                x = mkVariable "x"
                alias = mkAlias' "alias1" x mkTop_
                left = applyAlias' alias $ mkTop Mock.testSort
            actual <- simplifyUnify left mkTop_
            assertExpectTop actual
        , testCase "alias1() vs alias2()" $ do
            let
                x = mkVariable "x"
                leftAlias = mkAlias' "leftAlias" x mkTop_
                left = applyAlias' leftAlias $ mkTop Mock.testSort
                rightAlias = mkAlias' "rightAlias" x mkTop_
                right = applyAlias' rightAlias $ mkTop Mock.testSort
            actual <- simplifyUnify left right
            assertExpectTop actual
        , testCase "alias1(alias2()) vs top" $ do
            let
                x = mkVariable "x"
                y = mkVariable "y"
                alias1 = mkAlias' "alias1" x mkTop_
                alias1App =
                    applyAlias' alias1
                    $ mkSetVar (SetVariableName <$> y)
                alias2 = mkAlias' "alias2" x alias1App
                alias2App = applyAlias' alias2 $ mkTop Mock.testSort
            actual <- simplifyUnify alias2App mkTop_
            assertExpectTop actual
        , testCase "alias1() vs injHead" $ do
            let
                expect =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate =
                            makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
                x = mkVariable "x"
                alias = mkAlias' "alias1" x $ Mock.injective10 fOfA
                left = applyAlias' alias $ mkTop Mock.testSort
            actual <- simplifyUnify left $ Mock.injective10 gOfA
            assertEqual "" ([expect], [expect]) actual
        , testGroup "unhandled cases with aliases"
            [ testCase "top level" $ do
                let
                    expect =
                        ( [ Pattern.fromTermLike (mkAnd left plain1OfA) ]
                        , [ Pattern.fromTermLike (mkAnd left plain1OfA) ]
                        )
                    x = mkVariable "x"
                    alias = mkAlias' "alias1" x plain0OfA
                    left = applyAlias' alias $ mkTop Mock.testSort
                actual <- simplifyUnify left plain1OfA
                assertEqual "" expect actual

            , testCase "one level deep" $ do
                let
                    expect =
                        (   [ Pattern.fromTermLike
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            ]
                        ,   [ Pattern.fromTermLike
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            ]
                        )
                    x = mkVariable "x"
                    alias = mkAlias' "alias1" x $ Mock.constr10 plain0OfA
                    left = applyAlias' alias $ mkTop Mock.testSort
                actual <- simplifyUnify left $ Mock.constr10 plain1OfA
                assertEqual "" expect actual
            ]
        ]

    , testGroup "internal Int values"
        [ testCase "distinct values" $ do
            let expect = []
                input1 = Mock.builtinInt 1
                input2 = Mock.builtinInt 2
            actual <- unify input1 input2
            assertEqual "Expected \\bottom" expect actual
        , testCase "identical values" $ do
            let expect = [Pattern.fromTermLike input1]
                input1 = Mock.builtinInt 1
                input2 = Mock.builtinInt 1
            actual <- unify input1 input2
            assertEqual "" expect actual
        ]

    , testGroup "internal Bool values"
        [ testCase "distinct values" $ do
            let expect = []
                input1 = Mock.builtinBool True
                input2 = Mock.builtinBool False
            actual <- unify input1 input2
            assertEqual "Expected \\bottom" expect actual
        , testCase "identical values" $ do
            let expect = [Pattern.fromTermLike input1]
                input1 = Mock.builtinBool True
                input2 = Mock.builtinBool True
            actual <- unify input1 input2
            assertEqual "" expect actual
        ]

    , testGroup "internal String values"
        [ testCase "distinct values" $ do
            let expect = []
                input1 = Mock.builtinString "a"
                input2 = Mock.builtinString "b"
            actual <- unify input1 input2
            assertEqual "Expected \\bottom" expect actual
        , testCase "identical values" $ do
            let expect = [Pattern.fromTermLike input1]
                input1 = Mock.builtinString "a"
                input2 = Mock.builtinString "a"
            actual <- unify input1 input2
            assertEqual "" expect actual
        ]

    , testGroup "KEquals"
        [ testCase "Equal unification" $ do
            let input1 = Mock.keqBool (cf xVar) a
                input2 = Mock.builtinBool False
                expected = [Condition.top]
            Just actual <- simplifyEquals mempty input1 input2
            assertEqual "" expected actual
        , testCase "And unification" $ do
            let input1 = Mock.keqBool (cf xVar) a
                input2 = Mock.builtinBool False
                expected = [Pattern.top]
            actual <- simplify input1 input2
            assertEqual "" expected actual
        , testCase "And unification fails if pattern\
                    \ is not function-like" $ do
            let input1 = Mock.keqBool (TermLike.mkOr a (cf xVar)) b
                input2 = Mock.builtinBool False
                expected =
                    TermLike.mkAnd input1 input2
                    & Pattern.fromTermLike
                    & pure
            actual <- simplify input1 input2
            assertEqual "" expected actual
        , testCase "Equal unification fails if pattern\
                    \ is not function-like" $ do
            let input1 = Mock.keqBool (TermLike.mkOr a (cf xVar)) b
                input2 = Mock.builtinBool False
            actual <- simplifyEquals mempty input1 input2
            assertEqual "" Nothing actual
        ]
    ]
  where
    xVar = mkElemVar Mock.x
    cf = Mock.functionalConstr10
    a = Mock.a
    b = Mock.b

mkVariable :: Text -> Variable VariableName
mkVariable ident =
    Variable
    { variableName = mkVariableName (testId ident)
    , variableSort = Mock.testSort
    }

mkAlias'
    :: Text
    -> Variable VariableName
    -> TermLike VariableName
    -> SentenceAlias (TermLike VariableName)
mkAlias' ident var inner =
    mkAlias_
        (testId ident)
        Mock.testSort
        [inject $ fmap SetVariableName var]
        inner

applyAlias'
    :: InternalVariable variable
    => SentenceAlias (TermLike VariableName)
    -> TermLike variable
    -> TermLike variable
applyAlias' alias arg = applyAlias alias [] [arg]

assertExpectTop :: ([Pattern VariableName], [Pattern VariableName]) -> IO ()
assertExpectTop =
    assertEqual "" ([Pattern.top], [Pattern.top])

test_equalsTermsSimplification :: [TestTree]
test_equalsTermsSimplification =
    [ testCase "adds ceil when producing substitutions" $ do
        let expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution =
                        Substitution.unsafeWrap [(inject Mock.x, Mock.cf)]
                    }
                ]
        actual <- simplifyEquals Map.empty (mkElemVar Mock.x) Mock.cf
        assertEqual "" expected actual

    , testCase "handles set ambiguity" $ do
        let
            asInternal :: Set.Set (TermLike Concrete) -> TermLike VariableName
            asInternal =
                Set.map (retractKey >>> fromJust)
                >>> Map.fromSet (const SetValue)
                >>> Ac.asInternalConcrete Mock.metadataTools Mock.setSort
            expected = Just $ do -- list monad
                (xValue, xSetValue) <-
                    [ (Mock.a, [Mock.b])
                    , (Mock.b, [Mock.a])
                    ]
                mconcat
                    [ Condition.assign (inject Mock.x) xValue
                    , Condition.assign (inject Mock.xSet)
                        $ asInternal $ Set.fromList xSetValue
                    ]
                    & pure
        actual <- simplifyEquals
            Map.empty
            (Mock.concatSet
                (Mock.elementSet (mkElemVar Mock.x))
                (mkElemVar Mock.xSet)
            )
            (asInternal (Set.fromList [Mock.a, Mock.b]))
        assertEqual "" expected actual
    , testGroup "builtin Map"
        [ testCase "unifies functions in keys" $ do
            let concrete = Mock.builtinMap [(Mock.a       , Mock.a)]
                symbolic = Mock.builtinMap [(Mock.f Mock.b, Mock.a)]
                expect =
                    makeEqualsPredicate Mock.a (Mock.f Mock.b)
                    & Condition.fromPredicate
            actual <- simplifyEquals mempty concrete symbolic
            assertEqual "" (Just [expect]) actual
        , testCase "no keys in empty Map" $ do
            let expect = Condition.top
            actual <-
                simplifyEquals
                    mempty
                    (Mock.builtinBool False)
                    (Mock.inKeysMap (mkElemVar Mock.x) (Mock.builtinMap []))
            assertEqual "" (Just [expect]) actual
        , testCase "key not in singleton Map" $ do
            let expect =
                    makeEqualsPredicate
                        (mkElemVar Mock.x)
                        (mkElemVar Mock.y)
                    & makeNotPredicate
                    & Condition.fromPredicate
            actual <-
                simplifyEquals
                    mempty
                    ( Mock.builtinBool False )
                    ( Mock.inKeysMap
                        ( mkElemVar Mock.x)
                        ( Mock.builtinMap
                            [ ( mkElemVar Mock.y, Mock.a ) ]
                        )
                    )
            assertEqual "" (Just [expect]) actual
        , testCase "key not in two-element Map" $ do
                let expect =
                        foldr1
                            makeAndPredicate
                            [ makeNotPredicate
                                $ makeEqualsPredicate
                                    (mkElemVar Mock.x)
                                    (mkElemVar Mock.y)
                            , makeNotPredicate
                                $ makeEqualsPredicate
                                    (mkElemVar Mock.x)
                                    (mkElemVar Mock.z)
                            -- Definedness condition
                            , makeNotPredicate
                                $ makeEqualsPredicate
                                    (mkElemVar Mock.y)
                                    (mkElemVar Mock.z)
                            ]
                        & Condition.fromPredicate
                actual <-
                    simplifyEquals
                        mempty
                        (Mock.builtinBool False)
                        ( Mock.inKeysMap
                            ( mkElemVar Mock.x )
                            ( Mock.builtinMap
                                [ ( mkElemVar Mock.y, Mock.a )
                                , ( mkElemVar Mock.z, Mock.a )
                                ]
                            )
                        )
                assertEqual "" (Just [expect]) actual
        , testCase "unevaluated function key in singleton Map" $ do
            let expect =
                    makeAndPredicate
                        ( makeNotPredicate
                            ( makeAndPredicate
                                ( makeCeilPredicate
                                    (Mock.f (mkElemVar Mock.x))
                                )
                                ( makeEqualsPredicate
                                    (mkElemVar Mock.y)
                                    ( Mock.f (mkElemVar Mock.x) )
                                )
                            )
                        )
                        ( makeCeilPredicate
                            (Mock.f (mkElemVar Mock.x))
                        )
                    & Condition.fromPredicate
            actual <-
                simplifyEquals
                    mempty
                    (Mock.builtinBool False)
                    ( Mock.inKeysMap
                        ( Mock.f (mkElemVar Mock.x) )
                        ( Mock.builtinMap
                            [ (mkElemVar Mock.y, Mock.a ) ]
                        )
                    )
            assertEqual "" (Just [expect]) actual
        ]
    ]

test_functionAnd :: [TestTree]
test_functionAnd =
    [ testCase "simplifies result" $ do
        let f = TermLike.markSimplified . Mock.f
            x = mkElemVar Mock.x
            y = mkElemVar Mock.y
            expect =
                Pattern.withCondition (f x)
                $ Condition.fromPredicate
                $ makeEqualsPredicate (f x) (f y)
        let Just actual = functionAnd (f x) (f y)
        assertEqual "" expect (Pattern.syncSort actual)
        assertBool "" (Pattern.isSimplified sideRepresentation actual)
    ]

test_Defined :: [TestTree]
test_Defined =
    [ testGroup "exact matching" $
        let partial = Mock.f Mock.a
            defined = mkDefined partial
        in
            [ testCase "\\and(partial, defined)" $ do
                -- equalAndEquals returns the first argument
                let expect = [Pattern.fromTermLike partial]
                (actualAnd, actualUnify) <- simplifyUnify partial defined
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\and(defined, partial)" $ do
                -- equalAndEquals returns the first argument
                let expect = [Pattern.fromTermLike defined]
                (actualAnd, actualUnify) <- simplifyUnify defined partial
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\equals(partial, defined)" $ do
                let expect = Just [Condition.top]
                actual <- simplifyEquals mempty partial defined
                assertEqual "" expect actual
            , testCase "\\equals(defined, partial)" $ do
                let expect = Just [Condition.top]
                actual <- simplifyEquals mempty defined partial
                assertEqual "" expect actual
            ]
    , testGroup "variable with function" $
        let defined = mkDefined (Mock.f Mock.a)
            variable = mkElemVar Mock.x
            condition =
                Condition.assign (inject Mock.x) defined
        in
            [ testCase "\\and" $ do
                let expect = [Pattern.withCondition defined condition]
                (actualAnd, actualUnify) <- simplifyUnify defined variable
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\equals" $ do
                let expect = Just [condition]
                actual <- simplifyEquals mempty defined variable
                assertEqual "" expect actual
            ]
    , testGroup "functions" $
        let function1 = Mock.f Mock.a
            function2 = Mock.g Mock.b
            defined1 = mkDefined function1
            -- TODO (thomas.tuegel): condition should use defined1 instead of
            -- function1.
            condition =
                makeEqualsPredicate function1 function2
                & Condition.fromPredicate
        in
            [ testCase "\\and" $ do
                let expect = [Pattern.withCondition function1 condition]
                (actualAnd, actualUnify) <- simplifyUnify defined1 function2
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\equals" $ do
                let expect = Just [condition]
                actual <- simplifyEquals mempty defined1 function2
                assertEqual "" expect actual
            ]
    , testGroup "Sets" $
        let fx = Mock.f (mkElemVar Mock.x)
            fy = Mock.f (mkElemVar Mock.y)
            set1 = Mock.builtinSet [fx, fy]
            set2 = Mock.builtinSet [mkElemVar Mock.t, mkElemVar Mock.u]
            defined1 = mkDefined set1
            conditions =
                [ mconcat
                    [ Condition.assign (inject Mock.t) (mkDefined fx)
                    , Condition.assign (inject Mock.u) (mkDefined fy)
                    ]
                , mconcat
                    [ Condition.assign (inject Mock.t) (mkDefined fy)
                    , Condition.assign (inject Mock.u) (mkDefined fx)
                    ]
                ]
        in
            [ testCase "\\and(defined, _)" $ do
                let expect = Pattern.withCondition defined1 <$> conditions
                (actualAnd, actualUnify) <- simplifyUnify defined1 set2
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\and(_, defined)" $ do
                let expect = Pattern.withCondition defined1 <$> conditions
                (actualAnd, actualUnify) <- simplifyUnify set2 defined1
                assertEqual "" expect actualAnd
                assertEqual "" expect actualUnify
            , testCase "\\equals(defined, _)" $ do
                let expect = Just conditions
                actual <- simplifyEquals mempty defined1 set2
                assertEqual "" expect actual
            , testCase "\\equals(_, defined)" $ do
                let expect = Just conditions
                actual <- simplifyEquals mempty set2 defined1
                assertEqual "" expect actual
            ]
    , testGroup "Maps" $
        let map1 =
                Mock.builtinMap
                    [ (mkElemVar Mock.x, fOfA)
                    , (mkElemVar Mock.y, fOfB)
                    ]
            map2 =
                Mock.framedMap
                    [(mkElemVar Mock.t, mkElemVar Mock.u)]
                    [mkElemVar Mock.m]
            defined1 = mkDefined map1
            conditions =
                [ mconcat
                    [ Condition.assign (inject Mock.t) (mkElemVar Mock.x)
                    , Condition.assign (inject Mock.u) (mkDefined fOfA)
                    , Condition.assign (inject Mock.m)
                        (Mock.builtinMap [(mkElemVar Mock.y, mkDefined fOfB)])
                    ]
                , mconcat
                    [ Condition.assign (inject Mock.t) (mkElemVar Mock.y)
                    , Condition.assign (inject Mock.u) (mkDefined fOfB)
                    , Condition.assign (inject Mock.m)
                        (Mock.builtinMap [(mkElemVar Mock.x, mkDefined fOfA)])
                    ]
                ]
        in
            [ testCase "\\and(defined, _)" $ do
                let expect = Pattern.withCondition defined1 <$> conditions
                (actualAnd, actualUnify) <- simplifyUnify defined1 map2
                assertEqual "" (List.sort expect) (List.sort actualAnd)
                assertEqual "" (List.sort expect) (List.sort actualUnify)
            , testCase "\\and(_, defined)" $ do
                let expect = Pattern.withCondition defined1 <$> conditions
                (actualAnd, actualUnify) <- simplifyUnify map2 defined1
                assertEqual "" (List.sort expect) (List.sort actualAnd)
                assertEqual "" (List.sort expect) (List.sort actualUnify)
            , testCase "\\equals(defined, _)" $ do
                let expect = Just conditions
                actual <- simplifyEquals mempty defined1 map2
                assertEqual "" (List.sort <$> expect) actual
            , testCase "\\equals(_, defined)" $ do
                let expect = Just conditions
                actual <- simplifyEquals mempty map2 defined1
                assertEqual "" (List.sort <$> expect) actual
            ]
    ]

fOfA :: TermLike VariableName
fOfA = Mock.f Mock.a

fOfB :: TermLike VariableName
fOfB = Mock.f Mock.b

gOfA :: TermLike VariableName
gOfA = Mock.g Mock.a

plain0OfA :: TermLike VariableName
plain0OfA = Mock.plain10 Mock.a

plain1OfA :: TermLike VariableName
plain1OfA = Mock.plain11 Mock.a

plain0OfB :: TermLike VariableName
plain0OfB = Mock.plain10 Mock.b

plain1OfB :: TermLike VariableName
plain1OfB = Mock.plain11 Mock.b

aDomainValue :: TermLike VariableName
aDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "a"
        }

subDomainValue :: TermLike VariableName
subDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.subSort
        , domainValueChild = mkStringLiteral "a"
        }

subOtherDomainValue :: TermLike VariableName
subOtherDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.subOthersort
        , domainValueChild = mkStringLiteral "a"
        }

bDomainValue :: TermLike VariableName
bDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "b"
        }

simplifyUnifySorts
    :: TermLike VariableName
    -> TermLike VariableName
    -> IO ([Pattern VariableName], [Pattern VariableName])
simplifyUnifySorts first second = do
    (simplified, unified) <-
        simplifyUnify (simplifiedTerm first) (simplifiedTerm second)
    return (map Pattern.syncSort simplified, Pattern.syncSort <$> unified)

simplifyUnify
    :: TermLike VariableName
    -> TermLike VariableName
    -> IO ([Pattern VariableName], [Pattern VariableName])
simplifyUnify first second =
    (,)
        <$> simplify (simplifiedTerm first) (simplifiedTerm second)
        <*> unify (simplifiedTerm first) (simplifiedTerm second)

unify
    :: TermLike VariableName
    -> TermLike VariableName
    -> IO [Pattern VariableName]
unify first second =
    runSimplifier mockEnv unification
  where
    mockEnv = Mock.env
    unification =
        Monad.Unify.runUnifierT Not.notSimplifier
        $ termUnification
            Not.notSimplifier
            (simplifiedTerm first)
            (simplifiedTerm second)

simplify
    :: TermLike VariableName
    -> TermLike VariableName
    -> IO [Pattern VariableName]
simplify first second =
    runSimplifierBranch mockEnv
    $ termAnd Not.notSimplifier (simplifiedTerm first) (simplifiedTerm second)
  where
    mockEnv = Mock.env

simplifyEquals
    :: BuiltinAndAxiomSimplifierMap
    -> TermLike VariableName
    -> TermLike VariableName
    -> IO (Maybe [Condition VariableName])
simplifyEquals simplifierAxioms first second =
    (fmap . fmap) toList
    $ runSimplifier mockEnv
    $ runMaybeT $ termEquals (simplifiedTerm first) (simplifiedTerm second)
  where
    mockEnv = Mock.env { simplifierAxioms }

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
    (SideCondition.top :: SideCondition VariableName)
