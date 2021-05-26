{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Step.Simplification.AndTerms (
    test_andTermsSimplification,
    test_equalsTermsSimplification,
    test_functionAnd,
) where

import Control.Error (
    MaybeT (..),
 )
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import Data.Maybe (
    fromJust,
 )
import qualified Data.Set as Set
import Data.Text (
    Text,
 )
import qualified Kore.Builtin.AssociativeCommutative as Ac
import Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    toRepresentation,
    top,
 )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
    mkRewritingTerm,
 )
import Kore.Step.Simplification.And (
    termAnd,
 )
import Kore.Step.Simplification.AndTerms (
    functionAnd,
    matchFunctionAnd,
    termUnification,
 )
import Kore.Step.Simplification.Equals (
    termEquals,
 )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Sentence (
    SentenceAlias,
 )
import qualified Kore.Unification.UnifierT as Monad.Unify
import Prelude.Kore
import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification =
    [ testGroup
        "Predicates"
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
    , testGroup
        "variable function and"
        [ testCase "\\and{s}(x:s, f{}(a))" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.xConfig, fOfA)]
                        }
            actual <- simplifyUnify (mkElemVar Mock.xConfig) fOfA
            assertEqual "" ([expect], [expect]) actual
        , testCase "\\and{s}(f{}(a), x:s)" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.xConfig, fOfA)]
                        }
            actual <- simplifyUnify fOfA (mkElemVar Mock.xConfig)
            assertEqual "" ([expect], [expect]) actual
        ]
    , testGroup
        "injective head and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate =
                            makeEqualsPredicate
                                fOfA
                                gOfA
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA)
                    (Mock.injective10 gOfA)
            assertEqual "" ([expect], [expect]) actual
        , testCase "same head, same child" $ do
            let expected = Pattern.fromTermLike (Mock.injective10 fOfA)
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA)
                    (Mock.injective10 fOfA)
            assertEqual "" ([expected], [expected]) actual
        , testCase "different head" $ do
            let expect =
                    (
                        [ Pattern.fromTermLike
                            ( mkAnd
                                (Mock.injective10 fOfA)
                                (Mock.injective11 gOfA)
                            )
                        ]
                    ,
                        [ Pattern.fromTermLike
                            ( mkAnd
                                (Mock.injective10 fOfA)
                                (Mock.injective11 gOfA)
                            )
                        ]
                    )
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA)
                    (Mock.injective11 gOfA)
            assertEqual "" expect actual
        ]
    , testGroup
        "sort injection and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.sortInjection10 Mock.cfSort0
                        , predicate =
                            makeEqualsPredicate
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
                    (
                        [ Pattern.fromTermLike
                            ( Mock.sortInjectionSubToTop
                                ( mkAnd
                                    Mock.plain00Subsort
                                    ( Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                )
                            )
                        ]
                    ,
                        [ Pattern.fromTermLike
                            ( Mock.sortInjectionSubToTop
                                ( mkAnd
                                    Mock.plain00Subsort
                                    ( Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
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
                    (
                        [ Pattern.fromTermLike
                            ( Mock.sortInjectionSubToTop
                                ( mkAnd
                                    Mock.plain00Subsort
                                    ( Mock.sortInjectionSubSubToSub
                                        Mock.plain00SubSubsort
                                    )
                                )
                            )
                        ]
                    ,
                        [ Pattern.fromTermLike
                            ( Mock.sortInjectionSubToTop
                                ( mkAnd
                                    Mock.plain00Subsort
                                    ( Mock.sortInjectionSubSubToSub
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
    , testGroup
        "Overloading"
        [ testCase "direct overload, left side" $ do
            let expect =
                    Conditional
                        { term =
                            Mock.topOverload
                                ( Mock.sortInjectionOtherToTop
                                    Mock.aOtherSort
                                )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    ( Mock.topOverload
                        (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
                    ( Mock.sortInjectionOtherToTop
                        (Mock.otherOverload Mock.aOtherSort)
                    )
            assertEqual "" ([expect], [expect]) actual
        , testCase "direct overload, right side" $ do
            let expect =
                    Conditional
                        { term =
                            Mock.topOverload
                                ( Mock.sortInjectionOtherToTop
                                    Mock.aOtherSort
                                )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    ( Mock.sortInjectionOtherToTop
                        (Mock.otherOverload Mock.aOtherSort)
                    )
                    ( Mock.topOverload
                        (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
            assertEqual "" ([expect], [expect]) actual
        , testCase "overload, both sides" $ do
            let expect =
                    Conditional
                        { term =
                            Mock.topOverload
                                ( Mock.sortInjectionSubSubToTop
                                    Mock.aSubSubsort
                                )
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    ( Mock.sortInjectionOtherToTop
                        ( Mock.otherOverload
                            ( Mock.sortInjectionSubSubToOther
                                Mock.aSubSubsort
                            )
                        )
                    )
                    ( Mock.sortInjectionSubToTop
                        ( Mock.subOverload
                            ( Mock.sortInjectionSubSubToSub
                                Mock.aSubSubsort
                            )
                        )
                    )
            assertEqual "" ([expect], [expect]) actual
        ]
    , testGroup
        "Overloading -> bottom"
        [ testCase "direct overload, left side" $ do
            actual <-
                simplifyUnify
                    ( Mock.topOverload
                        (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqual "" ([], []) actual
        , testCase "direct overload, right side" $ do
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    ( Mock.topOverload
                        (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    )
            assertEqual "" ([], []) actual
        , testCase "overload, both sides" $ do
            actual <-
                simplifyUnify
                    ( Mock.sortInjectionOtherToOtherTop
                        ( Mock.otherOverload
                            ( Mock.sortInjectionSubSubToOther
                                Mock.aSubSubsort
                            )
                        )
                    )
                    ( Mock.sortInjectionSubToOtherTop
                        ( Mock.subOverload
                            ( Mock.sortInjectionSubSubToSub
                                Mock.aSubSubsort
                            )
                        )
                    )
            assertEqual "" ([], []) actual
        , testCase "injected overload vs. injected domain value, common join" $
            do
                actual <-
                    simplifyUnify
                        ( Mock.sortInjectionOtherToTop
                            ( Mock.otherOverload
                                ( Mock.sortInjectionSubSubToOther
                                    Mock.aSubSubsort
                                )
                            )
                        )
                        ( Mock.sortInjectionSubOtherToTop
                            subOtherDomainValue
                        )
                assertEqual "" ([], []) actual
        , testCase "injected overload vs. injected domain value, no common join" $
            do
                actual <-
                    simplifyUnify
                        ( Mock.sortInjectionOtherToOtherTop
                            ( Mock.otherOverload
                                ( Mock.sortInjectionSubSubToOther
                                    Mock.aSubSubsort
                                )
                            )
                        )
                        ( Mock.sortInjectionSubToOtherTop
                            subDomainValue
                        )
                assertEqual "" ([], []) actual
        ]
    , testGroup
        "constructor and"
        [ testCase "same head" $ do
            let expect =
                    let expected =
                            Conditional
                                { term = Mock.constr10 Mock.cf
                                , predicate =
                                    makeEqualsPredicate
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
                    let expected = Pattern.fromTermLike (Mock.constr10 Mock.cf)
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
    , testGroup
        "domain value and"
        [ testCase "equal values" $ do
            let expect =
                    let expected = Pattern.fromTermLike aDomainValue
                     in ([expected], [expected])
            actual <- simplifyUnify aDomainValue aDomainValue
            assertEqual "" expect actual
        , testCase "different values" $ do
            let expect = ([], [])
            actual <- simplifyUnify aDomainValue bDomainValue
            assertEqual "" expect actual
        ]
    , testGroup
        "string literal and"
        [ testCase "equal values" $ do
            let expect =
                    let expected = Pattern.fromTermLike (mkStringLiteral "a")
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
    , testGroup
        "function and"
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
    , testGroup
        "unhandled cases"
        [ testCase "top level" $ do
            let expect =
                    ( [Pattern.fromTermLike (mkAnd plain0OfA plain1OfA)]
                    , [Pattern.fromTermLike (mkAnd plain0OfA plain1OfA)]
                    )
            actual <- simplifyUnify plain0OfA plain1OfA
            assertEqual "" expect actual
        , testCase "one level deep" $ do
            let expect =
                    (
                        [ Pattern.fromTermLike
                            (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                        ]
                    ,
                        [ Pattern.fromTermLike
                            (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                        ]
                    )
            actual <-
                simplifyUnify
                    (Mock.constr10 plain0OfA)
                    (Mock.constr10 plain1OfA)
            assertEqual "" expect actual
        , testCase "two levels deep" $ do
            let expect =
                    (
                        [ Pattern.fromTermLike
                            ( Mock.constr10
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            )
                        ]
                    ,
                        [ Pattern.fromTermLike
                            ( Mock.constr10
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
                (
                    [ Pattern.fromTermLike
                        ( Mock.functionalConstr20
                            (mkAnd plain0OfA plain1OfA)
                            (mkAnd plain0OfB plain1OfB)
                        )
                    ]
                ,
                    [ Pattern.fromTermLike
                        ( Mock.functionalConstr20
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
    , testGroup
        "builtin Map domain"
        [ testCase "concrete Map, same keys" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, Mock.b)])
                        ( Condition.assign
                            (inject Mock.xConfig)
                            Mock.b
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
            assertEqual "" expect actual
        , testCase "concrete Map, different keys" $ do
            let expect = []
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.b, mkElemVar Mock.xConfig)])
            assertEqual "" expect actual
        , testCase "concrete Map with framed Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        ( mconcat
                            [ Condition.assign
                                (inject Mock.xConfig)
                                fOfA
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    ( Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                        (mkElemVar Mock.mConfig)
                    )
            assertEqual "" expect actual
        , testCase "concrete Map with framed Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        ( mconcat
                            [ Condition.assign (inject Mock.xConfig) fOfA
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    ( Mock.concatMap
                        (mkElemVar Mock.mConfig)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                    )
            assertEqual "" expect actual
        , testCase "framed Map with concrete Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        ( mconcat
                            [ Condition.assign (inject Mock.xConfig) fOfA
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                        (mkElemVar Mock.mConfig)
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual
        , testCase "framed Map with concrete Map" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                        ( mconcat
                            [ Condition.assign (inject Mock.xConfig) fOfA
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.concatMap
                        (mkElemVar Mock.mConfig)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.xConfig)])
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual
        , testCase "concrete Map with element+unit" $ do
            let expect =
                    [ Pattern.withCondition
                        (Mock.builtinMap [(Mock.a, fOfA)])
                        ( mconcat
                            [ Condition.assign (inject Mock.xConfig) Mock.a
                            , Condition.assign (inject Mock.yConfig) fOfA
                            ]
                        )
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA)])
                    ( Mock.concatMap
                        ( Mock.elementMap
                            (mkElemVar Mock.xConfig)
                            (mkElemVar Mock.yConfig)
                        )
                        Mock.unitMap
                    )
            assertEqual "" expect actual
        , testCase "map elem key inj splitting" $ do
            let expected =
                    [ Pattern.withCondition
                        ( Mock.builtinMap
                            [
                                ( Mock.sortInjection
                                    Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        )
                        ( mconcat
                            [ Condition.assign
                                (inject Mock.xConfigSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.yConfig) fOfA
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.builtinMap
                        [
                            ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                            , fOfA
                            )
                        ]
                    )
                    ( Mock.elementMap
                        ( Mock.sortInjection
                            Mock.testSort
                            (mkElemVar Mock.xConfigSubSort)
                        )
                        (mkElemVar Mock.yConfig)
                    )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let key = Mock.a
                value = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMap = Mock.builtinMap [(key, value)]
                valueInj = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMapInj = Mock.builtinMap [(key, valueInj)]
                expected =
                    [ Pattern.withCondition
                        testMapInj
                        ( mconcat
                            [ Condition.assign
                                (inject Mock.xConfigSubSort)
                                ( Mock.sortInjection
                                    Mock.subSort
                                    Mock.aSubSubsort
                                )
                            , Condition.assign (inject Mock.yConfig) Mock.a
                            ]
                        )
                    ]
            actual <-
                unify
                    testMap
                    ( Mock.elementMap
                        (mkElemVar Mock.yConfig)
                        ( Mock.sortInjection
                            Mock.testSort
                            (mkElemVar Mock.xConfigSubSort)
                        )
                    )
            assertEqual "" expected actual
        , testCase "map concat key inj splitting" $ do
            let expected =
                    [ Pattern.withCondition
                        ( Mock.builtinMap
                            [
                                ( Mock.sortInjection
                                    Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        )
                        ( mconcat
                            [ Condition.assign
                                (inject Mock.xConfigSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.yConfig) fOfA
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [])
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.builtinMap
                        [
                            ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                            , fOfA
                            )
                        ]
                    )
                    ( Mock.concatMap
                        ( Mock.elementMap
                            ( Mock.sortInjection
                                Mock.testSort
                                (mkElemVar Mock.xConfigSubSort)
                            )
                            (mkElemVar Mock.yConfig)
                        )
                        (mkElemVar Mock.mConfig)
                    )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let expected =
                    [ Pattern.withCondition
                        ( Mock.builtinMap
                            [
                                ( Mock.a
                                , Mock.sortInjection
                                    Mock.testSort
                                    Mock.aSubSubsort
                                )
                            ]
                        )
                        ( mconcat
                            [ Condition.assign
                                (inject Mock.xConfigSubSort)
                                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                            , Condition.assign (inject Mock.yConfig) Mock.a
                            , Condition.assign
                                (inject Mock.mConfig)
                                (Mock.builtinMap [])
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.builtinMap
                        [
                            ( Mock.a
                            , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                            )
                        ]
                    )
                    ( Mock.concatMap
                        ( Mock.elementMap
                            (mkElemVar Mock.yConfig)
                            ( Mock.sortInjection
                                Mock.testSort
                                (mkElemVar Mock.xConfigSubSort)
                            )
                        )
                        (mkElemVar Mock.mConfig)
                    )
            assertEqual "" expected actual
        , testCase "unifies functions in keys" $ do
            let concrete = Mock.builtinMap [(Mock.a, Mock.a)]
                symbolic = Mock.builtinMap [(Mock.f Mock.b, Mock.a)]
                expect =
                    makeEqualsPredicate Mock.a (Mock.f Mock.b)
                        & Condition.fromPredicate
                        & Pattern.withCondition concrete
            actual <- simplifyUnify concrete symbolic
            assertEqual "" ([expect], [expect]) actual
        ]
    , testGroup
        "builtin List domain"
        [ testCase "[same head, same head]" $ do
            let term1 =
                    Mock.builtinList
                        [ Mock.constr10 Mock.cf
                        , Mock.constr11 Mock.cf
                        ]
                expect = [Pattern.fromTermLike term1]
            actual <- unify term1 term1
            assertEqual "" expect actual
        , testCase "[same head, different head]" $ do
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                expect = []
            actual <- unify term3 term4
            assertEqual "" expect actual
        , testCase "[a] `concat` x /\\ [a, b] " $ do
            let x = configElementVariableFromId "x" Mock.listSort
                term5 =
                    Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
                expect =
                    [ Conditional
                        { term = Mock.builtinList [Mock.a, Mock.b]
                        , -- TODO: This predicate should have `listSort`;
                          predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
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
                        `Conditional.andPredicate` makeCeilPredicate expectTerm
                x = mkElemVar $ configElementVariableFromId "x" Mock.testSort
                l = mkElemVar $ configElementVariableFromId "y" Mock.listSort
                -- List unification does not fully succeed because the
                -- elementList symbol is not simplified to a builtin structure.
                lhs = Mock.concatList (Mock.elementList x) l
                rhs = Mock.builtinList [Mock.a, Mock.b]
            actual <- unify lhs rhs
            assertEqual "" [expect] actual
        , testCase "[a] `concat` unit /\\ x " $ do
            let x = configElementVariableFromId "x" Mock.listSort
                term9 = Mock.builtinList [Mock.a]
                term10 = Mock.concatList Mock.unitList (mkElemVar x)
                term11 = Mock.concatList (mkElemVar x) Mock.unitList
                expect =
                    [ Conditional
                        { term = Mock.builtinList [Mock.a]
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
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
    , testGroup
        "Builtin Set domain"
        [ testCase "set singleton + unit" $ do
            let expected =
                    [ Pattern.withCondition
                        (Mock.builtinSet [Mock.a])
                        (Condition.assign (inject Mock.xConfig) Mock.a)
                    ]
            actual <-
                unify
                    ( Mock.concatSet
                        (Mock.elementSet (mkElemVar Mock.xConfig))
                        Mock.unitSet
                    )
                    (Mock.builtinSet [Mock.a])
            assertEqual "" expected actual
        , testCase "handles set ambiguity" $ do
            let expected1 =
                    Pattern.withCondition
                        (Mock.builtinSet [Mock.a, Mock.b])
                        ( foldMap
                            (uncurry Condition.assign)
                            [ (inject Mock.xConfig, Mock.a)
                            ,
                                ( inject Mock.xConfigSet
                                , Mock.builtinSet [Mock.b]
                                )
                            ]
                        )
                expected2 =
                    Pattern.withCondition
                        (Mock.builtinSet [Mock.a, Mock.b])
                        ( foldMap
                            (uncurry Condition.assign)
                            [ (inject Mock.xConfig, Mock.b)
                            , (inject Mock.xConfigSet, Mock.builtinSet [Mock.a])
                            ]
                        )
                expected = OrPattern.fromPatterns [expected1, expected2]
            actual <-
                unify
                    ( Mock.concatSet
                        (Mock.elementSet (mkElemVar Mock.xConfig))
                        (mkElemVar Mock.xConfigSet)
                    )
                    (Mock.builtinSet [Mock.a, Mock.b])
                    & fmap OrPattern.fromPatterns
            assertEqual "" expected actual
        , testCase "set elem inj splitting" $ do
            let expected =
                    [ Pattern.withCondition
                        ( Mock.builtinSet
                            [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                        )
                        ( Condition.assign
                            (inject Mock.xConfigSubSort)
                            (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                        )
                    ]
            actual <-
                unify
                    ( Mock.elementSet
                        ( Mock.sortInjection
                            Mock.testSort
                            (mkElemVar Mock.xConfigSubSort)
                        )
                    )
                    ( Mock.builtinSet
                        [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                    )
            assertEqual "" expected actual
        , testCase "set concat inj splitting" $ do
            let expected =
                    [ Pattern.withCondition
                        ( Mock.builtinSet
                            [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                        )
                        ( foldMap
                            (uncurry Condition.assign)
                            [
                                ( inject Mock.xConfigSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,
                                ( inject Mock.xConfigSet
                                , Mock.builtinSet []
                                )
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.concatSet
                        ( Mock.elementSet
                            ( Mock.sortInjection
                                Mock.testSort
                                (mkElemVar Mock.xConfigSubSort)
                            )
                        )
                        (mkElemVar Mock.xConfigSet)
                    )
                    ( Mock.builtinSet
                        [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                    )
            assertEqual "" expected actual
        , testCase "set concat 2 inj splitting" $ do
            let testSet =
                    Mock.builtinSet
                        [ Mock.a
                        , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        ]
                expected =
                    [ Pattern.withCondition
                        testSet
                        ( foldMap
                            (uncurry Condition.assign)
                            [ (inject Mock.xConfig, Mock.a)
                            ,
                                ( inject Mock.xConfigSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            , (inject Mock.xConfigSet, Mock.builtinSet [])
                            ]
                        )
                    ]
            actual <-
                unify
                    ( Mock.concatSet
                        (Mock.elementSet (mkElemVar Mock.xConfig))
                        ( Mock.concatSet
                            ( Mock.elementSet
                                ( Mock.sortInjection
                                    Mock.testSort
                                    (mkElemVar Mock.xConfigSubSort)
                                )
                            )
                            (mkElemVar Mock.xConfigSet)
                        )
                    )
                    testSet
            assertEqual "" expected actual
        ]
    , testGroup
        "alias expansion"
        [ testCase "alias() vs top" $ do
            let x = mkVariable "x"
                alias = mkAlias' "alias1" x mkTop_
                left = applyAlias' alias $ mkTop Mock.testSort & mkRewritingTerm
            actual <- simplifyUnify left mkTop_
            assertExpectTop actual
        , testCase "alias1() vs alias2()" $ do
            let x = mkVariable "x"
                leftAlias = mkAlias' "leftAlias" x mkTop_
                left = applyAlias' leftAlias $ mkTop Mock.testSort
                rightAlias = mkAlias' "rightAlias" x mkTop_
                right = applyAlias' rightAlias $ mkTop Mock.testSort
            actual <- simplifyUnify left right
            assertExpectTop actual
        , testCase "alias1(alias2()) vs top" $ do
            let x = mkVariable "x"
                y = mkVariable "y"
                alias1 = mkAlias' "alias1" x mkTop_
                alias1App =
                    applyAlias' alias1 $
                        mkSetVar (SetVariableName <$> y)
                alias2 = mkAlias' "alias2" x alias1App
                alias2App = applyAlias' alias2 $ mkTop Mock.testSort
            actual <- simplifyUnify alias2App mkTop_
            assertExpectTop actual
        , testCase "alias1() vs injHead" $ do
            let expect =
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
        , testGroup
            "unhandled cases with aliases"
            [ testCase "top level" $ do
                let expect =
                        ( [Pattern.fromTermLike (mkAnd left plain1OfA)]
                        , [Pattern.fromTermLike (mkAnd left plain1OfA)]
                        )
                    x = mkVariable "x"
                    alias = mkAlias' "alias1" x plain0OfA
                    left = applyAlias' alias $ mkTop Mock.testSort
                actual <- simplifyUnify left plain1OfA
                assertEqual "" expect actual
            , testCase "one level deep" $ do
                let expect =
                        (
                            [ Pattern.fromTermLike
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            ]
                        ,
                            [ Pattern.fromTermLike
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
    , testGroup
        "internal Int values"
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
    , testGroup
        "internal Bool values"
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
    , testGroup
        "internal String values"
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
    , testGroup
        "KEquals"
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
        , testCase
            "And unification fails if pattern\
            \ is not function-like"
            $ do
                let input1 = Mock.keqBool (TermLike.mkOr a (cf xVar)) b
                    input2 = Mock.builtinBool False
                    expected =
                        TermLike.mkAnd input1 input2
                            & Pattern.fromTermLike
                            & pure
                actual <- simplify input1 input2
                assertEqual "" expected actual
        , testCase
            "Equal unification fails if pattern\
            \ is not function-like"
            $ do
                let input1 = Mock.keqBool (TermLike.mkOr a (cf xVar)) b
                    input2 = Mock.builtinBool False
                actual <- simplifyEquals mempty input1 input2
                assertEqual "" Nothing actual
        ]
    ]
  where
    xVar = mkElemVar Mock.xConfig
    cf = Mock.functionalConstr10
    a = Mock.a
    b = Mock.b

mkVariable :: Text -> Variable VariableName
mkVariable ident =
    Variable
        { variableName = mkVariableName (testId ident)
        , variableSort = Mock.testSort
        }

mkAlias' ::
    Text ->
    Variable VariableName ->
    TermLike VariableName ->
    SentenceAlias (TermLike VariableName)
mkAlias' ident var inner =
    mkAlias_
        (testId ident)
        Mock.testSort
        [inject $ fmap SetVariableName var]
        inner

applyAlias' ::
    InternalVariable variable =>
    SentenceAlias (TermLike VariableName) ->
    TermLike variable ->
    TermLike variable
applyAlias' alias arg = applyAlias alias [] [arg]

assertExpectTop ::
    ([Pattern RewritingVariableName], [Pattern RewritingVariableName]) ->
    IO ()
assertExpectTop =
    assertEqual "" ([Pattern.top], [Pattern.top])

test_equalsTermsSimplification :: [TestTree]
test_equalsTermsSimplification =
    [ testCase "adds ceil when producing substitutions" $ do
        let expected =
                Just
                    [ Conditional
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, Mock.cf)]
                        }
                    ]
        actual <- simplifyEquals Map.empty (mkElemVar Mock.xConfig) Mock.cf
        assertEqual "" expected actual
    , testCase "handles set ambiguity" $ do
        let asInternal ::
                Set.Set (TermLike Concrete) -> TermLike RewritingVariableName
            asInternal =
                Set.map (retractKey >>> fromJust)
                    >>> Set.toList
                    >>> flip zip (repeat SetValue)
                    >>> HashMap.fromList
                    >>> Ac.asInternalConcrete Mock.metadataTools Mock.setSort
            expected = Just $ do
                -- list monad
                (xValue, xSetValue) <-
                    [ (Mock.a, [Mock.b])
                        , (Mock.b, [Mock.a])
                        ]
                mconcat
                    [ Condition.assign (inject Mock.xConfig) xValue
                    , Condition.assign (inject Mock.xConfigSet) $
                        asInternal $ Set.fromList xSetValue
                    ]
                    & pure
        actual <-
            simplifyEquals
                Map.empty
                ( Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.xConfig))
                    (mkElemVar Mock.xConfigSet)
                )
                (asInternal (Set.fromList [Mock.a, Mock.b]))
        assertEqual "" expected actual
    , testGroup
        "builtin Map"
        [ testCase "unifies functions in keys" $ do
            let concrete = Mock.builtinMap [(Mock.a, Mock.a)]
                symbolic = Mock.builtinMap [(Mock.f Mock.b, Mock.a)]
                expect :: Conditional RewritingVariableName ()
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
                    ( Mock.inKeysMap
                        (mkElemVar Mock.xConfig)
                        (Mock.builtinMap [])
                    )
            assertEqual "" (Just [expect]) actual
        , testCase "key not in singleton Map" $ do
            let expect =
                    makeEqualsPredicate
                        (mkElemVar Mock.xConfig)
                        (mkElemVar Mock.yConfig)
                        & makeNotPredicate
                        & Condition.fromPredicate
            actual <-
                simplifyEquals
                    mempty
                    (Mock.builtinBool False)
                    ( Mock.inKeysMap
                        (mkElemVar Mock.xConfig)
                        ( Mock.builtinMap
                            [(mkElemVar Mock.yConfig, Mock.a)]
                        )
                    )
            assertEqual "" (Just [expect]) actual
        , testCase "key not in two-element Map" $ do
            let expect =
                    [ makeNotPredicate $
                        makeEqualsPredicate
                            (mkElemVar Mock.xConfig)
                            (mkElemVar Mock.yConfig)
                    , makeNotPredicate $
                        makeEqualsPredicate
                            (mkElemVar Mock.xConfig)
                            (mkElemVar Mock.zConfig)
                    , -- Definedness condition
                      makeNotPredicate $
                        makeEqualsPredicate
                            (mkElemVar Mock.yConfig)
                            (mkElemVar Mock.zConfig)
                    ]
                        & MultiAnd.make
            actual <-
                simplifyEquals
                    mempty
                    (Mock.builtinBool False)
                    ( Mock.inKeysMap
                        (mkElemVar Mock.xConfig)
                        ( Mock.builtinMap
                            [ (mkElemVar Mock.yConfig, Mock.a)
                            , (mkElemVar Mock.zConfig, Mock.a)
                            ]
                        )
                    )
                    & (fmap . fmap . fmap) (from @_ @(MultiAnd _))
            assertEqual "" (Just [expect]) actual
        , testCase "unevaluated function key in singleton Map" $ do
            let expect =
                    makeAndPredicate
                        ( makeNotPredicate
                            ( makeAndPredicate
                                ( makeCeilPredicate
                                    (Mock.f (mkElemVar Mock.xConfig))
                                )
                                ( makeEqualsPredicate
                                    (mkElemVar Mock.yConfig)
                                    (Mock.f (mkElemVar Mock.xConfig))
                                )
                            )
                        )
                        ( makeCeilPredicate
                            (Mock.f (mkElemVar Mock.xConfig))
                        )
                        & Condition.fromPredicate
            actual <-
                simplifyEquals
                    mempty
                    (Mock.builtinBool False)
                    ( Mock.inKeysMap
                        (Mock.f (mkElemVar Mock.xConfig))
                        ( Mock.builtinMap
                            [(mkElemVar Mock.yConfig, Mock.a)]
                        )
                    )
            assertEqual "" (Just [expect]) actual
        ]
    ]

test_functionAnd :: [TestTree]
test_functionAnd =
    [ testCase "simplifies result" $ do
        let f = TermLike.markSimplified . Mock.f
            x = mkElemVar Mock.xConfig
            y = mkElemVar Mock.yConfig
            expect =
                Pattern.withCondition (f x) $
                    Condition.fromPredicate $
                        makeEqualsPredicate (f x) (f y)
        let actual = functionAnd (f x) (f y)
        let matchResult = matchFunctionAnd (f x) (f y)
        assertEqual "" (Just ()) matchResult
        assertEqual "" expect (Pattern.syncSort actual)
        assertBool "" (Pattern.isSimplified sideRepresentation actual)
    ]

fOfA :: InternalVariable variable => TermLike variable
fOfA = Mock.f Mock.a

fOfB :: InternalVariable variable => TermLike variable
fOfB = Mock.f Mock.b

gOfA :: InternalVariable variable => TermLike variable
gOfA = Mock.g Mock.a

plain0OfA :: InternalVariable variable => TermLike variable
plain0OfA = Mock.plain10 Mock.a

plain1OfA :: InternalVariable variable => TermLike variable
plain1OfA = Mock.plain11 Mock.a

plain0OfB :: InternalVariable variable => TermLike variable
plain0OfB = Mock.plain10 Mock.b

plain1OfB :: InternalVariable variable => TermLike variable
plain1OfB = Mock.plain11 Mock.b

aDomainValue :: TermLike RewritingVariableName
aDomainValue =
    mkDomainValue
        DomainValue
            { domainValueSort = Mock.testSort
            , domainValueChild = mkStringLiteral "a"
            }

subDomainValue :: TermLike RewritingVariableName
subDomainValue =
    mkDomainValue
        DomainValue
            { domainValueSort = Mock.subSort
            , domainValueChild = mkStringLiteral "a"
            }

subOtherDomainValue :: TermLike RewritingVariableName
subOtherDomainValue =
    mkDomainValue
        DomainValue
            { domainValueSort = Mock.subOthersort
            , domainValueChild = mkStringLiteral "a"
            }

bDomainValue :: TermLike RewritingVariableName
bDomainValue =
    mkDomainValue
        DomainValue
            { domainValueSort = Mock.testSort
            , domainValueChild = mkStringLiteral "b"
            }

simplifyUnifySorts ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO ([Pattern RewritingVariableName], [Pattern RewritingVariableName])
simplifyUnifySorts first second = do
    (simplified, unified) <-
        simplifyUnify (simplifiedTerm first) (simplifiedTerm second)
    return (map Pattern.syncSort simplified, Pattern.syncSort <$> unified)

simplifyUnify ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO ([Pattern RewritingVariableName], [Pattern RewritingVariableName])
simplifyUnify first second =
    (,)
        <$> simplify (simplifiedTerm first) (simplifiedTerm second)
        <*> unify (simplifiedTerm first) (simplifiedTerm second)

unify ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO [Pattern RewritingVariableName]
unify first second =
    runSimplifier mockEnv unification
  where
    mockEnv = Mock.env
    unification =
        Monad.Unify.runUnifierT Not.notSimplifier $
            termUnification
                Not.notSimplifier
                (simplifiedTerm first)
                (simplifiedTerm second)

simplify ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO [Pattern RewritingVariableName]
simplify first second =
    runSimplifierBranch mockEnv $
        termAnd Not.notSimplifier (simplifiedTerm first) (simplifiedTerm second)
  where
    mockEnv = Mock.env

simplifyEquals ::
    BuiltinAndAxiomSimplifierMap ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO (Maybe [Condition RewritingVariableName])
simplifyEquals simplifierAxioms first second =
    (fmap . fmap) toList $
        runSimplifier mockEnv $
            runMaybeT $ termEquals (simplifiedTerm first) (simplifiedTerm second)
  where
    mockEnv = Mock.env{simplifierAxioms}

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
        (SideCondition.top :: SideCondition VariableName)
