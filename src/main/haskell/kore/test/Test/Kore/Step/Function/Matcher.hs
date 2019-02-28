module Test.Kore.Step.Function.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    , test_unificationWithAppMatchOnTop
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Function.Matcher
                 ( matchAsUnification, unificationWithAppMatchOnTop )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unifier
                 ( UnificationProof )
import qualified SMT

import           Test.Kore
                 ( emptyLogger, noRepl, testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads =
    [ testCase "And" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkAnd (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Application"
        [ testCase "same symbol" $ do
            let expect = Just $ OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = Nothing
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.constr10 (mkVar Mock.x))
                    (Mock.constr11 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different functions" $ do
            let expect = Nothing
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.f Mock.b)
                    (Mock.g Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different functions with variable" $ do
            let expect = Nothing
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.f (mkVar Mock.x))
                    (Mock.g Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different symbols" $ do
            let expect = Nothing
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.plain10 Mock.b)
                    (Mock.plain11 Mock.a)
            assertEqualWithExplanation "" expect actual
        ]

        , testCase "different symbols with variable" $ do
            let expect = Nothing
            actual <-
                matchDefinition mockMetadataTools
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain11 Mock.a)
            assertEqualWithExplanation "" expect actual

    , testCase "Bottom" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition
                mockMetadataTools
                mkBottom_
                mkBottom_
        assertEqualWithExplanation "" expect actual

    , testCase "Ceil" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkCeil_ (Mock.plain10 (mkVar Mock.x)))
                (mkCeil_ (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "CharLiteral" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition mockMetaMetadataTools
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" expect actual

    , testCase "DomainValue" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition mockMetadataTools
                (mkDomainValue Mock.testSort1
                    $ Domain.BuiltinPattern
                    $ eraseAnnotations
                    $ mkStringLiteral "10"
                )
                (mkDomainValue Mock.testSort1
                    $ Domain.BuiltinPattern
                    $ eraseAnnotations
                    $ mkStringLiteral "10"
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Equals" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkEquals_ (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkEquals_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Exists" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Floor" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkFloor_ (Mock.plain10 (mkVar Mock.x)))
                (mkFloor_ (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Forall" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkForall Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkImplies (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkIn_ (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIn_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Next" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkNext (Mock.plain10 (mkVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Not" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkNot (Mock.plain10 (mkVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkOr (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkRewrites (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkRewrites (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "StringLiteral" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition mockMetaMetadataTools
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqualWithExplanation "" expect actual

    , testCase "Top" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition mockMetadataTools
                mkTop_
                mkTop_
        assertEqualWithExplanation "" expect actual

    , testCase "Variable (quantified)" $ do
        let expect = Just $ OrOfExpandedPattern.make [Predicated.topPredicate]
        actual <-
            matchDefinition mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Simplification"
        [ testCase "same symbol" $ do
            let expect = Just $ OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchSimplification mockMetadataTools
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = Nothing
            actual <-
                matchSimplification mockMetadataTools
                    (Mock.constr10 (mkVar Mock.x))
                    (Mock.constr11 Mock.a)
            assertEqualWithExplanation "" expect actual
        ]
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction =
    [ testCase "Functional" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(Mock.x, Mock.functional00)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkVar Mock.x)
                Mock.functional00
        assertEqualWithExplanation "" expect actual

    , testCase "Function" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkVar Mock.x)
                Mock.cf
        assertEqualWithExplanation "" expect actual

    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (mkVar Mock.x)
                (Mock.constr10 Mock.cf)
        assertEqualWithExplanation "" expect actual

    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (Mock.functional10 (mkVar Mock.y))
                (mkVar Mock.x)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection" $ do
        let
            a = Mock.functional00SubSubSort
            x = Variable (testId "x") mempty Mock.subSort
            expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(x, Mock.sortInjectionSubSubToSub a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (Mock.sortInjectionSubToTop (mkVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection reverse" $ do
        let
            a = Mock.functional00SubSubSort
            x = Variable (testId "x") mempty Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkVar x))
        assertEqualWithExplanation "" expect actual

    , testCase "Injection + substitution" $ do
        let
            aSubSub = Mock.functional00SubSubSort
            xSub = Variable (testId "x") mempty Mock.subSort
            expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (xSub, Mock.sortInjectionSubSubToSub aSubSub)
                        , (Mock.x, Mock.functional10 Mock.a)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                    (mkVar Mock.x)
                )
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubSubToTop aSubSub)
                    (Mock.functional10 Mock.a)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "substitution + Injection" $ do
        let
            aSubSub = Mock.functional00SubSubSort
            xSub = Variable (testId "x") mempty Mock.subSort
            expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (xSub, Mock.sortInjectionSubSubToSub aSubSub)
                        , (Mock.x, Mock.functional10 Mock.a)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (Mock.functionalTopConstr21
                    (mkVar Mock.x)
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                )
                (Mock.functionalTopConstr21
                    (Mock.functional10 Mock.a)
                    (Mock.sortInjectionSubSubToTop aSubSub)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Quantified match on equivalent variable" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkVar Mock.z)))
        assertEqualWithExplanation "" expect actual
    , testCase "Quantified no match on variable" $ do
        let expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a Mock.a))
        assertEqualWithExplanation "" expect actual
    , testGroup "Simplification"
        [ testCase "Function" $ do
            let expect = Just $ OrOfExpandedPattern.make
                    [ Predicated
                        { predicate = makeCeilPredicate Mock.cf
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                        , term = ()
                        }
                    ]
            actual <-
                matchSimplification mockMetadataTools
                    (mkVar Mock.x)
                    Mock.cf
            assertEqualWithExplanation "" expect actual

        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification mockMetadataTools
                    (mkVar Mock.x)
                    (Mock.constr10 Mock.cf)
            assertEqualWithExplanation "" expect actual
        ]
    ]

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern =
    [ testCase "no-var - no-var" $ do
        let expect = Nothing
        actual <-
            matchSimplification mockMetadataTools
            (Mock.plain10 Mock.a)
            (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "var - no-var" $ do
        let expect = Nothing
        actual <-
            matchSimplification mockMetadataTools
            (Mock.plain10 (mkVar Mock.x))
            (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "no-var - var" $ do
        let expect = Nothing
        actual <-
            matchSimplification mockMetadataTools
            (Mock.plain10 Mock.a)
            (Mock.plain11 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "var - var" $ do
        let expect = Nothing
        actual <-
            matchSimplification mockMetadataTools
            (Mock.plain10 (mkVar Mock.x))
            (Mock.plain11 (mkVar Mock.y))
        assertEqualWithExplanation "" expect actual
    ]

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults =
    [ testCase "And" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkAnd (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Application" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (Mock.plain20
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cf Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Equals" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkEquals_
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkEquals_ Mock.cf (Mock.constr20 Mock.cf Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkIff (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkImplies
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkImplies
                    Mock.cf
                    (Mock.constr20 Mock.cf    Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                       [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkIn_ (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIn_    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkOr (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ OrOfExpandedPattern.make
                [ Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition mockMetadataTools
                (mkRewrites
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cg (mkVar Mock.y))
                )
                (mkRewrites
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Merge conflict" $ do
        let expect = Just (OrOfExpandedPattern.make [])
        actual <-
            matchDefinition mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd (mkVar Mock.y) (Mock.f (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual
    ]

test_unificationWithAppMatchOnTop :: [TestTree]
test_unificationWithAppMatchOnTop =
    [ testCase "Simple match same top" $ do
        let
            expect = Just (OrOfExpandedPattern.make [Predicated.topPredicate])
        actual <-
            unificationWithMatch mockMetadataTools
            Mock.cg
            Mock.cg
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs function" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.f (mkVar Mock.x))
            (Mock.f Mock.cf)
        assertEqualWithExplanation "" expect actual
    , testCase "function vs variable" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.f Mock.cf)
            (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "removes constructor" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.f (Mock.functionalConstr10 (mkVar Mock.x)))
            (Mock.f (Mock.functionalConstr10 Mock.cf))
        assertEqualWithExplanation "" expect actual
    , testCase "produces predicate" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeEqualsPredicate
                            Mock.a
                            (Mock.g (mkVar Mock.x))
                        , substitution = mempty
                        }
                    ]
                )
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.f Mock.a)
            (Mock.f (Mock.g (mkVar Mock.x)))
        assertEqualWithExplanation "" expect actual
    , testCase "merges results" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = ()
                        , predicate = makeAndPredicate
                            (makeEqualsPredicate
                                Mock.a
                                (Mock.g (mkVar Mock.x))
                            )
                            (makeCeilPredicate Mock.cf)
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.functional20 Mock.a Mock.cf)
            (Mock.functional20 (Mock.g (mkVar Mock.x)) (mkVar Mock.y))
        assertEqualWithExplanation "" expect actual
    , testCase "not matching" $ do
        let
            expect = Just
                (OrOfExpandedPattern.make [])
        actual <-
            unificationWithMatch mockMetadataTools
            (Mock.f Mock.a)
            (Mock.f Mock.b)
        assertEqualWithExplanation "" expect actual
    ]

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools = Mock.makeMetadataTools [] [] [] []

matchDefinition
    :: forall level . ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonOrOfPredicateSubstitution level))
matchDefinition = match

matchSimplification
    :: forall level . ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonOrOfPredicateSubstitution level))
matchSimplification = match

unificationWithMatch
    :: forall level . ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonOrOfPredicateSubstitution level))
unificationWithMatch tools first second = do
    eitherResult <- SMT.runSMT SMT.defaultConfig
        $ evalSimplifier emptyLogger noRepl
        $ runExceptT
        $ unificationWithAppMatchOnTop
            tools
            (Mock.substitutionSimplifier tools)
            (Simplifier.create tools Map.empty)
            Map.empty
            first
            second
    case eitherResult of
        Left _err -> return Nothing
        Right (result, _proof) -> return (Just result)

match
    :: forall level . ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonOrOfPredicateSubstitution level))
match tools first second =
    matchAsEither >>= return . \case
        Left _err -> Nothing
        Right (result, _) -> Just result
  where
    matchAsEither
        :: IO
            (Either
                (UnificationOrSubstitutionError level Variable)
                ( CommonOrOfPredicateSubstitution level
                , UnificationProof level Variable
                )
            )
    matchAsEither =
        SMT.runSMT SMT.defaultConfig
            $ evalSimplifier emptyLogger noRepl
            $ runExceptT matchResult
    matchResult
        :: ExceptT
            (UnificationOrSubstitutionError level Variable)
            Simplifier
            ( CommonOrOfPredicateSubstitution level
            , UnificationProof level Variable
            )
    matchResult =
        matchAsUnification
            tools
            (Mock.substitutionSimplifier tools)
            (Simplifier.create tools Map.empty)
            Map.empty
            first
            second
