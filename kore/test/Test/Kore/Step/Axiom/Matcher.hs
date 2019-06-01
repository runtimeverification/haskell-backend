module Test.Kore.Step.Axiom.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    , test_unificationWithAppMatchOnTop
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Default
                 ( Default (..) )
import qualified Data.Map as Map

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( Simplification (Simplification) )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( make )
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
                 ( fromPredicates )
import           Kore.Internal.Predicate
                 ( Conditional (..) )
import qualified Kore.Internal.Predicate as Conditional
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Axiom.Matcher
                 ( matchAsUnification, unificationWithAppMatchOnTop )
import           Kore.Step.Axiom.Registry
                 ( axiomPatternsToEvaluators )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import qualified Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import qualified SMT

import           Test.Kore
                 ( emptyLogger, testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads =
    [ testCase "And" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition
                (mkAnd (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Application"
        [ testCase "same symbol" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchDefinition
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = Nothing
            actual <-
                matchDefinition
                    (Mock.constr10 (mkVar Mock.x))
                    (Mock.constr11 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different functions" $ do
            let expect = Nothing
            actual <-
                matchDefinition
                    (Mock.f Mock.b)
                    (Mock.g Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different functions with variable" $ do
            let expect = Nothing
            actual <-
                matchDefinition
                    (Mock.f (mkVar Mock.x))
                    (Mock.g Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different symbols" $ do
            let expect = Nothing
            actual <-
                matchDefinition
                    (Mock.plain10 Mock.b)
                    (Mock.plain11 Mock.a)
            assertEqualWithExplanation "" expect actual
        ]

        , testCase "different symbols with variable" $ do
            let expect = Nothing
            actual <-
                matchDefinition
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain11 Mock.a)
            assertEqualWithExplanation "" expect actual

    , testCase "Bottom" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <- matchDefinition mkBottom_ mkBottom_
        assertEqualWithExplanation "" expect actual

    , testCase "Ceil" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    }
                ]
        actual <-
            matchDefinition
                (mkCeil_ (Mock.plain10 (mkVar Mock.x)))
                (mkCeil_ (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "CharLiteral" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" expect actual

    , testCase "Builtin" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
        assertEqualWithExplanation "" expect actual

    , testCase "DomainValue" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Equals" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition
                (mkEquals_ (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkEquals_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Exists" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Floor" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkFloor_ (Mock.plain10 (mkVar Mock.x)))
                (mkFloor_ (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Forall" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkForall Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkImplies (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIn_ (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIn_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Next" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkNext (Mock.plain10 (mkVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Not" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkNot (Mock.plain10 (mkVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkOr (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkRewrites (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkRewrites (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "StringLiteral" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqualWithExplanation "" expect actual

    , testCase "Top" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                mkTop_
                mkTop_
        assertEqualWithExplanation "" expect actual

    , testCase "Variable (quantified)" $ do
        let expect = Just $ MultiOr.make [Conditional.topPredicate]
        actual <-
            matchDefinition
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Simplification"
        [ testCase "same symbol" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchSimplification
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = Nothing
            actual <-
                matchSimplification
                    (Mock.constr10 (mkVar Mock.x))
                    (Mock.constr11 Mock.a)
            assertEqualWithExplanation "" expect actual
        ]
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction =
    [ testCase "Functional" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(Mock.x, Mock.functional00)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkVar Mock.x) Mock.functional00
        assertEqualWithExplanation "" expect actual

    , testCase "Function" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkVar Mock.x) Mock.cf
        assertEqualWithExplanation "" expect actual

    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <- matchDefinition (mkVar Mock.x) (Mock.constr10 Mock.cf)
        assertEqualWithExplanation "" expect actual

    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (Mock.functional10 (mkVar Mock.y))
                (mkVar Mock.x)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection" $ do
        let
            a = Mock.functional00SubSubSort
            x = Variable (testId "x") mempty Mock.subSort
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(x, Mock.sortInjectionSubSubToSub a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.sortInjectionSubToTop (mkVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection reverse" $ do
        let
            a = Mock.functional00SubSubSort
            x = Variable (testId "x") mempty Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkVar x))
        assertEqualWithExplanation "" expect actual

    , testCase "Injection + substitution" $ do
        let
            aSubSub = Mock.functional00SubSubSort
            xSub = Variable (testId "x") mempty Mock.subSort
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (xSub, Mock.sortInjectionSubSubToSub aSubSub)
                        , (Mock.x, Mock.functional10 Mock.a)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
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
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (xSub, Mock.sortInjectionSubSubToSub aSubSub)
                        , (Mock.x, Mock.functional10 Mock.a)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
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
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkVar Mock.z)))
        assertEqualWithExplanation "" expect actual
    , testCase "Quantified no match on variable" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a Mock.a))
        assertEqualWithExplanation "" expect actual
    , testGroup "Simplification"
        [ testCase "Function" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { predicate = makeCeilPredicate Mock.cf
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                        , term = ()
                        }
                    ]
            actual <- matchSimplification (mkVar Mock.x) Mock.cf
            assertEqualWithExplanation "" expect actual

        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification
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
            matchSimplification
            (Mock.plain10 Mock.a)
            (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "var - no-var" $ do
        let expect = Nothing
        actual <-
            matchSimplification
            (Mock.plain10 (mkVar Mock.x))
            (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "no-var - var" $ do
        let expect = Nothing
        actual <-
            matchSimplification
            (Mock.plain10 Mock.a)
            (Mock.plain11 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "var - var" $ do
        let expect = Nothing
        actual <-
            matchSimplification
            (Mock.plain10 (mkVar Mock.x))
            (Mock.plain11 (mkVar Mock.y))
        assertEqualWithExplanation "" expect actual
    ]

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults =
    [ testCase "And" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkAnd (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Application" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
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
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkEquals_
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkEquals_ Mock.cf (Mock.constr20 Mock.cf Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIff (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
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
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                       [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIn_ (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIn_    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkOr (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
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
        let expect = Just (MultiOr.make [])
        actual <-
            matchDefinition
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd (mkVar Mock.y) (Mock.f (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual
    ]

test_unificationWithAppMatchOnTop :: [TestTree]
test_unificationWithAppMatchOnTop =
    [ testCase "Simple match same top" $ do
        let
            expect = Just (MultiOr.make [Conditional.topPredicate])
        actual <- unificationWithMatch Mock.cg Mock.cg
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs function" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f (mkVar Mock.x))
            (Mock.f Mock.cf)
        assertEqualWithExplanation "" expect actual
    , testCase "function vs variable" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f Mock.cf)
            (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "removes constructor" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f (Mock.functionalConstr10 (mkVar Mock.x)))
            (Mock.f (Mock.functionalConstr10 Mock.cf))
        assertEqualWithExplanation "" expect actual
    , testCase "produces predicate" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeEqualsPredicate
                            Mock.a
                            (Mock.g (mkVar Mock.x))
                        , substitution = mempty
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f Mock.a)
            (Mock.f (Mock.g (mkVar Mock.x)))
        assertEqualWithExplanation "" expect actual
    , testCase "merges results" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
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
            unificationWithMatch
            (Mock.functional20 Mock.a Mock.cf)
            (Mock.functional20 (Mock.g (mkVar Mock.x)) (mkVar Mock.y))
        assertEqualWithExplanation "" expect actual
    , testCase "not matching" $ do
        let
            expect = Just
                (MultiOr.make [])
        actual <-
            unificationWithMatch
            (Mock.f Mock.a)
            (Mock.f Mock.b)
        assertEqualWithExplanation "" expect actual
    , testCase "handles ambiguity" $ do
        let
            expected = Just $ OrPredicate.fromPredicates
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.a)]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            -- Ceil branches, which makes matching ambiguous.
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.y) Mock.a)
                                    (mkEquals_ (mkVar Mock.y) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- unificationWithMatchSimplifiers
            simplifiers
            (Mock.f (mkVar Mock.x))
            (Mock.f Mock.cf)
        assertEqualWithExplanation "" expected actual
    , testCase "handles multiple ambiguity" $ do
        let
            expected = Just $ OrPredicate.fromPredicates
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.a), (Mock.z, Mock.a)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.a), (Mock.z, Mock.b)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.b), (Mock.z, Mock.a)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.b), (Mock.z, Mock.b)
                        ]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            -- Ceil branches, which makes matching ambiguous.
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.y) Mock.a)
                                    (mkEquals_ (mkVar Mock.y) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ,   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cgId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cg
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.z) Mock.a)
                                    (mkEquals_ (mkVar Mock.z) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- unificationWithMatchSimplifiers
            simplifiers
            (Mock.functionalConstr20 (mkVar Mock.x) (mkVar Mock.var_x_1))
            (Mock.functionalConstr20 Mock.cf Mock.cg)
        assertEqualWithExplanation "" expected actual
    ]

matchDefinition
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
matchDefinition = match

matchSimplification
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
matchSimplification = match

unificationWithMatchSimplifiers
    :: BuiltinAndAxiomSimplifierMap
    -> TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
unificationWithMatchSimplifiers axiomIdToSimplifier first second = do
    result <-
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier Mock.env { simplifierAxioms = axiomIdToSimplifier }
        $ Monad.Unify.runUnifier
        $ unificationWithAppMatchOnTop first second
    return $ either (const Nothing) Just (MultiOr.make <$> result)

unificationWithMatch
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
unificationWithMatch = unificationWithMatchSimplifiers Map.empty

match
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
match first second = do
    result <- matchAsEither
    return $ either (const Nothing) Just result
  where
    matchAsEither
        :: IO (Either UnificationOrSubstitutionError (OrPredicate Variable))
    matchAsEither =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier Mock.env matchResult
    matchResult
        :: Simplifier
            (Either UnificationOrSubstitutionError (OrPredicate Variable))
    matchResult =
        fmap MultiOr.make <$> Monad.Unify.runUnifier
            (matchAsUnification first second)
