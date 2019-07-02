module Test.Kore.Step.Axiom.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    , test_unificationWithAppMatchOnTop
    , test_matchingBuiltins
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Bifunctor as Bifunctor
import           Data.Default
                 ( Default (..) )
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( on )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( Simplification (Simplification) )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.String as String
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Internal.MultiOr as MultiOr
                 ( make )
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Predicate
                 ( Conditional (..) )
import qualified Kore.Internal.Predicate as Predicate
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
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
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
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" expect actual

    , testCase "Builtin" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
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
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
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
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqualWithExplanation "" expect actual

    , testCase "Top" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                mkTop_
                mkTop_
        assertEqualWithExplanation "" expect actual

    , testCase "Variable (quantified)" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
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
    , testGroup "Evaluated"
        [ testCase "Functional" $ do
            let evaluated = mkEvaluated Mock.functional00
                expect =
                    Just . OrPredicate.fromPredicate
                    $ Predicate.fromSingleSubstitution (Mock.x, evaluated)
            actual <- matchDefinition (mkVar Mock.x) evaluated
            assertEqualWithExplanation "" expect actual

        , testCase "Function" $ do
            let evaluated = mkEvaluated Mock.cf
                expect =
                    (Just . OrPredicate.fromPredicate)
                    (Predicate.fromSingleSubstitution (Mock.x, evaluated))
                        { predicate = makeCeilPredicate evaluated }
            actual <- matchDefinition (mkVar Mock.x) evaluated
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
            expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
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
                    , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate (Mock.f Mock.b) Mock.b
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.cf)]
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
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkVar Mock.y) Mock.b)
                                    )
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
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.a) Mock.a)
                        (makeEqualsPredicate (Mock.g Mock.a) Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg) ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.a) Mock.a)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg) ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.a) Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg) ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg) ]
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
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkVar Mock.y) Mock.b)
                                    )
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
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.g (mkVar Mock.z))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkVar Mock.z) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.g (mkVar Mock.z))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkVar Mock.z) Mock.b)
                                    )
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

test_matchingBuiltins :: [TestTree]
test_matchingBuiltins =
    Foldable.fold
        [ matchingBool
        , matchingInt
        , matchingString
        , matchingList
        -- TODO(Vladimir): implement after Virgil's set changes is done
        -- , matchingSet
        , matchingMap
        ]

matchingBool :: [TestTree]
matchingBool =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete True True
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete True False
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs concrete" $ do
        let expect = substitution [(Mock.xBool, True)]
        actual <- matchVariable Mock.xBool True
        assertEqualWithExplanation "" expect actual
    , testCase "concrete vs variable does not work" $ do
        let expect = Nothing
        actual <- matchDefinition (mkBool True) (mkVar Mock.xBool)
        assertEqualWithExplanation "" expect actual
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkBool subst)
            }
        ]
    mkBool = Bool.asInternal Mock.boolSort
    matchConcrete = matchDefinition `on` mkBool
    matchVariable var val =
        matchDefinition (mkVar var) (mkBool val)

matchingInt :: [TestTree]
matchingInt =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete 1 1
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete 1 0
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs concrete" $ do
        let expect = substitution [(Mock.xInt, 1)]
        actual <- matchVariable Mock.xInt 1
        assertEqualWithExplanation "" expect actual
    , testCase "concrete vs variable does not work" $ do
        let expect = Nothing
        actual <- matchDefinition (mkInt 1) (mkVar Mock.xInt)
        assertEqualWithExplanation "" expect actual
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkInt subst)
            }
        ]
    mkInt = Int.asInternal Mock.intSort
    matchConcrete = matchDefinition `on` mkInt
    matchVariable var val =
        matchDefinition (mkVar var) (mkInt val)

matchingString :: [TestTree]
matchingString =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete "str" "str"
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete "s1" "s2"
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs concrete" $ do
        let expect = substitution [(Mock.xString, "str")]
        actual <- matchVariable Mock.xString "str"
        assertEqualWithExplanation "" expect actual
    , testCase "concrete vs variable does not work" $ do
        let expect = Nothing
        actual <- matchDefinition (mkStr "str") (mkVar Mock.xString)
        assertEqualWithExplanation "" expect actual
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkStr subst)
            }
        ]
    mkStr = String.asInternal Mock.stringSort
    matchConcrete = matchDefinition `on` mkStr
    matchVariable var val =
        matchDefinition (mkVar var) (mkStr val)

matchingList :: [TestTree]
matchingList =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete [1, 2] [1, 2]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete [1, 2] [1, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "variable on right does not match" $ do
        let expect = Nothing
        actual <- matchDefinition (mkList [mkInt 1]) (mkVar Mock.xList)
        assertEqualWithExplanation "" expect actual
    , testCase "single variable" $ do
        let expect = substitution [(Mock.xInt, 2)]
        actual <- matchVariable [Right 1, Left Mock.xInt] [1, 2]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables (simple)" $ do
        let expect = substitution [(Mock.xInt, 1), (Mock.yInt, 2)]
        actual <- matchVariable
            [ Left Mock.xInt
            , Left Mock.yInt
            ]
            [ 1, 2 ]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables" $ do
        let expect = substitution [(Mock.xInt, 2), (Mock.yInt, 4)]
        actual <- matchVariable
            [ Right 1
            , Left Mock.xInt
            , Right 3
            , Left Mock.yInt
            ]
            [ 1, 2, 3, 4 ]
        assertEqualWithExplanation "" expect actual
    , testCase "no AC" $ do
        let expect = Nothing
        actual <- matchVariable
            [ Right 1, Left Mock.xInt] [ 2, 1 ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(empty, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [mkInt 1, mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkList [] `cons` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(unit, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkList [mkInt 1] `cons` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(concrete, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkList [mkInt 1, mkInt 2, mkInt 3] `cons` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(var, empty) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [mkInt 1, mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xList `cons` mkList [] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(var, unit) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [mkInt 1, mkInt 2])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xList `cons` mkList [mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(var, concrete) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xList, mkList [])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xList `cons` mkList [mkInt 1, mkInt 2, mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(x, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xInt, mkInt 1)
                            , (Mock.xList, mkList [mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkList [mkVar Mock.xInt] `cons` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "cons(var, x) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xInt, mkInt 3)
                            , (Mock.xList, mkList [mkInt 1, mkInt 2])
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xList `cons` mkList [mkVar Mock.xInt])
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkInt subst)
            }
        ]
    mkInt = Int.asInternal Mock.intSort
    mkList = List.asInternal Mock.metadataTools Mock.listSort . Seq.fromList
    cons = Mock.concatList
    matchList = matchDefinition `on` mkList
    matchConcrete =
        matchList `on` fmap mkInt
    matchVariable var val =
            matchList
            (either mkVar mkInt <$> var)
            (mkInt <$> val)
    matchCons t1 l2 =
        matchDefinition t1
            . mkList
            . fmap mkInt
            $ l2

matchingMap :: [TestTree]
matchingMap =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete [(1, 11), (2, 12)] [(1, 11), (2, 12)]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete [(1, 11), (2, 12)] [(1, 11)]
        assertEqualWithExplanation "" expect actual
    , testCase "variable on right does not match" $ do
        let expect = Nothing
        actual <- matchDefinition (mkMap [(mkKey 1, mkVal 11)]) (mkVar Mock.xMap)
        assertEqualWithExplanation "" expect actual
    , testCase "single variable" $ do
        let expect = substitution [(Mock.xInt, 12)]
        actual <- matchVariable
            [ (1, Right 11)
            , (2, Left Mock.xInt)
            ]
            [ (2, 12)
            , (1, 11)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables" $ do
        let expect = substitution [(Mock.xInt, 12), (Mock.yInt, 14)]
        actual <- matchVariable
            [ (1, Right 11)
            , (2, Left Mock.xInt)
            , (3, Right 13)
            , (4, Left Mock.yInt)
            ]
            [ (2, 12)
            , (1, 11)
            , (4, 14)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (empty, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap
                                  [ (mkKey 1, mkVal 11)
                                  , (mkKey 2, mkVal 12)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchCons
            (mkMap [] `cons` mkVar Mock.xMap)
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (unit, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap
                                  [ (mkKey 2, mkVal 12)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchCons
            (mkMap [(mkKey 1, mkVal 11)] `cons` mkVar Mock.xMap)
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (concrete, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap [])
                            ]
                        }
                    ]
        actual <- matchCons
            ( mkMap
                [ (mkKey 1, mkVal 11)
                , (mkKey 2, mkVal 12)
                , (mkKey 3, mkVal 13)
                ]
            `cons` mkVar Mock.xMap
            )
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (var, empty) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap
                                  [ (mkKey 1, mkVal 11)
                                  , (mkKey 2, mkVal 12)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xMap `cons` mkMap [])
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (var, unit) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap
                                  [ (mkKey 1, mkVal 11)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchCons
            (mkVar Mock.xMap `cons` mkMap [(mkKey 2, mkVal 12)])
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "cons (var, concrete) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkMap [])
                            ]
                        }
                    ]
        actual <- matchCons
            ( mkVar Mock.xMap
            `cons` mkMap
                [ (mkKey 1, mkVal 11)
                , (mkKey 2, mkVal 12)
                , (mkKey 3, mkVal 13)
                ]
            )
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkVal subst)
            }
        ]
    mkKey k =
        (mkBuiltin . Domain.BuiltinInt)
            Domain.InternalInt
                { builtinIntSort  = Mock.intSort
                , builtinIntValue = k
                }
    mkVal = Int.asInternal Mock.intSort
    mkMap = Map.asInternal Mock.metadataTools Mock.mapSort . Map.fromList
    mapWithKey = Bifunctor.bimap mkKey
    matchMap = matchDefinition `on` mkMap
    matchConcrete =
        matchMap `on` fmap (mapWithKey mkVal)
    matchVariable var val =
            matchMap
            (mapWithKey (either mkVar mkVal) <$> var)
            (mapWithKey mkVal <$> val)
    cons = Mock.concatMap
    matchCons t1 m2 =
        matchDefinition t1
            . mkMap
            $ fmap (mapWithKey mkVal) m2

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
        $ Monad.Unify.runUnifierT
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
        (fmap . fmap) MultiOr.make
        $ Monad.Unify.runUnifierT
        $ matchAsUnification first second
