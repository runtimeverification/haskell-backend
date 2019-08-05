module Test.Kore.Step.Axiom.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    , test_unificationWithAppMatchOnTop
    , test_matching_Bool
    , test_matching_Int
    , test_matching_String
    , test_matching_List
    , test_matching_Set
    , test_matching_Map
    , match
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Bifunctor as Bifunctor
import           Data.Default
                 ( Default (..) )
import           Data.Function
                 ( on )
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( Simplification (Simplification) )
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
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

        , Mock.constr10 (mkVar Mock.x) `notMatches` Mock.constr11 Mock.a $ "different constructors"
        , Mock.f Mock.b `notMatches` Mock.g Mock.a                       $ "different functions"
        , Mock.f (mkVar Mock.x) `notMatches` Mock.g Mock.a               $ "different functions with variable"
        , Mock.plain10 Mock.b `notMatches` Mock.plain11 Mock.a           $ "different symbols"
        , Mock.plain10 (mkVar Mock.x) `notMatches` Mock.plain11 Mock.a   $ "different symbols with variable"
        ]

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
        actual <-
            matchDefinition
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" topOrPredicate actual

    , testCase "Builtin" $ do
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
        assertEqualWithExplanation "" topOrPredicate actual

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
  where
    aSubSub = Mock.functional00SubSubSort
    xSub = Variable (testId "x") mempty Mock.subSort

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern =
    [ failure Mock.a Mock.b                 "no-var - no-var"
    , failure (mkVar Mock.x) Mock.a         "var - no-var"
    , failure Mock.a (mkVar Mock.x)         "no-var - var"
    , failure (mkVar Mock.x) (mkVar Mock.y) "no-var - var"
    ]
  where
    failure term1 term2 = notMatches (Mock.plain10 term1) (Mock.plain11 term2)

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

test_matching_Bool :: [TestTree]
test_matching_Bool =
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
    , mkBool True  `notMatches` mkVar Mock.xBool  $ "true !~ x:Bool"
    , mkBool False `notMatches` mkVar Mock.xBool  $ "false !~ x:Bool"
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

test_matching_Int :: [TestTree]
test_matching_Int =
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
    , mkInt 1 `notMatches` mkVar Mock.xInt  $ "1 !~ x:Int"
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

test_matching_String :: [TestTree]
test_matching_String =
    [ testCase "concrete top" $ do
        let expect = topOrPredicate
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
    , mkStr "str" `notMatches` mkVar Mock.xString  $ "\"str\" !~ x:String"
    ]
  where
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

test_matching_List :: [TestTree]
test_matching_List =
    [ testCase "concrete top" $ do
        let expect = topOrPredicate
        actual <- matchConcrete [1, 2] [1, 2]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete [1, 2] [1, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom 2" $ do
        let expect = Nothing
        actual <- matchConcrete [1, 2] [1, 2, 3]
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
    , testCase "concat(empty, var) vs concrete" $ do
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
        actual <- matchConcat
            (mkList [] `concat'` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(unit, var) vs concrete" $ do
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
        actual <- matchConcat
            (mkList [mkInt 1] `concat'` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(concrete, var) vs concrete" $ do
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
        actual <- matchConcat
            (mkList [mkInt 1, mkInt 2, mkInt 3] `concat'` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, empty) vs concrete" $ do
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
        actual <- matchConcat
            (mkVar Mock.xList `concat'` mkList [] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, unit) vs concrete" $ do
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
        actual <- matchConcat
            (mkVar Mock.xList `concat'` mkList [mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, concrete) vs concrete" $ do
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
        actual <- matchConcat
            (mkVar Mock.xList `concat'` mkList [mkInt 1, mkInt 2, mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(x, var) vs concrete" $ do
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
        actual <- matchConcat
            (mkList [mkVar Mock.xInt] `concat'` mkVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, x) vs concrete" $ do
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
        actual <- matchConcat
            (mkVar Mock.xList `concat'` mkList [mkVar Mock.xInt])
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual

    , unitList               `notMatches` mkVar yList  $ "[] !~ y:List"
    , prefixList [one] xList `notMatches` mkVar yList  $ "[1] x:List !~ y:List"
    , suffixList xList [one] `notMatches` mkVar yList  $ "x:List [1] !~ y:List"

    , matches "[] ~ []"
        unitList
        unitList
        []
    , unitList `notMatches` mkList [one]            $ "[] !~ [1]"
    , unitList `notMatches` prefixList [one] xList  $ "[] !~ [1] x:List"
    , unitList `notMatches` suffixList xList [one]  $ "[] !~ x:List [1]"

    , mkList [one] `notMatches` unitList                $ "[1] !~ []"
    , matches "[1] ~ [1]"
        (mkList [one])
        (mkList [one])
        []
    , matches "[x:Int] ~ [1]"
        (mkList [mkVar xInt])
        (mkList [one       ])
        [(xInt, one)]
    , mkList [one] `notMatches` prefixList [one] xList  $ "[1] !~ [1] x:List"
    , mkList [one] `notMatches` suffixList xList [one]  $ "[1] !~ x:List [1]"

    , prefixList [one] xList `notMatches` unitList      $ "[1] x:List !~ []"
    , matches "[1] x:List ~ [1]"
        (prefixList [one] xList)
        (mkList     [one]      )
        [(xList, unitList)]
    , matches "[x:Int] y:List ~ [1]"
        (prefixList [mkVar xInt] yList)
        (mkList     [one]             )
        [(xInt, one), (yList, unitList)]
    , matches "[1] x:List ~ [1, 2]"
        (prefixList [one] xList)
        (mkList     [one, two ])
        [(xList, mkList [two])]
    , matches "[x:Int] y:List ~ [1, 2]"
        (prefixList [mkVar xInt] yList)
        (mkList     [one,        two ])
        [(xInt, one), (yList, mkList [two])]

    , suffixList xList [one] `notMatches` unitList      $ "x:List [1] !~ []"
    , matches "x:List [1] ~ [1]"
        (suffixList xList [one])
        (mkList           [one])
        [(xList, unitList)]
    , matches "y:List [x:Int] ~ [1]"
        (suffixList yList [mkVar xInt])
        (mkList           [one       ])
        [(xInt, one), (yList, unitList)]
    , matches "x:List [2] ~ [1, 2]"
        (suffixList xList [two])
        (mkList    [one,   two])
        [(xList, mkList [one])]
    , matches "y:List [x:Int] ~ [1, 2]"
        (suffixList yList [mkVar xInt])
        (mkList    [one,   two       ])
        [(xInt, two), (yList, mkList [one])]
    ]
  where
    xInt = varS (testId "xInt") Mock.intSort
    xList = varS (testId "xList") Mock.listSort
    yList = varS (testId "yList") Mock.listSort
    one = mkInt 1
    two = mkInt 2
    unitList = mkList []
    prefixList elems frame = Mock.concatList (mkList elems) (mkVar frame)
    suffixList frame elems = Mock.concatList (mkVar frame) (mkList elems)
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
    concat' = Mock.concatList
    matchList = matchDefinition `on` mkList
    matchConcrete =
        matchList `on` fmap mkInt
    matchVariable var val =
            matchList
            (either mkVar mkInt <$> var)
            (mkInt <$> val)
    matchConcat t1 =
        matchDefinition t1 . mkList . fmap mkInt

topOrPredicate :: Maybe (OrPredicate Variable)
topOrPredicate = Just $ OrPredicate.fromPredicate Predicate.topPredicate

data SetElementType concrete elem set
    = Concrete concrete
    | ElemVar elem
    | SetVar set

concrete :: [SetElementType concrete elem set] -> [concrete]
concrete = concatMap isConcrete'
  where
    isConcrete' =
        \case
            Concrete x -> [x]
            _ -> []

elemVars :: [SetElementType concrete elem set] -> [elem]
elemVars = concatMap isElemVar
  where
    isElemVar =
        \case
            ElemVar x -> [x]
            _ -> []

setVars :: [SetElementType concrete elem set] -> [set]
setVars = concatMap isSetVar
  where
    isSetVar =
        \case
            SetVar x -> [x]
            _ -> []

test_matching_Set :: [TestTree]
test_matching_Set =
    [ testCase "empty vs empty" $ do
        let expect = top
        actual <- matchConcrete [] []
        assertEqualWithExplanation "" expect actual
    , testCase "concrete vs concrete" $ do
        let expect = top
        actual <- matchConcrete [1, 2, 3] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "empty vs concrete" $ do
        let expect = Nothing
        actual <- matchConcrete [] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete vs empty" $ do
        let expect = Nothing
        actual <- matchConcrete [1, 2, 3] []
        assertEqualWithExplanation "" expect actual

    , testCase "elementVar vs singleton" $ do
        let expect = substitution [(Mock.xInt, 1)]
        actual <- matchVariable [ElemVar Mock.xInt] [1]
        assertEqualWithExplanation "" expect actual
    , testCase "{elementVar, rest} vs {set}" $ do
        let expect = substitution [(Mock.xInt, 2)]
        actual <-
            matchVariable [Concrete 1, Concrete 3, ElemVar Mock.xInt] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{elementVars, rest} vs {set}" $ do
        let expect =
                substitution
                    [ (Mock.xInt, 2)
                    , (Mock.yInt, 4)
                    ]
        actual <-
            matchVariable
                [Concrete 1, Concrete 3, ElemVar Mock.xInt, ElemVar Mock.yInt]
                [1, 2, 3, 4]
        assertEqualWithExplanation "" expect actual
    , testCase "more variables than available items" $ do
        let expect = Nothing
        actual <-
            matchVariable
                [Concrete 1, Concrete 3, ElemVar Mock.xInt, ElemVar Mock.yInt]
                [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "more items than available variables" $ do
        let expect = Nothing
        actual <-
            matchVariable
                [Concrete 1, Concrete 3, ElemVar Mock.xInt, ElemVar Mock.yInt]
                [1, 2, 3, 4, 5]
        assertEqualWithExplanation "" expect actual
    , testCase "{elementVariable} vs empty" $ do
        let expect = Nothing
        actual <- matchVariable [ElemVar Mock.xInt] []
        assertEqualWithExplanation "" expect actual

    , testCase "setVar vs empty" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [])
                            ]
                        }
                    ]
        actual <- matchVariable [SetVar Mock.xSet] []
        assertEqualWithExplanation "" expect actual
    , testCase "setVar vs unit" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 1])
                            ]
                        }
                    ]
        actual <- matchVariable [SetVar Mock.xSet] [1]
        assertEqualWithExplanation "" expect actual
    , testCase "setVar vs {set}" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 1, mkKey 2, mkKey 3])
                            ]
                        }
                    ]
        actual <- matchVariable [SetVar Mock.xSet] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, rest} vs {set}" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 2, mkKey 3])
                            ]
                        }
                    ]
        actual <- matchVariable [SetVar Mock.xSet, Concrete 1] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, set} vs {set}" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [])
                            ]
                        }
                    ]
        actual <-
            matchVariable
                [SetVar Mock.xSet, Concrete 1, Concrete 2, Concrete 3]
                [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, set, a} vs {set}" $ do
        let expect = Nothing
        actual <-
            matchVariable
                [SetVar Mock.xSet, Concrete 1, Concrete 2, Concrete 3, Concrete 4]
                [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "multiple setVars don't match" $ do
        let expect = Nothing
        actual <-
            matchVariable
                [SetVar Mock.xSet, SetVar Mock.ySet]
                [1, 2]
        assertEqualWithExplanation "" expect actual

    , testCase "{setVar, elemVar} vs empty" $ do
        let expect = Nothing
        actual <-
            matchVariable
                [SetVar Mock.xSet, ElemVar Mock.xInt]
                []
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, elemVar} vs unit" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [])
                            , (Mock.xInt, mkKey 1)
                            ]
                        }
                    ]
        actual <-
            matchVariable
                [SetVar Mock.xSet, ElemVar Mock.xInt]
                [1]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, elemVar} vs set" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 2, mkKey 3])
                            , (Mock.xInt, mkKey 1)
                            ]
                        }
                    ]
        actual <-
            matchVariable
                [SetVar Mock.xSet, ElemVar Mock.xInt]
                [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, elemVar, concrete} vs set" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 3])
                            , (Mock.xInt, mkKey 2)
                            ]
                        }
                    ]
        actual <-
            matchVariable
                [SetVar Mock.xSet, ElemVar Mock.xInt, Concrete 1]
                [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{setVar, elemVars, concrete} vs set" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xSet, mkConcreteSet [mkKey 5])
                            , (Mock.xInt, mkKey 2)
                            , (Mock.yInt, mkKey 4)
                            ]
                        }
                    ]
        actual <-
            matchVariable
                [ SetVar Mock.xSet
                , ElemVar Mock.xInt
                , ElemVar Mock.yInt
                , Concrete 1
                , Concrete 3
                ]
                [1, 2, 3, 4, 5]
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
                    $ fmap mkKey <$> subst
            }
        ]
    mkKey k =
        (mkBuiltin . Domain.BuiltinInt)
            Domain.InternalInt
                { builtinIntSort  = Mock.intSort
                , builtinIntValue = k
                }
    mkConcreteSet :: [TermLike Concrete] -> TermLike Variable
    mkConcreteSet =
        Ac.asInternalConcrete Mock.metadataTools Mock.setSort
        . Map.fromSet (const Domain.SetValue)
        . Set.fromList
    mkSet concrete' evars svars =
        Ac.asInternal Mock.metadataTools Mock.setSort
        $ Domain.wrapAc Domain.NormalizedAc
            { elementsWithVariables = Domain.SetElement <$> evars
            , concreteElements =
                Map.fromSet (const Domain.SetValue) (Set.fromList concrete')
            , opaque = svars
            }
    matchConcreteSet = matchDefinition `on` mkConcreteSet
    matchConcrete = matchConcreteSet `on` fmap mkKey
    matchVariable var val =
        matchDefinition
            (mkSet
                (mkKey <$> concrete var)
                (mkVar <$> elemVars var)
                (mkVar <$> setVars  var)
            )
            (mkConcreteSet $ fmap mkKey val)

test_matching_Map :: [TestTree]
test_matching_Map =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete [(1, 11), (2, 12)] [(1, 11), (2, 12)]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete [(1, 11), (2, 12)] [(1, 11)]
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom values not matching" $ do
        let expect = Nothing
        actual <- matchConcrete [(1, 11), (2, 12)] [(1, 11), (2, 13)]
        assertEqualWithExplanation "" expect actual
    , testCase "variable on right does not match" $ do
        let expect = Nothing
        actual <- matchDefinition (mkConcreteMap [(mkKey 1, mkVal 11)]) (mkVar Mock.xMap)
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
    , testCase "concat(var, empty) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkConcreteMap
                                  [ (mkKey 1, mkVal 11)
                                  , (mkKey 2, mkVal 12)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchBuiltin
            [ SetVar Mock.xMap ]
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, singleton) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkConcreteMap
                                  [ (mkKey 1, mkVal 11)
                                  , (mkKey 3, mkVal 13)
                                  ]
                              )
                            ]
                        }
                    ]
        actual <- matchBuiltin
            [ SetVar Mock.xMap
            , Concrete (2, 12)
            ]
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, concrete) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.xMap, mkConcreteMap [])
                            ]
                        }
                    ]
        actual <- matchBuiltin
            [ SetVar Mock.xMap
            , Concrete (1, 11)
            , Concrete (2, 12)
            , Concrete (3, 13)
            ]
            [ (1, 11)
            , (2, 12)
            , (3, 13)
            ]
        assertEqualWithExplanation "" expect actual
    , matches "k |-> v m ~ 0 |-> 1"
        (framedMap [(mkVar kInt, mkVar vInt)] [mMap])
        (builtinMap [(zero, one)])
        [(kInt, zero), (vInt, one), (mMap, unitMap)]
    , matches "k |-> v m ~ 0 |-> 1 2 |-> 4"
        (framedMap [(mkVar kInt, mkVar vInt)] [mMap])
        (builtinMap [(zero, one), (two, four)])
        [ (kInt, zero)
        , (vInt, one)
        , (mMap, builtinMap [(two, four)])
        ]
    ]
  where
    framedMap = Mock.framedMap
    builtinMap = Mock.builtinMap
    mkInt = Int.asInternal Mock.intSort
    kInt = varS (testId "kInt") Mock.intSort
    vInt = varS (testId "vInt") Mock.intSort
    mMap = varS (testId "mMap") Mock.mapSort
    zero = mkInt 0
    one = mkInt 1
    two = mkInt 2
    four = mkInt 4
    unitMap = builtinMap []
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
    mkKey :: Integer -> TermLike Concrete
    mkKey k =
        (mkBuiltin . Domain.BuiltinInt)
            Domain.InternalInt
                { builtinIntSort  = Mock.intSort
                , builtinIntValue = k
                }
    mkVal = Int.asInternal Mock.intSort
    mkConcreteMap
        :: [(TermLike Concrete, TermLike Variable)] -> TermLike Variable
    mkConcreteMap =
        Ac.asInternalConcrete Mock.metadataTools Mock.mapSort
        . fmap Domain.MapValue
        . Map.fromList
    mkMap
        :: [(TermLike Concrete, TermLike Variable)]
        -> [(TermLike Variable, TermLike Variable)]
        -> [TermLike Variable]
        -> TermLike Variable
    mkMap concrete' evars svars =
        Ac.asInternal Mock.metadataTools Mock.setSort
        $ Domain.wrapAc Domain.NormalizedAc
            { elementsWithVariables = Domain.MapElement <$> evars
            , concreteElements = Domain.MapValue <$> Map.fromList concrete'
            , opaque = svars
            }
    mapWithKey = Bifunctor.bimap mkKey
    matchMap = matchDefinition `on` mkConcreteMap
    matchConcrete = matchMap `on` fmap (mapWithKey mkVal)
    matchVariable var val =
        matchMap
            (mapWithKey (either mkVar mkVal) <$> var)
            (mapWithKey mkVal <$> val)
    matchBuiltin varComponents concreteElements =
        matchDefinition
            (mkMap
                (Bifunctor.bimap mkKey mkVal <$> concrete varComponents)
                (Bifunctor.bimap mkVar mkVal <$> elemVars varComponents)
                (mkVar <$> setVars  varComponents)
            )
            (mkConcreteMap (Bifunctor.bimap mkKey mkVal <$> concreteElements))

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
match first second =
    either (const Nothing) Just <$> matchAsEither
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

withMatch
    :: GHC.HasCallStack
    => (Maybe (OrPredicate Variable) -> Assertion)
    -> TermLike Variable
    -> TermLike Variable
    -> TestName
    -> TestTree
withMatch check term1 term2 comment =
    testCase comment $ do
        actual <- match term1 term2
        check actual

notMatches
    :: GHC.HasCallStack
    => TermLike Variable
    -> TermLike Variable
    -> TestName
    -> TestTree
notMatches = withMatch (assertBool "" . Maybe.isNothing)

matches
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> [(Variable, TermLike Variable)]
    -> TestTree
matches comment term1 term2 substitutions =
    withMatch check term1 term2 comment
  where
    expect =
        OrPredicate.fromPredicate
        $ Predicate.fromSubstitution
        $ Substitution.unsafeWrap substitutions
    check Nothing = assertFailure "Expected matching solution."
    check (Just actual) = assertEqual "" expect actual
