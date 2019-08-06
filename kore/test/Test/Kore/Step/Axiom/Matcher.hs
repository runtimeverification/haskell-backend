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
import           Kore.Syntax.ElementVariable
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import qualified Kore.Variables.UnifiedVariable as UnifiedVariable
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
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition
                (mkAnd (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Application"
        [ testCase "same symbol" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchDefinition
                    (Mock.plain10 (mkElemVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual
        , testCase "same symbol, set variables" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.SetVar Mock.setX, mkTop Mock.testSort)]
                        }
                    ]
            actual <-
                matchDefinition
                    (Mock.plain10 (mkSetVar Mock.setX))
                    (Mock.plain10 (mkTop Mock.testSort))
            assertEqualWithExplanation "" expect actual

        , Mock.constr10 (mkElemVar Mock.x) `notMatches` Mock.constr11 Mock.a $ "different constructors"
        , Mock.f Mock.b `notMatches` Mock.g Mock.a                       $ "different functions"
        , Mock.f (mkElemVar Mock.x) `notMatches` Mock.g Mock.a               $ "different functions with variable"
        , Mock.plain10 Mock.b `notMatches` Mock.plain11 Mock.a           $ "different symbols"
        , Mock.plain10 (mkElemVar Mock.x) `notMatches` Mock.plain11 Mock.a   $ "different symbols with variable"
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
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    }
                ]
        actual <-
            matchDefinition
                (mkCeil_ (Mock.plain10 (mkElemVar Mock.x)))
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
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    }
                ]
        actual <-
            matchDefinition
                (mkEquals_ (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkEquals_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Exists" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkExists Mock.x (Mock.plain10 (mkElemVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Floor" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkFloor_ (Mock.plain10 (mkElemVar Mock.x)))
                (mkFloor_ (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Forall" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.y, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkForall Mock.x (Mock.plain10 (mkElemVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkImplies (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIn_ (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkIn_ (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Next" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkNext (Mock.plain10 (mkElemVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Not" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkNot (Mock.plain10 (mkElemVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkOr (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.b)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkRewrites (Mock.plain10 Mock.a) (mkElemVar Mock.x))
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
                (mkExists Mock.x (Mock.plain10 (mkElemVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkElemVar Mock.y)))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Simplification"
        [ testCase "same symbol" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchSimplification
                    (Mock.plain10 (mkElemVar Mock.x))
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
                        Substitution.unsafeWrap
                            [ ( UnifiedVariable.ElemVar Mock.x
                              , Mock.functional00
                              )
                            ]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkElemVar Mock.x) Mock.functional00
        assertEqualWithExplanation "" expect actual

    , testCase "SetVariable vs Function" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.SetVar Mock.setX, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkSetVar Mock.setX) Mock.cf
        assertEqualWithExplanation "" expect actual

    , testCase "SetVariable vs Bottom" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.SetVar Mock.setX, mkBottom Mock.testSort)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkSetVar Mock.setX) (mkBottom Mock.testSort)
        assertEqualWithExplanation "" expect actual

    , testCase "Function" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkElemVar Mock.x) Mock.cf
        assertEqualWithExplanation "" expect actual

    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <- matchDefinition (mkElemVar Mock.x) (Mock.constr10 Mock.cf)
        assertEqualWithExplanation "" expect actual

    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (Mock.functional10 (mkElemVar Mock.y))
                (mkElemVar Mock.x)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection" $ do
        let
            a = Mock.functional00SubSubSort
            x = ElementVariable $ Variable (testId "x") mempty Mock.subSort
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ ( UnifiedVariable.ElemVar x
                          , Mock.sortInjectionSubSubToSub a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.sortInjectionSubToTop (mkElemVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection reverse" $ do
        let
            a = Mock.functional00SubSubSort
            x = ElementVariable $ Variable (testId "x") mempty Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkElemVar x))
        assertEqualWithExplanation "" expect actual

    , testCase "Injection + substitution" $ do
        let
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ ( UnifiedVariable.ElemVar xSub
                          , Mock.sortInjectionSubSubToSub aSubSub
                          )
                        , ( UnifiedVariable.ElemVar Mock.x
                          , Mock.functional10 Mock.a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
                    (mkElemVar Mock.x)
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
                        [ ( UnifiedVariable.ElemVar xSub
                          , Mock.sortInjectionSubSubToSub aSubSub
                          )
                        , ( UnifiedVariable.ElemVar Mock.x
                          , Mock.functional10 Mock.a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.functionalTopConstr21
                    (mkElemVar Mock.x)
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
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
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkExists Mock.y (Mock.constr20 (mkElemVar Mock.x) (mkElemVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkElemVar Mock.z)))
        assertEqualWithExplanation "" expect actual
    , testCase "Quantified no match on variable" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkExists Mock.y (Mock.constr20 (mkElemVar Mock.x) (mkElemVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a Mock.a))
        assertEqualWithExplanation "" expect actual
    , testGroup "Simplification"
        [ testCase "Function" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { predicate = makeCeilPredicate Mock.cf
                        , substitution =
                            Substitution.unsafeWrap
                                [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                        , term = ()
                        }
                    ]
            actual <- matchSimplification (mkElemVar Mock.x) Mock.cf
            assertEqualWithExplanation "" expect actual

        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification
                    (mkElemVar Mock.x)
                    (Mock.constr10 Mock.cf)
            assertEqualWithExplanation "" expect actual
        ]
    , testGroup "Evaluated"
        [ testCase "Functional" $ do
            let evaluated = mkEvaluated Mock.functional00
                expect =
                    Just . OrPredicate.fromPredicate
                    $ Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated)
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqualWithExplanation "" expect actual

        , testCase "Function" $ do
            let evaluated = mkEvaluated Mock.cf
                expect =
                    (Just . OrPredicate.fromPredicate)
                    (Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated))
                        { predicate = makeCeilPredicate evaluated }
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqualWithExplanation "" expect actual
        ]
    ]
  where
    aSubSub = Mock.functional00SubSubSort
    xSub = ElementVariable $ Variable (testId "x") mempty Mock.subSort

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern =
    [ failure Mock.a Mock.b                 "no-var - no-var"
    , failure (mkElemVar Mock.x) Mock.a         "var - no-var"
    , failure Mock.a (mkElemVar Mock.x)         "no-var - var"
    , failure (mkElemVar Mock.x) (mkElemVar Mock.y) "no-var - var"
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
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkAnd (mkElemVar Mock.x) (Mock.constr20 Mock.cf (mkElemVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Application" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.plain20
                    (mkElemVar Mock.x)
                    (Mock.constr20 Mock.cf (mkElemVar Mock.y))
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
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkEquals_
                    (mkElemVar Mock.x)
                    (Mock.constr20 Mock.cf (mkElemVar Mock.y))
                )
                (mkEquals_ Mock.cf (Mock.constr20 Mock.cf Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIff (mkElemVar Mock.x) (Mock.constr20 Mock.cf (mkElemVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkImplies
                    (mkElemVar Mock.x)
                    (Mock.constr20 Mock.cf (mkElemVar Mock.y))
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
                       [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                       , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                       ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkIn_ (mkElemVar Mock.x) (Mock.constr20 Mock.cf (mkElemVar Mock.y)))
                (mkIn_    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkOr (mkElemVar Mock.x) (Mock.constr20 Mock.cf (mkElemVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cf    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (mkRewrites
                    (mkElemVar Mock.x)
                    (Mock.constr20 Mock.cg (mkElemVar Mock.y))
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
                (mkAnd (mkElemVar Mock.x) (mkElemVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkAnd (mkElemVar Mock.x) (mkElemVar Mock.x))
                (mkAnd (mkElemVar Mock.y) (Mock.f (mkElemVar Mock.y)))
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
                            [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f (mkElemVar Mock.x))
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
                            [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f Mock.cf)
            (Mock.f (mkElemVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "removes constructor" $ do
        let
            expect = Just
                (MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeCeilPredicate Mock.cf
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f (Mock.functionalConstr10 (mkElemVar Mock.x)))
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
                            (Mock.g (mkElemVar Mock.x))
                        , substitution = mempty
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.f Mock.a)
            (Mock.f (Mock.g (mkElemVar Mock.x)))
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
                                (Mock.g (mkElemVar Mock.x))
                            )
                            (makeCeilPredicate Mock.cf)
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.ElemVar Mock.y, Mock.cf)]
                        }
                    ]
                )
        actual <-
            unificationWithMatch
            (Mock.functional20 Mock.a Mock.cf)
            (Mock.functional20 (Mock.g (mkElemVar Mock.x)) (mkElemVar Mock.y))
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
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate (Mock.f Mock.b) Mock.b
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
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
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.b)
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
            (Mock.f (mkElemVar Mock.x))
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
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.a) Mock.a)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.a) Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.var_x_1, Mock.cg)
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
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.b)
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
                                            (Mock.g (mkElemVar Mock.z))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.z) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.g (mkElemVar Mock.z))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.z) Mock.b)
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
            (Mock.functionalConstr20 (mkElemVar Mock.x) (mkElemVar Mock.var_x_1))
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
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xBool, True)]
        actual <- matchVariable Mock.xBool True
        assertEqualWithExplanation "" expect actual
    , mkBool True  `notMatches` mkElemVar Mock.xBool  $ "true !~ x:Bool"
    , mkBool False `notMatches` mkElemVar Mock.xBool  $ "false !~ x:Bool"
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
        matchDefinition (mkElemVar var) (mkBool val)

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
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 1)]
        actual <- matchVariable Mock.xInt 1
        assertEqualWithExplanation "" expect actual
    , mkInt 1 `notMatches` mkElemVar Mock.xInt  $ "1 !~ x:Int"
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
        matchDefinition (mkElemVar var) (mkInt val)

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
        let expect =
                substitution [(UnifiedVariable.ElemVar Mock.xString, "str")]
        actual <- matchVariable Mock.xString "str"
        assertEqualWithExplanation "" expect actual
    , mkStr "str" `notMatches` mkElemVar Mock.xString  $ "\"str\" !~ x:String"
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
        matchDefinition (mkElemVar var) (mkStr val)

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
        actual <- matchDefinition (mkList [mkInt 1]) (mkElemVar Mock.xList)
        assertEqualWithExplanation "" expect actual
    , testCase "single variable" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 2)]
        actual <- matchVariable [Right 1, Left Mock.xInt] [1, 2]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables (simple)" $ do
        let expect = substitution
                [ (UnifiedVariable.ElemVar Mock.xInt, 1)
                , (UnifiedVariable.ElemVar Mock.yInt, 2)
                ]
        actual <- matchVariable
            [ Left Mock.xInt
            , Left Mock.yInt
            ]
            [ 1, 2 ]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables" $ do
        let expect =
                substitution
                    [ (UnifiedVariable.ElemVar Mock.xInt, 2)
                    , (UnifiedVariable.ElemVar Mock.yInt, 4)
                    ]
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
                            [ ( UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 1, mkInt 2, mkInt 3]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkList [] `concat'` mkElemVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(unit, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ ( UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 2, mkInt 3]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkInt 1] `concat'` mkElemVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(concrete, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (UnifiedVariable.ElemVar Mock.xList, mkList []) ]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkInt 1, mkInt 2, mkInt 3] `concat'` mkElemVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, empty) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ ( UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 1, mkInt 2, mkInt 3]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkElemVar Mock.xList `concat'` mkList [] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, unit) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 1, mkInt 2]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkElemVar Mock.xList `concat'` mkList [mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, concrete) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (UnifiedVariable.ElemVar Mock.xList, mkList [])
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkElemVar Mock.xList `concat'` mkList [mkInt 1, mkInt 2, mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(x, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (UnifiedVariable.ElemVar Mock.xInt, mkInt 1)
                            , ( UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 2, mkInt 3]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkElemVar Mock.xInt] `concat'` mkElemVar Mock.xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, x) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (UnifiedVariable.ElemVar Mock.xInt, mkInt 3)
                            , ( UnifiedVariable.ElemVar Mock.xList
                              , mkList [mkInt 1, mkInt 2]
                              )
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkElemVar Mock.xList `concat'` mkList [mkElemVar Mock.xInt])
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual

    , unitList               `notMatches` mkElemVar yList  $ "[] !~ y:List"
    , prefixList [one] xList `notMatches` mkElemVar yList  $ "[1] x:List !~ y:List"
    , suffixList xList [one] `notMatches` mkElemVar yList  $ "x:List [1] !~ y:List"

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
        (mkList [mkElemVar xInt])
        (mkList [one       ])
        [(UnifiedVariable.ElemVar xInt, one)]
    , mkList [one] `notMatches` prefixList [one] xList  $ "[1] !~ [1] x:List"
    , mkList [one] `notMatches` suffixList xList [one]  $ "[1] !~ x:List [1]"

    , prefixList [one] xList `notMatches` unitList      $ "[1] x:List !~ []"
    , matches "[1] x:List ~ [1]"
        (prefixList [one] xList)
        (mkList     [one]      )
        [(UnifiedVariable.ElemVar xList, unitList)]
    , matches "[x:Int] y:List ~ [1]"
        (prefixList [mkElemVar xInt] yList)
        (mkList     [one]             )
        [ (UnifiedVariable.ElemVar xInt, one)
        , (UnifiedVariable.ElemVar yList, unitList)
        ]
    , matches "[1] x:List ~ [1, 2]"
        (prefixList [one] xList)
        (mkList     [one, two ])
        [(UnifiedVariable.ElemVar xList, mkList [two])]
    , matches "[x:Int] y:List ~ [1, 2]"
        (prefixList [mkElemVar xInt] yList)
        (mkList     [one,        two ])
        [ (UnifiedVariable.ElemVar xInt, one)
        , (UnifiedVariable.ElemVar yList, mkList [two])
        ]

    , suffixList xList [one] `notMatches` unitList      $ "x:List [1] !~ []"
    , matches "x:List [1] ~ [1]"
        (suffixList xList [one])
        (mkList           [one])
        [(UnifiedVariable.ElemVar xList, unitList)]
    , matches "y:List [x:Int] ~ [1]"
        (suffixList yList [mkElemVar xInt])
        (mkList           [one       ])
        [ (UnifiedVariable.ElemVar xInt, one)
        , (UnifiedVariable.ElemVar yList, unitList)
        ]
    , matches "x:List [2] ~ [1, 2]"
        (suffixList xList [two])
        (mkList    [one,   two])
        [(UnifiedVariable.ElemVar xList, mkList [one])]
    , matches "y:List [x:Int] ~ [1, 2]"
        (suffixList yList [mkElemVar xInt])
        (mkList    [one,   two       ])
        [ (UnifiedVariable.ElemVar xInt, two)
        , (UnifiedVariable.ElemVar yList, mkList [one])
        ]
    ]
  where
    xInt = ElementVariable $ varS (testId "xInt") Mock.intSort
    xList = ElementVariable $ varS (testId "xList") Mock.listSort
    yList = ElementVariable $ varS (testId "yList") Mock.listSort
    one = mkInt 1
    two = mkInt 2
    unitList = mkList []
    prefixList elems frame = Mock.concatList (mkList elems) (mkElemVar frame)
    suffixList frame elems = Mock.concatList (mkElemVar frame) (mkList elems)
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
            (either mkElemVar mkInt <$> var)
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
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 1)]
        actual <- matchVariable [ElemVar Mock.xInt] [1]
        assertEqualWithExplanation "" expect actual
    , testCase "{elementVar, rest} vs {set}" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 2)]
        actual <-
            matchVariable [Concrete 1, Concrete 3, ElemVar Mock.xInt] [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "{elementVars, rest} vs {set}" $ do
        let expect =
                substitution
                    [ (UnifiedVariable.ElemVar Mock.xInt, 2)
                    , (UnifiedVariable.ElemVar Mock.yInt, 4)
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet []
                              )
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 1]
                              )
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 1, mkKey 2, mkKey 3]
                              )
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 2, mkKey 3]
                              )
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet []
                              )
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
                [ SetVar Mock.xSet
                , Concrete 1, Concrete 2, Concrete 3, Concrete 4
                ]
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet []
                              )
                            , (UnifiedVariable.ElemVar Mock.xInt, mkKey 1)
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 2, mkKey 3]
                              )
                            , (UnifiedVariable.ElemVar Mock.xInt, mkKey 1)
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 3]
                              )
                            , (UnifiedVariable.ElemVar Mock.xInt, mkKey 2)
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
                            [ ( UnifiedVariable.ElemVar Mock.xSet
                              , mkConcreteSet [mkKey 5]
                              )
                            , (UnifiedVariable.ElemVar Mock.xInt, mkKey 2)
                            , (UnifiedVariable.ElemVar Mock.yInt, mkKey 4)
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
                (mkElemVar <$> elemVars var)
                (mkElemVar <$> setVars  var)
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
        actual <-
            matchDefinition
                (mkConcreteMap [(mkKey 1, mkVal 11)])
                (mkElemVar Mock.xMap)
        assertEqualWithExplanation "" expect actual
    , testCase "single variable" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 12)]
        actual <- matchVariable
            [ (1, Right 11)
            , (2, Left Mock.xInt)
            ]
            [ (2, 12)
            , (1, 11)
            ]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables" $ do
        let expect =
                substitution
                    [ (UnifiedVariable.ElemVar Mock.xInt, 12)
                    , (UnifiedVariable.ElemVar Mock.yInt, 14)
                    ]
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
                            [ (UnifiedVariable.ElemVar Mock.xMap, mkConcreteMap
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
                            [ (UnifiedVariable.ElemVar Mock.xMap, mkConcreteMap
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
                            [ ( UnifiedVariable.ElemVar Mock.xMap
                              , mkConcreteMap []
                              )
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
        (framedMap [(mkElemVar kInt, mkElemVar vInt)] [mMap])
        (builtinMap [(zero, one)])
        [ (UnifiedVariable.ElemVar kInt, zero)
        , (UnifiedVariable.ElemVar vInt, one)
        , (UnifiedVariable.ElemVar mMap, unitMap)
        ]
    , matches "k |-> v m ~ 0 |-> 1 2 |-> 4"
        (framedMap [(mkElemVar kInt, mkElemVar vInt)] [mMap])
        (builtinMap [(zero, one), (two, four)])
        [ (UnifiedVariable.ElemVar kInt, zero)
        , (UnifiedVariable.ElemVar vInt, one)
        , (UnifiedVariable.ElemVar mMap, builtinMap [(two, four)])
        ]
    ]
  where
    framedMap = Mock.framedMap
    builtinMap = Mock.builtinMap
    mkInt = Int.asInternal Mock.intSort
    kInt = ElementVariable $ varS (testId "kInt") Mock.intSort
    vInt = ElementVariable $ varS (testId "vInt") Mock.intSort
    mMap = ElementVariable $ varS (testId "mMap") Mock.mapSort
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
            (mapWithKey (either mkElemVar mkVal) <$> var)
            (mapWithKey mkVal <$> val)
    matchBuiltin varComponents concreteElements =
        matchDefinition
            (mkMap
                (Bifunctor.bimap mkKey mkVal <$> concrete varComponents)
                (Bifunctor.bimap mkElemVar mkVal <$> elemVars varComponents)
                (mkElemVar <$> setVars  varComponents)
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
    -> [(UnifiedVariable.UnifiedVariable Variable, TermLike Variable)]
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
