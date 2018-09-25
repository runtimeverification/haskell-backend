module Test.Kore.Step.Function.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Control.Monad.Counter
                 ( runCounter )
import           Kore.AST.Common
                 ( BuiltinDomain (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCeil, mkCharLiteral, mkDomainValue,
                 mkEquals, mkExists, mkFloor, mkForall, mkIff, mkImplies, mkIn,
                 mkNext, mkNot, mkOr, mkRewrites, mkStringLiteral, mkTop,
                 mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonPredicateSubstitution,
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Function.Matcher
                 ( matchAsUnification )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads = give mockSortTools
    [ testCase "And"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkAnd (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Application"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (Mock.plain10 (mkVar Mock.x))
                (Mock.plain10 Mock.a)
            )
        )
    , testCase "Application different constructors"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (Mock.constr10 (mkVar Mock.x))
                (Mock.constr11 Mock.a)
            )
        )
    , testCase "Application different functions"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (Mock.f (mkVar Mock.x))
                (Mock.g Mock.a)
            )
        )
    , testCase "Application different symbols"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (Mock.plain10 (mkVar Mock.x))
                (Mock.plain11 Mock.a)
            )
        )
    , testCase "Bottom"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetadataTools
                mkBottom
                mkBottom
            )
        )
    , testCase "Ceil"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkCeil (Mock.plain10 (mkVar Mock.x)))
                (mkCeil (Mock.plain10 Mock.a))
            )
        )
    , testCase "CharLiteral"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetaMetadataTools
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
            )
        )
    , testCase "DomainValue"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetadataTools
                (mkDomainValue Mock.testSort1
                    (BuiltinDomainPattern  (mkStringLiteral "10"))
                )
                (mkDomainValue Mock.testSort1
                    (BuiltinDomainPattern (mkStringLiteral "10"))
                )
            )
        )
    , testCase "Equals"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkEquals (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkEquals (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Exists"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.y, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
            )
        )
    , testCase "Floor"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkFloor (Mock.plain10 (mkVar Mock.x)))
                (mkFloor (Mock.plain10 Mock.a))
            )
        )
    , testCase "Forall"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.y, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkForall Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
            )
        )
    , testCase "Iff"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Implies"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkImplies (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "In"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkIn (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIn (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Next"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkNext (Mock.plain10 (mkVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
            )
        )
    , testCase "Not"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkNot (Mock.plain10 (mkVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
            )
        )
    , testCase "Or"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkOr (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Rewrites"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkRewrites (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkRewrites (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "StringLiteral"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetaMetadataTools
                (mkStringLiteral "10")
                (mkStringLiteral "10")
            )
        )
    , testCase "Top"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetadataTools
                mkTop
                mkTop
            )
        )
    , testCase "Variable (quantified)"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = []
                }
            )
            (match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkVar Mock.y)))
            )
        )
    , testCase "Iff vs Or"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
            )
        )
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction = give mockSortTools
    [ testCase "Functional"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.functional00)]
                }
            )
            (match mockMetadataTools
                (mkVar Mock.x)
                Mock.functional00
            )
        )
    , testCase "Function"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeCeilPredicate Mock.cf
                , substitution = [(Mock.x, Mock.cf)]
                }
            )
            (match mockMetadataTools
                (mkVar Mock.x)
                Mock.cf
            )
        )
    , testCase "Non-functional"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (mkVar Mock.x)
                (Mock.constr10 Mock.cf)
            )
        )
    , testCase "Unidirectional"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (Mock.functional10 (mkVar Mock.y))
                (mkVar Mock.x)
            )
        )
    , testCase "Quantified" $ do
        assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkVar Mock.z)))
            )
        assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a Mock.a))
            )
    ]

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern = give mockSortTools
    [ testCase "no-var - no-var"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeEqualsPredicate
                    (Mock.plain10 Mock.a) (Mock.plain11 Mock.b)
                , substitution = []
                }
            )
            (match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 Mock.b)
            )
        )
    , testCase "var - no-var"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 Mock.b)
            )
        )
    , testCase "no-var - var"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeEqualsPredicate
                    (Mock.plain10 Mock.a) (Mock.plain11 (mkVar Mock.x))
                , substitution = []
                }
            )
            (match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 (mkVar Mock.x))
            )
        )
    , testCase "var - var"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 (mkVar Mock.y))
            )
        )
    ]

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults = give mockSortTools
    [ testCase "And"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkAnd (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Application"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (Mock.plain20
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cg Mock.b)
                )
            )
        )
    , testCase "Equals"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkEquals (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkEquals    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Iff"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkIff (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Implies"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkImplies
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkImplies
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
            )
        )
    , testCase "In"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkIn (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIn    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Or"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkOr (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Rewrites"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate =
                    fst $ makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkRewrites
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkRewrites
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
            )
        )
    , testCase "Merge conflict"
        (assertEqualWithExplanation ""
            (Just PredicateSubstitution
                { predicate = makeFalsePredicate
                , substitution = []
                }
            )
            (match mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
            )
        )
    ]


mockSortTools :: SortTools Object
mockSortTools = Mock.makeSortTools Mock.sortToolsMapping
mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSortTools Mock.attributesMapping

mockMetaSortTools :: SortTools Meta
mockMetaSortTools = Mock.makeSortTools []
mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools = Mock.makeMetadataTools mockMetaSortTools []


match
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> Maybe (CommonPredicateSubstitution level)
match tools first second =
    case matchAsUnification tools first second of
        Left _err -> Nothing
        Right result -> Just $ fst $ fst $ runCounter result 0
