module Test.Kore.Step.Simplification.AndTerms
    ( test_andTermsSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Control.Monad.Counter
import           Kore.AST.Common
                 ( BuiltinDomain (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCharLiteral, mkDomainValue,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom )
import           Kore.Step.Simplification.AndTerms
                 ( termAnd, termUnification )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification = give mockSymbolOrAliasSorts
    [ testCase "boolean and"
        (do
            assertEqualWithExplanation "pattern and top"
                (let
                    expected = ExpandedPattern
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA mkTop
                )
            assertEqualWithExplanation "top and pattern"
                (let
                    expected = ExpandedPattern
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    mkTop fOfA
                )
            assertEqualWithExplanation "pattern and bottom"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA mkBottom
                )
            assertEqualWithExplanation "bottom and pattern"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    mkBottom fOfA
                )
        )
    , testCase "equal patterns and"
        (assertEqualWithExplanation ""
            (let
                expected = ExpandedPattern
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
              in (expected, Just expected)
            )
            (simplifyUnify
                mockMetadataTools
                fOfA fOfA
            )
        )
    , testCase "variable function and"
        (do
            assertEqualWithExplanation ""
                (let
                    expected = ExpandedPattern
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.x, fOfA)]
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (mkVar Mock.x) fOfA
                )
            assertEqualWithExplanation ""
                (let
                    expected = ExpandedPattern
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.x, fOfA)]
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA (mkVar Mock.x)
                )
        )
    , testCase "injective head and"
        (do
            assertEqualWithExplanation "same head"
                (let
                    expected = ExpandedPattern
                        { term = Mock.injective10 fOfA
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 gOfA)
                )
            assertEqualWithExplanation "same head same child"
                (let
                    expected = ExpandedPattern
                        { term = Mock.injective10 fOfA
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 fOfA)
                )
            assertEqualWithExplanation "different head"
                ( ExpandedPattern
                    { term =
                        mkAnd
                            (Mock.injective10 fOfA)
                            (Mock.injective11 gOfA)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective11 gOfA)
                )
        )
    , testCase "sortInjection and"
        (do
            assertEqualWithExplanation "same head"
                (let
                    expected = ExpandedPattern
                        { term = Mock.sortInjection10 Mock.cfSort0
                        , predicate =
                            makeEqualsPredicate Mock.cfSort0 Mock.cgSort0
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cgSort0)
                )
            assertEqualWithExplanation "same head same child"
                (let
                    expected = ExpandedPattern
                        { term =
                            Mock.sortInjection10 Mock.cfSort0
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cfSort0)
                )
            assertEqualWithExplanation "different head not subsort"
                ( ExpandedPattern
                    { term =
                        mkAnd
                            (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                            (Mock.sortInjection0ToTop Mock.plain00Sort0)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
                )
            assertEqualWithExplanation "different head subsort first"
                ( ExpandedPattern
                    { term =
                        Mock.sortInjectionSubToTop
                            (mkAnd
                                (Mock.sortInjectionSubSubToSub
                                    Mock.plain00SubSubsort
                                )
                                Mock.plain00Subsort
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                )
            assertEqualWithExplanation "different head subsort second"
                ( ExpandedPattern
                    { term =
                        Mock.sortInjectionSubToTop
                            (mkAnd
                                Mock.plain00Subsort
                                (Mock.sortInjectionSubSubToSub
                                    Mock.plain00SubSubsort
                                )
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                )
            assertEqualWithExplanation "different head constructors not subsort"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.aSort0)
                    (Mock.sortInjection11 Mock.aSort1)
                )
            assertEqualWithExplanation "different head constructors subsort"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
                )
        )
    , testCase "constructor and"
        (do
            assertEqualWithExplanation "same head"
                (let
                    expected = ExpandedPattern
                        { term = Mock.constr10 Mock.cf
                        , predicate = makeEqualsPredicate Mock.cf Mock.cg
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cg)
                )
            assertEqualWithExplanation "same head same child"
                (let
                    expected = ExpandedPattern
                        { term = Mock.constr10 Mock.cf
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cf)
                )
            assertEqualWithExplanation "different head"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr11 Mock.cf)
                )
        )
    , testCase "constructor-sortinjection and"
        (assertEqualWithExplanation ""
            ( ExpandedPattern.bottom
            , Just ExpandedPattern.bottom
            )
            (simplifyUnify
                mockMetadataTools
                (Mock.constr10 Mock.cf)
                (Mock.sortInjection11 Mock.cfSort1)
            )
        )
    , testCase "domain value and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expected = ExpandedPattern
                        { term = aDomainValue
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetadataTools
                    aDomainValue aDomainValue
                )
            assertEqualWithExplanation "different values"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    aDomainValue bDomainValue
                )
        )
    , give mockMetaSymbolOrAliasSorts $ testCase "string literal and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expected = ExpandedPattern
                        { term = mkStringLiteral "a"
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "a")
                )
            assertEqualWithExplanation "different values"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "b")
                )
        )
    , give mockMetaSymbolOrAliasSorts $ testCase "char literal and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expected = ExpandedPattern
                        { term = mkCharLiteral 'a'
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'a')
                )
            assertEqualWithExplanation "different values"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'b')
                )
        )
    , testCase "function and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expanded = ExpandedPattern
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expanded, Just expanded)
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA fOfA
                )
            assertEqualWithExplanation "not equal values"
                (let
                    expanded = ExpandedPattern
                        { term = fOfA
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = []
                        }
                  in (expanded, Just expanded)
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA gOfA
                )
        )
    , testCase "unhandled cases"
        (do
            assertEqualWithExplanation "top level"
                ( ExpandedPattern
                    { term = mkAnd plain0OfA plain1OfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    plain0OfA plain1OfA
                )
            assertEqualWithExplanation "one level deep"
                ( ExpandedPattern
                    { term = Mock.constr10 (mkAnd plain0OfA plain1OfA)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 plain0OfA) (Mock.constr10 plain1OfA)
                )
            assertEqualWithExplanation "two levels deep"
                ( ExpandedPattern
                    { term =
                        Mock.constr10
                            (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 (Mock.constr10 plain0OfA))
                    (Mock.constr10 (Mock.constr10 plain1OfA))
                )
        )
    , testCase "binary constructor of non-specialcased values"
        (assertEqualWithExplanation ""
            ( ExpandedPattern
                { term =
                    Mock.functionalConstr20
                        (mkAnd plain0OfA plain1OfA) (mkAnd plain0OfB plain1OfB)
                , predicate = makeTruePredicate
                , substitution = []
                }
            , Nothing
            )
            (simplifyUnify
                mockMetadataTools
                (Mock.functionalConstr20 plain0OfA plain0OfB)
                (Mock.functionalConstr20 plain1OfA plain1OfB)
            )
        )
    ]

fOfA :: CommonPurePattern Object
fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a

gOfA :: CommonPurePattern Object
gOfA = give mockSymbolOrAliasSorts $ Mock.g Mock.a

plain0OfA :: CommonPurePattern Object
plain0OfA = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.a

plain1OfA :: CommonPurePattern Object
plain1OfA = give mockSymbolOrAliasSorts $ Mock.plain11 Mock.a

plain0OfB :: CommonPurePattern Object
plain0OfB = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.b

plain1OfB :: CommonPurePattern Object
plain1OfB = give mockSymbolOrAliasSorts $ Mock.plain11 Mock.b

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

mockMetaSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockMetaSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSymbolOrAliasSorts Mock.attributesMapping Mock.subsorts

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools =
    Mock.makeMetadataTools mockMetaSymbolOrAliasSorts [] []

aDomainValue :: CommonPurePattern Object
aDomainValue =
    give mockSymbolOrAliasSorts
        $ mkDomainValue  Mock.testSort
        $ BuiltinDomainPattern (mkStringLiteral "a")

bDomainValue :: CommonPurePattern Object
bDomainValue =
    give mockSymbolOrAliasSorts
        $ mkDomainValue Mock.testSort
        $ BuiltinDomainPattern (mkStringLiteral "b")

simplifyUnify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> (CommonExpandedPattern level, Maybe (CommonExpandedPattern level))
simplifyUnify tools first second =
    (simplify tools first second, unify tools first second)


unify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> Maybe (CommonExpandedPattern level)
unify tools first second =
    case termUnification tools first second of
        Nothing -> Nothing
        Just result -> Just $ fst $ evalCounter result

simplify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonExpandedPattern level
simplify tools first second =
    fst $ evalCounter (termAnd tools first second)
