module Test.Kore.Step.Simplification.AndTerms
    ( test_andTermsSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( CharLiteral (..), StringLiteral (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCharLiteral, mkDomainValue,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SortTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom )
import           Kore.Step.Simplification.AndTerms
                 ( termAnd, termUnification )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Variables.Fresh.IntCounter
                 ( runIntCounter )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification = give mockSortTools
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
                ( ExpandedPattern
                    { term = Mock.injective10 (mkAnd fOfA gOfA)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
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
                ( ExpandedPattern
                    { term =
                        Mock.sortInjection10
                            (mkAnd Mock.cfSort0 Mock.cgSort0)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
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
            assertEqualWithExplanation "different head"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection11 Mock.cfSort1)
                )
        )
    , testCase "constructor and"
        (do
            assertEqualWithExplanation "same head"
                (ExpandedPattern
                        { term = Mock.constr10 (mkAnd Mock.cf Mock.cg)
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                , Nothing
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
    , give mockMetaSortTools $ testCase "string literal and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expected = ExpandedPattern
                        { term = mkStringLiteral (StringLiteral "a")
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral (StringLiteral "a"))
                    (mkStringLiteral (StringLiteral "a"))
                )
            assertEqualWithExplanation "different values"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral (StringLiteral "a"))
                    (mkStringLiteral (StringLiteral "b"))
                )
        )
    , give mockMetaSortTools $ testCase "char literal and"
        (do
            assertEqualWithExplanation "equal values"
                (let
                    expected = ExpandedPattern
                        { term = mkCharLiteral (CharLiteral 'a')
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                  in (expected, Just expected)
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral (CharLiteral 'a'))
                    (mkCharLiteral (CharLiteral 'a'))
                )
            assertEqualWithExplanation "different values"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral (CharLiteral 'a'))
                    (mkCharLiteral (CharLiteral 'b'))
                )
        )
    , testCase "unhandled cases"
        (do
            assertEqualWithExplanation "top level"
                ( ExpandedPattern
                    { term = mkAnd fOfA gOfA
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    fOfA gOfA
                )
            assertEqualWithExplanation "one level deep"
                ( ExpandedPattern
                    { term = Mock.constr10 (mkAnd fOfA gOfA)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 fOfA) (Mock.constr10 gOfA)
                )
            assertEqualWithExplanation "two levels deep"
                ( ExpandedPattern
                    { term = Mock.constr10 (Mock.constr10 (mkAnd fOfA gOfA))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Nothing
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 (Mock.constr10 fOfA))
                    (Mock.constr10 (Mock.constr10 gOfA))
                )
        )
    , testCase "funct-constr(f(a), f(b)) vs funct-constr(g(a), g(b))"
        (assertEqualWithExplanation ""
            ( ExpandedPattern
                { term =
                    Mock.functionalConstr20 (mkAnd fOfA gOfA) (mkAnd fOfB gOfB)
                , predicate = makeTruePredicate
                , substitution = []
                }
            , Nothing
            )
            (simplifyUnify
                mockMetadataTools
                (Mock.functionalConstr20 fOfA fOfB)
                (Mock.functionalConstr20 gOfA gOfB)
            )
        )
    ]

fOfA :: CommonPurePattern Object
fOfA = give mockSortTools $ Mock.f Mock.a

fOfB :: CommonPurePattern Object
fOfB = give mockSortTools $ Mock.f Mock.b

gOfA :: CommonPurePattern Object
gOfA = give mockSortTools $ Mock.g Mock.a

gOfB :: CommonPurePattern Object
gOfB = give mockSortTools $ Mock.g Mock.b

mockSortTools :: SortTools Object
mockSortTools = Mock.makeSortTools Mock.sortToolsMapping

mockMetaSortTools :: SortTools Meta
mockMetaSortTools = Mock.makeSortTools []

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSortTools Mock.attributesMapping

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools =
    Mock.makeMetadataTools mockMetaSortTools []

aDomainValue :: CommonPurePattern Object
aDomainValue =
    give mockSortTools $ mkDomainValue
        Mock.testSort
        (mkStringLiteral (StringLiteral "a"))

bDomainValue :: CommonPurePattern Object
bDomainValue =
    give mockSortTools $ mkDomainValue
        Mock.testSort
        (mkStringLiteral (StringLiteral "b"))

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
        Just result -> Just $ fst $ fst $ runIntCounter result 0

simplify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonExpandedPattern level
simplify tools first second =
    fst $ fst $ runIntCounter (termAnd tools first second) 0

