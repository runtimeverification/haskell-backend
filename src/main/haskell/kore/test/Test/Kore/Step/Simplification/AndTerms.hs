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
                 ( BuiltinDomain (..), CommonPurePattern )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCharLiteral, mkDomainValue,
                 mkStringLiteral, mkTop, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Simplification.AndTerms
                 ( termAnd, termUnification )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification = give mockSymbolOrAliasSorts
    [ testCase "boolean and"
        (do
            assertEqualWithExplanation "pattern and top"
                (let
                    expected = Predicated
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
                    expected = Predicated
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
                expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                ( Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                ( ExpandedPattern.bottom, Just ExpandedPattern.bottom )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
                )
            assertEqualWithExplanation "different head subsort first"
                ( Predicated
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
                ( Predicated
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
            assertEqualWithExplanation
                "different head constructors common subsort"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                )
            assertEqualWithExplanation
                "different head constructors common subsort reversed"
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
                (simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                )
        )
    , testCase "constructor and"
        (do
            assertEqualWithExplanation "same head"
                (let
                    expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                    expected = Predicated
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
                    expanded = Predicated
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
                    expanded = Predicated
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
                ( Predicated
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
                ( Predicated
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
                ( Predicated
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
            ( Predicated
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
    , testCase "builtin Map domain"
        (do
            assertEqualWithExplanation "concrete Map, same keys"
                (Just Predicated
                    { term = Mock.builtinMap [(Mock.aConcrete, Mock.b)]
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    }
                )
                (unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                )
            assertEqualWithExplanation "concrete Map, different keys"
                (Just ExpandedPattern.bottom)
                (unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.bConcrete, mkVar Mock.x)])
                )
            assertEqualWithExplanation "concrete Map with framed Map"
                (Just Predicated
                    { term =
                        Mock.concatMap
                            (Mock.builtinMap [(Mock.aConcrete, fOfA)])
                            (Mock.builtinMap [(Mock.bConcrete, fOfB)])
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                )
                (unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, fOfA), (Mock.bConcrete, fOfB)])
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                        (mkVar Mock.m)
                    )
                )
            assertEqualWithExplanation "concrete Map with framed Map"
                (Just Predicated
                    { term =
                        Mock.concatMap
                            (Mock.builtinMap [(Mock.aConcrete, fOfA)])
                            (Mock.builtinMap [(Mock.bConcrete, fOfB)])
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                )
                (unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, fOfA), (Mock.bConcrete, fOfB)])
                    (Mock.concatMap
                        (mkVar Mock.m)
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    )
                )
            assertEqualWithExplanation "framed Map with concrete Map"
                (Just Predicated
                    { term =
                        Mock.concatMap
                            (Mock.builtinMap [(Mock.aConcrete, fOfA)])
                            (Mock.builtinMap [(Mock.bConcrete, fOfB)])
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                )
                (unify
                    mockMetadataTools
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                        (mkVar Mock.m)
                    )
                    (Mock.builtinMap [(Mock.aConcrete, fOfA), (Mock.bConcrete, fOfB)])
                )
            assertEqualWithExplanation "framed Map with concrete Map"
                (Just Predicated
                    { term =
                        Mock.concatMap
                            (Mock.builtinMap [(Mock.aConcrete, fOfA)])
                            (Mock.builtinMap [(Mock.bConcrete, fOfB)])
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                        , (Mock.x, fOfA)
                        ]
                    }
                )
                (unify
                    mockMetadataTools
                    (Mock.concatMap
                        (mkVar Mock.m)
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    )
                    (Mock.builtinMap [(Mock.aConcrete, fOfA), (Mock.bConcrete, fOfB)])
                )
        )
    , testCase "builtin List domain"
        (do
            let term1 = Mock.builtinList
                            [Mock.constr10 Mock.cf, Mock.constr11 Mock.cf]
            assertEqualWithExplanation "[same head, same head]"
                ( Just $ Predicated
                        { term = term1
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
                ( unify
                    mockMetadataTools
                        term1
                        term1
                )
            let term3 = Mock.builtinList $
                            [Mock.a, Mock.a]
            let term4 = Mock.builtinList $
                            [Mock.a, Mock.b]
            assertEqualWithExplanation "[same head, different head]"
                ( Just $ ExpandedPattern.bottom
                )
                ( unify
                    mockMetadataTools
                    term3
                    term4
                )
            let term5 = Mock.concatList
                        (Mock.builtinList [Mock.constr10 Mock.cf])
                        (mkVar Mock.x)
            let term6 = Mock.builtinList $ [Mock.constr10 Mock.cf, Mock.constr11 Mock.cf]
            assertEqualWithExplanation "[a] `concat` x /\\ [a, b] "
                ( Just $ Predicated
                        { term = Mock.builtinList[Mock.constr10 Mock.cf, Mock.constr11 Mock.cf]
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.x, Mock.builtinList [Mock.constr11 Mock.cf])]
                        }
                )
                ( unify
                    mockMetadataTools
                    term5
                    term6
                )
            let term7 = Mock.builtinList [Mock.a, Mock.a]
            let term8 = Mock.builtinList [Mock.a]
            assertEqualWithExplanation "different lengths"
                ( Just ExpandedPattern.bottom
                )
                ( unify
                    mockMetadataTools
                    term7
                    term8
                )

        )
    ]

fOfA :: CommonPurePattern Object
fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a

fOfB :: CommonPurePattern Object
fOfB = give mockSymbolOrAliasSorts $ Mock.f Mock.b

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
    case unification of
        Nothing -> Nothing
        Just result -> Just $ fst $ evalSimplifier result
  where
    unification =
        termUnification tools (Mock.substitutionSimplifier tools) first second

simplify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonExpandedPattern level
simplify tools first second =
    fst $ evalSimplifier
        (termAnd tools (Mock.substitutionSimplifier tools) first second)
