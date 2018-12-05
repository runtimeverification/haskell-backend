module Test.Kore.Step.Simplification.And
    ( test_andSimplification
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( And (..), Sort (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( getSort, mkAnd, mkBottom, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.And
                 ( makeEvaluate, simplify )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andSimplification :: [TestTree]
test_andSimplification = give mockSymbolOrAliasSorts
    [ testCase "And truth table" $ do
        assertEqualWithExplanation "false and false = false"
            (OrOfExpandedPattern.make [])
            =<< evaluate (makeAnd [] [])
        assertEqualWithExplanation "false and true = false"
            (OrOfExpandedPattern.make [])
            =<< evaluate (makeAnd [] [ExpandedPattern.top])
        assertEqualWithExplanation "true and false = false"
            (OrOfExpandedPattern.make [])
            =<< evaluate (makeAnd [ExpandedPattern.top] [])
        assertEqualWithExplanation "true and true = true"
            (OrOfExpandedPattern.make [ExpandedPattern.top])
            =<< evaluate (makeAnd [ExpandedPattern.top] [ExpandedPattern.top])

    , testCase "And with booleans" $ do
        assertEqualWithExplanation "false and something = false"
            (OrOfExpandedPattern.make [])
            =<< evaluate (makeAnd [] [fOfXExpanded])
        assertEqualWithExplanation "something and false = false"
            (OrOfExpandedPattern.make [])
            =<< evaluate (makeAnd [fOfXExpanded] [])
        assertEqualWithExplanation "true and something = something"
            (OrOfExpandedPattern.make [fOfXExpanded])
            =<< evaluate (makeAnd [ExpandedPattern.top] [fOfXExpanded])
        assertEqualWithExplanation "something and true = something"
            (OrOfExpandedPattern.make [fOfXExpanded])
            =<< evaluate (makeAnd [fOfXExpanded] [ExpandedPattern.top])

    , testCase "And with partial booleans" $ do
        assertEqualWithExplanation "false term and something = false"
            ExpandedPattern.bottom
            =<< evaluatePatterns bottomTerm fOfXExpanded
        assertEqualWithExplanation "something and false term = false"
            ExpandedPattern.bottom
            =<< evaluatePatterns fOfXExpanded bottomTerm
        assertEqualWithExplanation "false predicate and something = false"
            ExpandedPattern.bottom
            =<< evaluatePatterns falsePredicate fOfXExpanded
        assertEqualWithExplanation "something and false predicate = false"
            ExpandedPattern.bottom
            =<< evaluatePatterns fOfXExpanded falsePredicate

    , testGroup "And with normal patterns"
        [ testCase "And random terms" $ do
            let expect =
                    Predicated
                        { term = mkAnd plain0OfX plain1OfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- evaluatePatterns plain0OfXExpanded plain1OfXExpanded
            assertEqualWithExplanation "" expect actual

        , testCase "And function terms" $ do
            let expect =
                    Predicated
                        { term = fOfX
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
            actual <- evaluatePatterns fOfXExpanded gOfXExpanded
            assertEqualWithExplanation "" expect actual

        , testCase "And predicates" $ do
            let expect =
                    Predicated
                        { term = mkTop
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
            assertEqualWithExplanation "" expect actual

        , testCase "And substitutions - simple" $ do
            let expect =
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfX), (Mock.z, gOfX)]
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.y, fOfX)]
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.z, gOfX)]
                        }
            assertEqualWithExplanation "" expect actual

        , testCase "And substitutions - multiple terms" $ do
            let
                expect =
                    Predicated
                        { term = mkAnd (mkAnd Mock.a Mock.b) Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- evaluatePatterns
                Predicated
                    { term = mkAnd Mock.a Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                Predicated
                    { term = mkAnd Mock.b Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            assertEqualWithExplanation "" expect actual

        , testCase "And substitutions - separate predicate" $ do
            let
                expect =
                    Predicated
                        { term = mkTop
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution =
                            Substitution.unsafeWrap [(Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns
                Predicated
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, fOfX)]
                    }
                Predicated
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, gOfX)]
                    }
            assertEqualWithExplanation "" expect actual

        , testCase "And substitutions - failure" $ do
            let expect =
                    Predicated
                        { term = mkTop
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [   ( Mock.y
                                , Mock.functionalConstr10 (mkVar Mock.x)
                                )
                            ]
                        }
                    Predicated
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [   ( Mock.y
                                , Mock.functionalConstr11 (mkVar Mock.x)
                                )
                            ]
                        }
            assertEqualWithExplanation "" expect actual
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation
                "Combines conditions with substitution merge condition"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ makeAndPredicate
                            (fst $ makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                            )
                            (givemakeEqualsPredicate fOfX gOfX)
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, mock.functionAttributes)
                    , (gSymbol, mock.functionAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
        ]
    , testGroup "Variable-function and"
        [ testCase "variable-term" $ do
            let expect =
                    Predicated
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns yExpanded fOfXExpanded
            assertEqualWithExplanation "" expect actual

        , testCase "term-variable" $ do
            let expect =
                    Predicated
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns fOfXExpanded yExpanded
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "constructor and"
        [ testCase "same constructors" $ do
            let expect =
                    Predicated
                        { term = Mock.constr10 fOfX
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Predicated
                        { term = Mock.constr10 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = ExpandedPattern.bottom
            actual <-
                evaluatePatterns
                    Predicated
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Predicated
                        { term = Mock.constr11 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqualWithExplanation "" expect actual
        ]

    -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
    , testCase "And-Or distribution" $ do
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = fOfX
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
                    , Predicated
                        { term = fOfX
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    , Predicated
                        { term = gOfX
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    , Predicated
                        { term = mkTop
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                (makeAnd
                    [ fOfXExpanded
                    , Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    ]
                    [ gOfXExpanded
                    , Predicated
                        { term = mkTop
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    ]
                )
        assertEqualWithExplanation "Distributes or" expect actual
    ]
  where
    yExpanded = Predicated
        { term = give mockSymbolOrAliasSorts $ mkVar Mock.y
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    fOfX = give mockSymbolOrAliasSorts $ Mock.f (mkVar Mock.x)
    fOfXExpanded = Predicated
        { term = fOfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    gOfX = give mockSymbolOrAliasSorts $ Mock.g (mkVar Mock.x)
    gOfXExpanded = Predicated
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain0OfX = give mockSymbolOrAliasSorts $ Mock.plain10 (mkVar Mock.x)
    plain0OfXExpanded = Predicated
        { term = plain0OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain1OfX = give mockSymbolOrAliasSorts $ Mock.plain11 (mkVar Mock.x)
    plain1OfXExpanded = Predicated
        { term = plain1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    bottomTerm = Predicated
        { term = mkBottom
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    falsePredicate = Predicated
        { term = mkTop
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

makeAnd
    :: [CommonExpandedPattern Object]
    -> [CommonExpandedPattern Object]
    -> And Object (CommonOrOfExpandedPattern Object)
makeAnd first second =
    And
        { andSort = findSort (first ++ second)
        , andFirst = OrOfExpandedPattern.make first
        , andSecond = OrOfExpandedPattern.make second
        }

findSort :: [CommonExpandedPattern Object] -> Sort Object
findSort [] = testSort
findSort
    ( Predicated {term} : _ )
  =
    give mockSymbolOrAliasSorts $ getSort term

evaluate
    :: And Object (CommonOrOfExpandedPattern Object)
    -> IO (CommonOrOfExpandedPattern Object)
evaluate patt =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ simplify
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        patt

evaluatePatterns
    :: CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> IO (CommonExpandedPattern Object)
evaluatePatterns first second =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ makeEvaluate
            mockMetadataTools
            (Mock.substitutionSimplifier mockMetadataTools)
            first
            second

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts =
    Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        mockSymbolOrAliasSorts
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.subsorts

testSort :: forall level. MetaOrObject level => Sort level
testSort =
    case mkBottom :: CommonStepPattern level of
        Bottom_ sort -> sort
        _ -> error "unexpected"
