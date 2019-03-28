module Test.Kore.Step.Simplification.And
    ( test_andSimplification
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr (MultiOr) )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import           Kore.Step.Simplification.And
                 ( makeEvaluate, simplify )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier, gather )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andSimplification :: [TestTree]
test_andSimplification =
    [ testCase "And truth table" $ do
        assertEqualWithExplanation "false and false = false"
            (MultiOr.make [])
            =<< evaluate (makeAnd [] [])
        assertEqualWithExplanation "false and true = false"
            (MultiOr.make [])
            =<< evaluate (makeAnd [] [ExpandedPattern.top])
        assertEqualWithExplanation "true and false = false"
            (MultiOr.make [])
            =<< evaluate (makeAnd [ExpandedPattern.top] [])
        assertEqualWithExplanation "true and true = true"
            (MultiOr.make [ExpandedPattern.top])
            =<< evaluate (makeAnd [ExpandedPattern.top] [ExpandedPattern.top])

    , testCase "And with booleans" $ do
        assertEqualWithExplanation "false and something = false"
            (MultiOr.make [])
            =<< evaluate (makeAnd [] [fOfXExpanded])
        assertEqualWithExplanation "something and false = false"
            (MultiOr.make [])
            =<< evaluate (makeAnd [fOfXExpanded] [])
        assertEqualWithExplanation "true and something = something"
            (MultiOr.make [fOfXExpanded])
            =<< evaluate (makeAnd [ExpandedPattern.top] [fOfXExpanded])
        assertEqualWithExplanation "something and true = something"
            (MultiOr.make [fOfXExpanded])
            =<< evaluate (makeAnd [fOfXExpanded] [ExpandedPattern.top])

    , testCase "And with partial booleans" $ do
        assertEqualWithExplanation "false term and something = false"
            mempty
            =<< evaluatePatterns bottomTerm fOfXExpanded
        assertEqualWithExplanation "something and false term = false"
            mempty
            =<< evaluatePatterns fOfXExpanded bottomTerm
        assertEqualWithExplanation "false predicate and something = false"
            mempty
            =<< evaluatePatterns falsePredicate fOfXExpanded
        assertEqualWithExplanation "something and false predicate = false"
            mempty
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
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "And function terms" $ do
            let expect =
                    Predicated
                        { term = fOfX
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
            actual <- evaluatePatterns fOfXExpanded gOfXExpanded
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "And predicates" $ do
            let expect =
                    Predicated
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    Predicated
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "And substitutions - simple" $ do
            let expect =
                    Predicated
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfX), (Mock.z, gOfX)]
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.y, fOfX)]
                        }
                    Predicated
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.z, gOfX)]
                        }
            assertEqualWithExplanation "" (MultiOr [expect]) actual

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
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "And substitutions - separate predicate" $ do
            let
                expect =
                    Predicated
                        { term = mkTop_
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution =
                            Substitution.unsafeWrap [(Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns
                Predicated
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, fOfX)]
                    }
                Predicated
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, gOfX)]
                    }
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "And substitutions - failure" $ do
            let expect =
                    Predicated
                        { term = mkTop_
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Predicated
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [   ( Mock.y
                                , Mock.functionalConstr10 (mkVar Mock.x)
                                )
                            ]
                        }
                    Predicated
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [   ( Mock.y
                                , Mock.functionalConstr11 (mkVar Mock.x)
                                )
                            ]
                        }
            assertEqualWithExplanation "" (MultiOr [expect]) actual
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation
                "Combines conditions with substitution merge condition"
                ExpandedPattern
                    { term = mkTop_
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
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop_
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
            assertEqualWithExplanation "" (MultiOr [expect]) actual

        , testCase "term-variable" $ do
            let expect =
                    Predicated
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns fOfXExpanded yExpanded
            assertEqualWithExplanation "" (MultiOr [expect]) actual
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
            assertEqualWithExplanation "" (MultiOr [expect]) actual

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
            assertEqualWithExplanation "" (MultiOr [expect]) actual
        ]

    -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
    , testCase "And-Or distribution" $ do
        let expect =
                MultiOr.make
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
                        { term = mkTop_
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
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    ]
                    [ gOfXExpanded
                    , Predicated
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    ]
                )
        assertEqualWithExplanation "Distributes or" expect actual
    ]
  where
    yExpanded = Predicated
        { term = mkVar Mock.y
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    fOfX = Mock.f (mkVar Mock.x)
    fOfXExpanded = Predicated
        { term = fOfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    gOfX = Mock.g (mkVar Mock.x)
    gOfXExpanded = Predicated
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain0OfX = Mock.plain10 (mkVar Mock.x)
    plain0OfXExpanded = Predicated
        { term = plain0OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain1OfX = Mock.plain11 (mkVar Mock.x)
    plain1OfXExpanded = Predicated
        { term = plain1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    bottomTerm = Predicated
        { term = mkBottom_
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    falsePredicate = Predicated
        { term = mkTop_
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
        , andFirst = MultiOr.make first
        , andSecond = MultiOr.make second
        }

findSort :: [CommonExpandedPattern Object] -> Sort Object
findSort [] = testSort
findSort ( Predicated {term} : _ ) = getSort term

evaluate
    :: And Object (CommonOrOfExpandedPattern Object)
    -> IO (CommonOrOfExpandedPattern Object)
evaluate patt =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ simplify
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        patt

evaluatePatterns
    :: CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
evaluatePatterns first second =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ gather
    $ makeEvaluate
            mockMetadataTools
            (Mock.substitutionSimplifier mockMetadataTools)
            (Simplifier.create mockMetadataTools Map.empty)
            Map.empty
            first
            second

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
