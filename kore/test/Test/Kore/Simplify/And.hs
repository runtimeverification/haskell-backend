module Test.Kore.Simplify.And (
    test_andSimplification,
) where

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeFalsePredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.And
import qualified Kore.Simplify.Not as Not
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_andSimplification :: [TestTree]
test_andSimplification =
    [ testCase "And truth table" $ do
        assertEqual
            "false and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [])
        assertEqual
            "false and true = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [Pattern.top])
        assertEqual
            "true and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [Pattern.top] [])
        assertEqual
            "true and true = true"
            OrPattern.top
            =<< evaluate (makeAnd [Pattern.top] [Pattern.top])
    , testCase "And with booleans" $ do
        assertEqual
            "false and something = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [fOfXExpanded])
        assertEqual
            "something and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [fOfXExpanded] [])
        assertEqual
            "true and something = something"
            (OrPattern.fromPatterns [fOfXExpanded])
            =<< evaluate (makeAnd [Pattern.top] [fOfXExpanded])
        assertEqual
            "something and true = something"
            (OrPattern.fromPatterns [fOfXExpanded])
            =<< evaluate (makeAnd [fOfXExpanded] [Pattern.top])
    , testCase "And with partial booleans" $ do
        assertEqual
            "false term and something = false"
            mempty
            =<< evaluatePatterns bottomTerm fOfXExpanded
        assertEqual
            "something and false term = false"
            mempty
            =<< evaluatePatterns fOfXExpanded bottomTerm
        assertEqual
            "false predicate and something = false"
            mempty
            =<< evaluatePatterns falsePredicate fOfXExpanded
        assertEqual
            "something and false predicate = false"
            mempty
            =<< evaluatePatterns fOfXExpanded falsePredicate
    , testGroup
        "And with normal patterns"
        [ testCase "And random terms" $ do
            let expect =
                    Conditional
                        { term = mkAnd plain0OfX plain1OfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- evaluatePatterns plain0OfXExpanded plain1OfXExpanded
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And function terms" $ do
            let expect =
                    makeEqualsPredicate fOfX gOfX
                        & Condition.fromPredicate
                        & Pattern.withCondition fOfX
            actual <- evaluatePatterns fOfXExpanded gOfXExpanded
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And predicates" $ do
            let expect =
                    Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And substitutions - simple" $ do
            let expect =
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject Mock.yConfig, fOfX)
                                , (inject Mock.zConfig, gOfX)
                                ]
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.yConfig, fOfX)]
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.zConfig, gOfX)]
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And substitutions - multiple terms" $ do
            let expect =
                    Conditional
                        { term = mkAnd (mkAnd Mock.a Mock.b) Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkAnd Mock.a Mock.b
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Conditional
                        { term = mkAnd Mock.b Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And substitutions - separate predicate" $ do
            let expect =
                    Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.yConfig, fOfX)]
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.yConfig, fOfX)]
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.yConfig, gOfX)]
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual
        , testCase "And substitutions - failure" $ do
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [
                                        ( inject Mock.yConfig
                                        , Mock.functionalConstr10
                                            (mkElemVar Mock.xConfig)
                                        )
                                    ]
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [
                                        ( inject Mock.yConfig
                                        , Mock.functionalConstr11
                                            (mkElemVar Mock.xConfig)
                                        )
                                    ]
                        }
            assertEqual "" OrPattern.bottom actual
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqual
                "Combines conditions with substitution merge condition"
                Pattern
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
                    Pattern
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    Pattern
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
        ]
    , testGroup
        "Variable-function and"
        [ testCase "variable-term" $ do
            let expect =
                    Conditional
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.yConfig, fOfX)]
                        }
            actual <- evaluatePatterns yExpanded fOfXExpanded
            assertEqual "" (MultiOr.make [expect]) actual
        , testCase "term-variable" $ do
            let expect =
                    Conditional
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.yConfig, fOfX)]
                        }
            actual <- evaluatePatterns fOfXExpanded yExpanded
            assertEqual "" (MultiOr.make [expect]) actual
        ]
    , testGroup
        "constructor and"
        [ testCase "same constructors" $ do
            let expect =
                    Conditional
                        { term = Mock.constr10 fOfX
                        , predicate =
                            makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Conditional
                        { term = Mock.constr10 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqual "" (MultiOr.make [expect]) actual
        , testCase "different constructors" $ do
            actual <-
                evaluatePatterns
                    Conditional
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Conditional
                        { term = Mock.constr11 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqual "" (MultiOr.make []) actual
        ]
    , -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
      testCase "And-Or distribution" $ do
        let expect =
                OrPattern.fromPatterns
                    [ makeEqualsPredicate fOfX gOfX
                        & Condition.fromPredicate
                        & Pattern.withCondition fOfX
                    , Conditional
                        { term = fOfX
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    , Conditional
                        { term = gOfX
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    , Conditional
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
                ( makeAnd
                    [ fOfXExpanded
                    , Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    ]
                    [ gOfXExpanded
                    , Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    ]
                )
        assertEqual "Distributes or" expect actual
    , testCase "Predicates are not duplicated" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeEqualsPredicate fOfX gOfX)
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 gOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    ]
  where
    yExpanded =
        Conditional
            { term = mkElemVar Mock.yConfig
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    fOfX = Mock.f (mkElemVar Mock.xConfig)
    fOfXExpanded = Pattern.fromTermLike fOfX
    gOfX = Mock.g (mkElemVar Mock.xConfig)
    gOfXExpanded =
        Conditional
            { term = gOfX
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    plain0OfX = Mock.plain10 (mkElemVar Mock.xConfig)
    plain0OfXExpanded =
        Conditional
            { term = plain0OfX
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    plain1OfX = Mock.plain11 (mkElemVar Mock.xConfig)
    plain1OfXExpanded =
        Conditional
            { term = plain1OfX
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    bottomTerm =
        Conditional
            { term = mkBottom_
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    falsePredicate =
        Conditional
            { term = mkTop_
            , predicate = makeFalsePredicate
            , substitution = mempty
            }

makeAnd ::
    [Pattern RewritingVariableName] ->
    [Pattern RewritingVariableName] ->
    And Sort (OrPattern RewritingVariableName)
makeAnd first second =
    And
        { andSort = findSort (first ++ second)
        , andFirst = OrPattern.fromPatterns first
        , andSecond = OrPattern.fromPatterns second
        }

findSort :: [Pattern RewritingVariableName] -> Sort
findSort [] = testSort
findSort (Conditional{term} : _) = termLikeSort term

evaluate ::
    And Sort (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
evaluate And{andFirst, andSecond} =
    MultiAnd.make [andFirst, andSecond]
        & simplify Not.notSimplifier SideCondition.top
        & runSimplifier Mock.env

evaluatePatterns ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
evaluatePatterns first second =
    MultiAnd.make [first, second]
        & makeEvaluate Not.notSimplifier SideCondition.top
        & runSimplifierBranch Mock.env
        & fmap OrPattern.fromPatterns
