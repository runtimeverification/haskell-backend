module Test.Kore.Step.Simplification.Next
    ( test_nextSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Next
                 ( simplify )
import           Kore.Syntax.Next

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_nextSimplification :: [TestTree]
test_nextSimplification =
    [ testCase "Next evaluates to Next"
        (assertEqualWithExplanation ""
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkNext Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            (evaluate
                (makeNext
                    [ Conditional
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
            )
        )
    , testCase "Next collapses or"
        (assertEqualWithExplanation ""
            (OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkNext
                            (mkOr
                                Mock.a
                                (mkAnd Mock.b (mkEquals_ Mock.a Mock.b))
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            (evaluate
                (makeNext
                    [ Conditional
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.b
                        , predicate = makeEqualsPredicate Mock.a Mock.b
                        , substitution = mempty
                        }
                    ]
                )
            )
        )
    ]

findSort :: [Pattern Variable] -> Sort
findSort [] = Mock.testSort
findSort ( Conditional {term} : _ ) = getSort term

evaluate :: Next Sort (OrPattern Variable) -> OrPattern Variable
evaluate = simplify

makeNext
    :: [Pattern Variable]
    -> Next Sort (OrPattern Variable)
makeNext child =
    Next
        { nextSort = findSort child
        , nextChild = OrPattern.fromPatterns child
        }
