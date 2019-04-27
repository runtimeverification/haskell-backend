module Test.Kore.Step.Simplification.Next
    ( test_nextSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Next (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Pattern.Or as Or
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Next
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_nextSimplification :: [TestTree]
test_nextSimplification =
    [ testCase "Next evaluates to Next"
        (assertEqualWithExplanation ""
            (MultiOr.make
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
            (MultiOr.make
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

findSort :: [Pattern Object Variable] -> Sort Object
findSort [] = Mock.testSort
findSort ( Conditional {term} : _ ) = getSort term

evaluate
    :: Next Object (Or.Pattern Object Variable)
    -> Or.Pattern Object Variable
evaluate next =
    case simplify next of
        (result, _proof) -> result

makeNext
    :: [Pattern Object Variable]
    -> Next Object (Or.Pattern Object Variable)
makeNext child =
    Next
        { nextSort = findSort child
        , nextChild = MultiOr.make child
        }
