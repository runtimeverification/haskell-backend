module Test.Kore.Step.Simplification.Next
    ( test_nextSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Next (..), Sort )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( getSort, mkAnd, mkEquals, mkNext, mkOr )
import           Kore.IndexedModule.MetadataTools
                 ( SymSorts )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Next
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSymSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_nextSimplification :: [TestTree]
test_nextSimplification = give mockSymSorts
    [ testCase "Next evaluates to Next"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkNext Mock.a
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (makeNext
                    [ ExpandedPattern
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
            )
        )
    , testCase "Next collapses or"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term =
                        mkNext
                            (mkOr
                                Mock.a
                                (mkAnd Mock.b (mkEquals Mock.a Mock.b))
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (makeNext
                    [ ExpandedPattern
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    , ExpandedPattern
                        { term = Mock.b
                        , predicate = makeEqualsPredicate Mock.a Mock.b
                        , substitution = []
                        }
                    ]
                )
            )
        )
    ]

mockSymSorts :: SymSorts Object
mockSymSorts = Mock.makeSymSorts Mock.symSortsMapping

findSort :: [CommonExpandedPattern Object] -> Sort Object
findSort [] = Mock.testSort
findSort
    ( ExpandedPattern {term} : _ )
  =
    give mockSymSorts $ getSort term

evaluate
    :: Next Object (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate next =
    case give mockSymSorts $ simplify next of
        (result, _proof) -> result

makeNext
    :: [CommonExpandedPattern Object]
    -> Next Object (CommonOrOfExpandedPattern Object)
makeNext child =
    Next
        { nextSort = findSort child
        , nextChild = OrOfExpandedPattern.make child
        }
