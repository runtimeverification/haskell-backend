module Test.Kore.Step.Simplification.And
    (test_andSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Control.Monad.Except
       ( runExceptT )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( And (..), AstLocation (..), Id (..), Sort (..),
                 SymbolOrAlias (..), Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( getSort, mkAnd, mkApp, mkBottom, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (MetadataTools), SortTools )
import qualified Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.And
                 ( makeEvaluate, simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Variables.Fresh.IntCounter
                 ( runIntCounter )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( constructorFunctionalAttributes, makeMetadataTools )
import           Test.Tasty.HUnit.Extensions

test_andSimplification :: [TestTree]
test_andSimplification =
    [ testCase "And truth table"
        (do
            assertEqualWithExplanation "false and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [])
                )
            assertEqualWithExplanation "false and true = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [ExpandedPattern.top])
                )
            assertEqualWithExplanation "true and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [])
                )
            assertEqualWithExplanation "true and true = true"
                (OrOfExpandedPattern.make [ExpandedPattern.top])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [ExpandedPattern.top])
                )
        )
    , testCase "And with booleans"
        (do
            assertEqualWithExplanation "false and something = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [] [fOfXExpanded])
                )
            assertEqualWithExplanation "something and false = false"
                (OrOfExpandedPattern.make [])
                (evaluate
                    (makeAnd [fOfXExpanded] [])
                )
            assertEqualWithExplanation "true and something = something"
                (OrOfExpandedPattern.make [fOfXExpanded])
                (evaluate
                    (makeAnd [ExpandedPattern.top] [fOfXExpanded])
                )
            assertEqualWithExplanation "something and true = something"
                (OrOfExpandedPattern.make [fOfXExpanded])
                (evaluate
                    (makeAnd [fOfXExpanded] [ExpandedPattern.top])
                )
        )
    , testCase "And with partial booleans"
        (do
            assertEqualWithExplanation "false term and something = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    bottomTerm fOfXExpanded
                )
            assertEqualWithExplanation "something and false term = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    fOfXExpanded bottomTerm
                )
            assertEqualWithExplanation "false predicate and something = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    falsePredicate fOfXExpanded
                )
            assertEqualWithExplanation "something and false predicate = false"
                ExpandedPattern.bottom
                (evaluatePatterns
                    fOfXExpanded falsePredicate
                )
        )
    , testCase "And with normal patterns"
        (do
            assertEqualWithExplanation "And terms"
                ExpandedPattern
                    { term = give mockSortTools $ mkAnd fOfX gOfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                (evaluatePatterns
                    fOfXExpanded gOfXExpanded
                )
            assertEqualWithExplanation "And predicates"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ give mockSortTools $ makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = []
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate fOfX
                        , substitution = []
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate gOfX
                        , substitution = []
                        }
                )
            assertEqualWithExplanation "And substitutions - simple"
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(y, fOfX), (z, gOfX)]
                    }
                (evaluatePatterns
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(z, gOfX)]
                        }
                )
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation "And substitutions - separate predicate"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        give mockSortTools $ makeEqualsPredicate fOfX gOfX
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, Mock.functionAttributes)
                    , (gSymbol, Mock.functionAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
            assertEqualWithExplanation "And substitutions - failure"
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, Mock.constructorFunctionalAttributes)
                    , (gSymbol, Mock.constructorFunctionalAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = [(y, gOfX)]
                        }
                )
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqualWithExplanation
                "Combines conditions with substitution merge condition"
                ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ give mockSortTools $ makeAndPredicate
                            (fst $ give mockSortTools $ makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                            )
                            (give mockSortTools $ makeEqualsPredicate fOfX gOfX)
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, mock.functionAttributes)
                    , (gSymbol, mock.functionAttributes)
                    ]
                    ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate gOfX
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
        )
    -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
    , testCase "And-Or distribution"
        (assertEqualWithExplanation "Distributes or"
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = give mockSortTools $ mkAnd fOfX gOfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = fOfX
                    , predicate =
                        give mockSortTools $ makeCeilPredicate gOfX
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = gOfX
                    , predicate =
                        give mockSortTools $ makeCeilPredicate fOfX
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ give mockSortTools $ makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (makeAnd
                    [ fOfXExpanded
                    , ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate fOfX
                        , substitution = []
                        }
                    ]
                    [ gOfXExpanded
                    , ExpandedPattern
                        { term = mkTop
                        , predicate =
                            give mockSortTools $ makeCeilPredicate gOfX
                        , substitution = []
                        }
                    ]
                )
            )
        )
    ]
  where
    x = Variable
        { variableName = Id "x" AstLocationTest
        , variableSort = testSort
        }
    y = Variable
        { variableName = Id "y" AstLocationTest
        , variableSort = testSort
        }
    z = Variable
        { variableName = Id "z" AstLocationTest
        , variableSort = testSort
        }
    fSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "f" AstLocationTest
        , symbolOrAliasParams      = []
        }
    gSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "g" AstLocationTest
        , symbolOrAliasParams      = []
        }
    fOfX = give mockSortTools $ mkApp fSymbol [mkVar x]
    fOfXExpanded = ExpandedPattern
        { term = fOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    gOfX = give mockSortTools $ mkApp gSymbol [mkVar x]
    gOfXExpanded = ExpandedPattern
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    bottomTerm = ExpandedPattern
        { term = mkBottom
        , predicate = makeTruePredicate
        , substitution = []
        }
    falsePredicate = ExpandedPattern
        { term = mkTop
        , predicate = makeFalsePredicate
        , substitution = []
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
    ( ExpandedPattern {term} : _ )
  =
    give mockSortTools $ getSort term

evaluate
    :: And Object (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate patt =
    either (error . printError) fst $ fst $ runIntCounter
        (runExceptT $ simplify mockMetadataTools patt)
        0

evaluatePatterns
    :: CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
evaluatePatterns first second =
    fst $ fst $ runIntCounter
        (makeEvaluate mockMetadataTools first second)
        0

evaluatePatternsWithAttributes
    :: [(SymbolOrAlias Object, StepperAttributes)]
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
    -> CommonExpandedPattern Object
evaluatePatternsWithAttributes attributes first second =
    fst $ fst $ runIntCounter
        (makeEvaluate
            (mockMetadataToolsWithAttributes attributes)
            first
            second
        )
        0

mockSortTools :: SortTools Object
mockSortTools = const
    ApplicationSorts
    { applicationSortsOperands = [testSort]
    , applicationSortsResult = testSort
    }

testSort :: MetaOrObject level => Sort level
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools = MetadataTools
    { attributes = const Mock.constructorFunctionalAttributes
    , sortTools = mockSortTools
    }

mockMetadataToolsWithAttributes
    :: [(SymbolOrAlias Object, StepperAttributes)]
    -> MetadataTools Object StepperAttributes
mockMetadataToolsWithAttributes = Mock.makeMetadataTools mockSortTools
