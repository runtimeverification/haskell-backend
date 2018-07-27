module Test.Kore.Step.Simplification.Ceil
    ( test_ceilSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( AstLocation (..), Ceil (..), Id (..), Sort (..),
                 SymbolOrAlias (..), Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkBottom, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Ceil
                 ( makeEvaluateCeil, simplify )

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSortTools )
import           Test.Tasty.HUnit.Extensions

test_ceilSimplification :: [TestTree]
test_ceilSimplification =
    [ testCase "Ceil - or distribution"
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = give mockSortTools $ makeCeilPredicate a
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = mkTop
                    , predicate = give mockSortTools $ makeCeilPredicate b
                    , substitution = []
                    }
                ]
            )
            (give mockSortTools $ evaluate
                (makeCeil
                    [aExpanded, bExpanded]
                )
            )
        )
    , testCase "Ceil - bool operations"
        (do
            -- ceil(top) = top
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (give mockSortTools $ evaluate
                    (makeCeil
                        [ExpandedPattern.top]
                    )
                )
            -- ceil(bottom) = bottom
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (give mockSortTools $ evaluate
                    (makeCeil
                        []
                    )
                )
        )
    , testCase "expanded Ceil - bool operations"
        (do
            -- ceil(top) = top
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern
                        { term = mkTop
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (give mockSortTools $ makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- ceil(bottom) = bottom
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (give mockSortTools $ makeEvaluate
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
        )
    , testCase "ceil with predicates and substitutions"
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        (assertEqualWithExplanation "ceil(top)"
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ give mockSortTools $ makeAndPredicate
                            (makeCeilPredicate a)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = [(x, fOfB)]
                    }
                ]
            )
            (give mockSortTools $ makeEvaluate
                ExpandedPattern
                    { term = a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = [(x, fOfB)]
                    }
            )
        )
    -- ceil moves predicates and substitutions up
    ]
  where
    fId = Id "f" AstLocationTest
    gId = Id "g" AstLocationTest
    aSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "a" AstLocationTest
        , symbolOrAliasParams      = []
        }
    bSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "b" AstLocationTest
        , symbolOrAliasParams      = []
        }
    fSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = fId
        , symbolOrAliasParams      = []
        }
    gSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = gId
        , symbolOrAliasParams      = []
        }
    x = Variable (testId "x") testSort
    a = give mockSortTools $ mkApp aSymbol []
    b = give mockSortTools $ mkApp bSymbol []
    fOfA = give mockSortTools $ mkApp fSymbol [a]
    fOfB = give mockSortTools $ mkApp fSymbol [b]
    gOfA = give mockSortTools $ mkApp gSymbol [a]
    aExpanded = ExpandedPattern
        { term = a
        , predicate = makeTruePredicate
        , substitution = []
        }
    bExpanded = ExpandedPattern
        { term = b
        , predicate = makeTruePredicate
        , substitution = []
        }
    sortToolsMapping =
        [   ( aSymbol
            , ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = testSort
                }
            )
        ,   ( bSymbol
            , ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = testSort
                }
            )
        ,   ( fSymbol
            , ApplicationSorts
                { applicationSortsOperands = [testSort]
                , applicationSortsResult = testSort
                }
            )
        ,   ( gSymbol
            , ApplicationSorts
                { applicationSortsOperands = [testSort]
                , applicationSortsResult = testSort
                }
            )
        ]
    mockSortTools = Mock.makeSortTools sortToolsMapping

makeCeil
    :: [ExpandedPattern Object variable]
    -> Ceil Object (OrOfExpandedPattern Object variable)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort  = testSort
        , ceilChild       = OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => Ceil level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate ceil =
    case simplify ceil of
        (result, _proof) -> result


makeEvaluate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
makeEvaluate child =
    case makeEvaluateCeil child of
        (result, _proof) -> result
