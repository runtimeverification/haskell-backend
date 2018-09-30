module Test.Kore.Step.Simplification.Floor
    ( test_floorSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( AstLocation (..), Floor (..), Id (..), Sort (..),
                 SymbolOrAlias (..), Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkBottom, mkOr, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( SymSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFloorPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Floor
                 ( makeEvaluateFloor, simplify )

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSymSorts )
import           Test.Tasty.HUnit.Extensions

test_floorSimplification :: [TestTree]
test_floorSimplification =
    [ testCase "Floor - or distribution"
        -- floor(a or b) = (top and floor(a)) or (top and floor(b))
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = give mockSymSorts $
                        makeFloorPredicate (mkOr a b)
                    , substitution = []
                    }
                ]
            )
            (give mockSymSorts $ evaluate
                (makeFloor
                    [aExpanded, bExpanded]
                )
            )
        )
    , testCase "Floor - bool operations"
        (do
            -- floor(top) = top
            assertEqualWithExplanation "floor(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (give mockSymSorts $ evaluate
                    (makeFloor
                        [ExpandedPattern.top]
                    )
                )
            -- floor(bottom) = bottom
            assertEqualWithExplanation "floor(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (give mockSymSorts $ evaluate
                    (makeFloor
                        []
                    )
                )
        )
    , testCase "expanded Floor - bool operations"
        (do
            -- floor(top) = top
            assertEqualWithExplanation "floor(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (give mockSymSorts $ makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- floor(bottom) = bottom
            assertEqualWithExplanation "floor(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (give mockSymSorts $ makeEvaluate
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
        )
    , testCase "floor with predicates and substitutions"
        -- floor(term and predicate and subst)
        --     = top and (floor(term) and predicate) and subst
        (assertEqualWithExplanation "floor(top)"
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate =
                        fst $ give mockSymSorts $ makeAndPredicate
                            (makeFloorPredicate a)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = [(x, fOfB)]
                    }
                ]
            )
            (give mockSymSorts $ makeEvaluate
                ExpandedPattern
                    { term = a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = [(x, fOfB)]
                    }
            )
        )
    -- floor moves predicates and substitutions up
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
    a = give mockSymSorts $ mkApp aSymbol []
    b = give mockSymSorts $ mkApp bSymbol []
    fOfA = give mockSymSorts $ mkApp fSymbol [a]
    fOfB = give mockSymSorts $ mkApp fSymbol [b]
    gOfA = give mockSymSorts $ mkApp gSymbol [a]
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
    symSortsMapping =
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
    mockSymSorts = Mock.makeSymSorts symSortsMapping

makeFloor
    :: [ExpandedPattern Object variable]
    -> Floor Object (OrOfExpandedPattern Object variable)
makeFloor patterns =
    Floor
        { floorOperandSort = testSort
        , floorResultSort  = testSort
        , floorChild       = OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level
        , Given (SymSorts level)
        )
    => Floor level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate floor' =
    case simplify floor' of
        (result, _proof) -> result


makeEvaluate
    ::  ( MetaOrObject level
        , Given (SymSorts level)
        )
    => CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
makeEvaluate child =
    case makeEvaluateFloor child of
        (result, _proof) -> result
