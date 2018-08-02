module Test.Kore.Step.ExpandedPattern (test_expandedPattern) where

import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Kore.AST.Common
       ( AstLocation (..), Id (..), Sort (..), SortVariable (..),
       SortedVariable (..) )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.ASTHelpers
       ( ApplicationSorts(..) )
import Kore.ASTUtils.SmartConstructors
       ( mkAnd, mkBottom, mkEquals, mkTop, mkVar )
import Kore.IndexedModule.MetadataTools
       ( SortTools )

import Kore.Predicate.Predicate
       ( Predicate, makeEqualsPredicate, makeFalsePredicate,
       makeTruePredicate )
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..), allVariables, mapVariables, toMLPattern )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase "Mapping variables"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = war "1"
                , predicate = makeEquals (war "2") (war "3")
                , substitution = [(W "4", war "5")]
                }
            (ExpandedPattern.mapVariables showVar
                ExpandedPattern
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = [(V 4, var 5)]
                    }
            )
        )
    , testCase "Extracting variables"
        (assertEqual ""
            [V 1, V 2, V 3, V 4, V 5]
            (Set.toList
                (ExpandedPattern.allVariables
                    ExpandedPattern
                        { term = var 1
                        , predicate = makeEquals (var 2) (var 3)
                        , substitution = [(V 4, var 5)]
                        }
                )
            )
        )
    , testCase "Converting to a ML pattern"
        (assertEqualWithExplanation ""
            (makeAnd
                (makeAnd
                    (var 1)
                    (makeEq (var 2) (var 3))
                )
                (makeEq (var 4) (var 5))
            )
            (give mockSortTools $ ExpandedPattern.toMLPattern
                ExpandedPattern
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top pattern"
        (assertEqualWithExplanation ""
            (makeAnd
                (makeEq (var 2) (var 3))
                (makeEq (var 4) (var 5))
            )
            (give mockSortTools $ ExpandedPattern.toMLPattern
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top predicate"
        (assertEqualWithExplanation ""
            (var 1)
            (give mockSortTools $ ExpandedPattern.toMLPattern
                ExpandedPattern
                    { term = var 1
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom pattern"
        (assertEqualWithExplanation ""
            mkBottom
            (give mockSortTools $ ExpandedPattern.toMLPattern
                ExpandedPattern
                    { term = mkBottom
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom predicate"
        (assertEqualWithExplanation ""
            mkBottom
            (give mockSortTools $ ExpandedPattern.toMLPattern
                ExpandedPattern
                    { term = var 1
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
            )
        )
    ]

newtype V level = V Integer
    deriving (Show, Eq, Ord)
newtype W level = W String
    deriving (Show, Eq, Ord)

instance SortedVariable V where
    sortedVariableSort _ = sortVariable

instance SumEqualWithExplanation (V level)
  where
    sumConstructorPair (V a1) (V a2) =
        SumConstructorSameWithArguments
            (EqWrap "V" a1 a2)

instance EqualWithExplanation (V level)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance SortedVariable W where
    sortedVariableSort _ = sortVariable

instance SumEqualWithExplanation (W level)
  where
    sumConstructorPair (W a1) (W a2) =
        SumConstructorSameWithArguments
            (EqWrap "W" (EWEString a1) (EWEString a2))

instance EqualWithExplanation (W level)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show


showVar :: V level -> W level
showVar (V i) = W (show i)

var :: Integer -> PureMLPattern Meta V
var i = give mockSortTools (mkVar (V i))

war :: String -> PureMLPattern Meta W
war s = give mockSortTools (mkVar (W s))

makeEq
    :: (SortedVariable var, Show (var Meta))
    => PureMLPattern Meta var
    -> PureMLPattern Meta var
    -> PureMLPattern Meta var
makeEq p1 p2 =
    give mockSortTools (mkEquals p1 p2)

makeAnd
    :: (SortedVariable var, Show (var Meta))
    => PureMLPattern Meta var
    -> PureMLPattern Meta var
    -> PureMLPattern Meta var
makeAnd p1 p2 =
    give mockSortTools (mkAnd p1 p2)

makeEquals
    :: (SortedVariable var, Show (var Meta))
    => PureMLPattern Meta var -> PureMLPattern Meta var -> Predicate Meta var
makeEquals p1 p2 =
    give mockSortTools (makeEqualsPredicate p1 p2)

mockSortTools :: SortTools Meta
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = [sortVariable, sortVariable]
    , applicationSortsResult = sortVariable
    }

sortVariable :: Sort level
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
