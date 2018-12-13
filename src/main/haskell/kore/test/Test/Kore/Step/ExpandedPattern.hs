module Test.Kore.Step.ExpandedPattern (test_expandedPattern) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty (..) )

import           Kore.AST.Pure
import           Kore.AST.Valid hiding
                 ( V )
import           Kore.Predicate.Predicate
                 ( Predicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), allVariables, mapVariables, toMLPattern )
import           Kore.Step.Pattern
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase "Mapping variables"
        (assertEqualWithExplanation ""
            Predicated
                { term = war "1"
                , predicate = makeEquals (war "2") (war "3")
                , substitution = Substitution.wrap [(W "4", war "5")]
                }
            (ExpandedPattern.mapVariables showVar
                Predicated
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Extracting variables"
        (assertEqual ""
            [V 1, V 2, V 3, V 4, V 5]
            (Set.toList
                (ExpandedPattern.allVariables
                    Predicated
                        { term = var 1
                        , predicate = makeEquals (var 2) (var 3)
                        , substitution = Substitution.wrap [(V 4, var 5)]
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
            (ExpandedPattern.toMLPattern
                Predicated
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top pattern"
        (assertEqualWithExplanation ""
            (makeAnd
                (makeEq (var 2) (var 3))
                (makeEq (var 4) (var 5))
            )
            (ExpandedPattern.toMLPattern
                Predicated
                    { term = mkTop sortVariable
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top predicate"
        (assertEqualWithExplanation ""
            (var 1)
            (ExpandedPattern.toMLPattern
                Predicated
                    { term = var 1
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom pattern"
        (assertEqualWithExplanation ""
            (mkBottom sortVariable)
            (ExpandedPattern.toMLPattern
                Predicated
                    { term = mkBottom sortVariable
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom predicate"
        (assertEqualWithExplanation ""
            (mkBottom sortVariable)
            (ExpandedPattern.toMLPattern
                Predicated
                    { term = var 1
                    , predicate = makeFalsePredicate
                    , substitution = mempty
                    }
            )
        )
    ]

newtype V level = V Integer
    deriving (Show, Eq, Ord)
newtype W level = W String
    deriving (Show, Eq, Ord)

instance Unparse (V level) where
    unparse (V n) = "V" <> pretty n <> ":" <> unparse sortVariable

instance Unparse (W level) where
    unparse (W name) = "W" <> pretty name <> ":" <> unparse sortVariable

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

var :: Integer -> StepPattern Meta V
var i = mkVar (V i)

war :: String -> StepPattern Meta W
war s = mkVar (W s)

makeEq
    :: (SortedVariable var, Show (var Meta), Unparse (var Meta))
    => StepPattern Meta var
    -> StepPattern Meta var
    -> StepPattern Meta var
makeEq = mkEquals sortVariable

makeAnd
    :: (SortedVariable var, Show (var Meta), Unparse (var Meta))
    => StepPattern Meta var
    -> StepPattern Meta var
    -> StepPattern Meta var
makeAnd p1 p2 = mkAnd p1 p2

makeEquals
    :: (SortedVariable var, Eq (var Meta), Show (var Meta), Unparse (var Meta))
    => StepPattern Meta var -> StepPattern Meta var -> Predicate Meta var
makeEquals p1 p2 = makeEqualsPredicate p1 p2

sortVariable :: Sort level
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
