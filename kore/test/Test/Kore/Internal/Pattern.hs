module Test.Kore.Internal.Pattern
    ( test_expandedPattern
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty (..) )

import           Kore.Internal.Pattern as Pattern
                 ( Conditional (..), allVariables, mapVariables, toTermLike )
import           Kore.Internal.TermLike hiding
                 ( V )
import           Kore.Predicate.Predicate
                 ( Predicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase "Mapping variables"
        (assertEqualWithExplanation ""
            Conditional
                { term = war "1"
                , predicate = makeEquals (war "2") (war "3")
                , substitution = Substitution.wrap [(W "4", war "5")]
                }
            (Pattern.mapVariables showVar
                Conditional
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
                (Pattern.allVariables
                    Conditional
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
            (Pattern.toTermLike
                Conditional
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
            (Pattern.toTermLike
                Conditional
                    { term = mkTop sortVariable
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top predicate"
        (assertEqualWithExplanation ""
            (var 1)
            (Pattern.toTermLike
                Conditional
                    { term = var 1
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom pattern"
        (assertEqualWithExplanation ""
            (mkBottom sortVariable)
            (Pattern.toTermLike
                Conditional
                    { term = mkBottom sortVariable
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap [(V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom predicate"
        (assertEqualWithExplanation ""
            (mkBottom sortVariable)
            (Pattern.toTermLike
                Conditional
                    { term = var 1
                    , predicate = makeFalsePredicate
                    , substitution = mempty
                    }
            )
        )
    ]

newtype V = V Integer
    deriving (Show, Eq, Ord)
newtype W = W String
    deriving (Show, Eq, Ord)

instance Unparse V where
    unparse (V n) = "V" <> pretty n <> ":" <> unparse sortVariable
    unparse2 = error "Not implemented"

instance Unparse W where
    unparse (W name) = "W" <> pretty name <> ":" <> unparse sortVariable
    unparse2 = error "Not implemented"

instance SortedVariable V where
    sortedVariableSort _ = sortVariable
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

instance SumEqualWithExplanation V where
    sumConstructorPair (V a1) (V a2) =
        SumConstructorSameWithArguments
            (EqWrap "V" a1 a2)

instance EqualWithExplanation V where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance SortedVariable W where
    sortedVariableSort _ = sortVariable
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

instance SumEqualWithExplanation W where
    sumConstructorPair (W a1) (W a2) =
        SumConstructorSameWithArguments (EqWrap "W" a1 a2)

instance EqualWithExplanation W where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show


showVar :: V -> W
showVar (V i) = W (show i)

var :: Integer -> TermLike V
var i = mkVar (V i)

war :: String -> TermLike W
war s = mkVar (W s)

makeEq
    :: (SortedVariable var, Ord var, Show var, Unparse var)
    => TermLike var
    -> TermLike var
    -> TermLike var
makeEq = mkEquals sortVariable

makeAnd
    :: (SortedVariable var, Ord var, Show var, Unparse var)
    => TermLike var
    -> TermLike var
    -> TermLike var
makeAnd p1 p2 = mkAnd p1 p2

makeEquals
    :: (SortedVariable var, Ord var, Show var, Unparse var)
    => TermLike var -> TermLike var -> Predicate var
makeEquals p1 p2 = makeEqualsPredicate p1 p2

sortVariable :: Sort
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
