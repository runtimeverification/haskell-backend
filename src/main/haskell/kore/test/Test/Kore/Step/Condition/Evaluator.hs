module Test.Kore.Step.Condition.Evaluator
    ( prop_andNegation
    ) where

import Test.Tasty.QuickCheck

import Data.Reflection

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.SMT.Config
import qualified Kore.Step.Condition.Evaluator as Evaluator
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.AST.Common
                 ( arbitrarySortedVariable )
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Predicate.Predicate ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
tools :: MetadataTools Object StepperAttributes
tools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    Builtin.Bool.tools

arbitraryPredicate
    :: Given (SymbolOrAliasSorts Object)
    => Gen (Predicate Object Variable)
arbitraryPredicate = sized arbitraryPredicateWorker
    where
    arbitraryPredicateWorker size
      | size == 0 =
        oneof
            [ pure makeFalsePredicate
            , pure makeTruePredicate
            ]
      | otherwise =
        oneof
            [ arbitraryAndPredicate
            , arbitraryCeilPredicate
            , arbitraryEqualsPredicate
            , arbitraryExistsPredicate
            , arbitraryFloorPredicate
            , arbitraryForallPredicate
            , arbitraryIffPredicate
            , arbitraryImpliesPredicate
            , arbitraryInPredicate
            , arbitraryNotPredicate
            , arbitraryOrPredicate
            ]
    halved = scale (`div` 2)
    arbitraryAndPredicate = do
        first <- halved arbitraryPredicate
        second <- halved arbitraryPredicate
        return $ makeAndPredicate first second
    arbitraryCeilPredicate = do
        first <- arbitrarySortedVariable Builtin.Bool.boolSort
        return $ makeCeilPredicate (mkVar first)
    arbitraryEqualsPredicate = do
        first <- arbitrarySortedVariable Builtin.Bool.boolSort
        second <- arbitrarySortedVariable Builtin.Bool.boolSort
        return $ makeEqualsPredicate (mkVar first) (mkVar second)
    arbitraryExistsPredicate = do
        var <- arbitrarySortedVariable Builtin.Bool.boolSort
        child <- scale pred arbitraryPredicate
        return $ makeExistsPredicate var child
    arbitraryFloorPredicate = do
        first <- arbitrarySortedVariable Builtin.Bool.boolSort
        return $ makeFloorPredicate (mkVar first)
    arbitraryForallPredicate = do
        var <- arbitrarySortedVariable Builtin.Bool.boolSort
        child <- scale pred arbitraryPredicate
        return $ makeForallPredicate var child
    arbitraryIffPredicate = do
        first <- halved arbitraryPredicate
        second <- halved arbitraryPredicate
        return $ makeIffPredicate first second
    arbitraryImpliesPredicate = do
        first <- halved arbitraryPredicate
        second <- halved arbitraryPredicate
        return $ makeImpliesPredicate first second
    arbitraryInPredicate = do
        first <- arbitrarySortedVariable Builtin.Bool.boolSort
        second <- arbitrarySortedVariable Builtin.Bool.boolSort
        return $ makeInPredicate (mkVar first) (mkVar second)
    arbitraryNotPredicate = do
        child <- scale pred arbitraryPredicate
        return $ makeNotPredicate child
    arbitraryOrPredicate = do
        first <- halved arbitraryPredicate
        second <- halved arbitraryPredicate
        return $ makeOrPredicate first second

{- |
@
    \\and{_}(φ, \not{_}(φ)) === \\bottom
@
 -}
prop_andNegation :: Gen Property
prop_andNegation = give testSymbolOrAliasSorts $ do
    predicate <- arbitraryPredicate
    let actual :: PredicateSubstitution Object Variable
        actual =
            evaluate
                (makeAndPredicate
                    predicate
                    (makeNotPredicate predicate)
                )
    return (expected === actual)
  where
    expected =
        PredicateSubstitution
            { predicate = makeFalsePredicate
            , substitution = []
            }

evaluate
    :: Predicate Object Variable
    -> PredicateSubstitution Object Variable
evaluate predicate =
    fst $ fst $
    give tools $
    give testSymbolOrAliasSorts $
    flip (runSimplifier $ SMTTimeOut 1000) 0 $
    Evaluator.evaluate
        (Mock.substitutionSimplifier tools)
        (mockSimplifier [])
        predicate
