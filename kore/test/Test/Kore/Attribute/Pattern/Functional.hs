module Test.Kore.Attribute.Pattern.Functional where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Synthetic
import Kore.Internal.TermLike
       ( TermLikeF (..) )
import Kore.Syntax hiding
       ( PatternF (..) )

import qualified Test.Kore.Step.MockSymbols as Mock

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF" $ map (isn't . AndF) (And sort <$> range <*> range)
    , testGroup "ApplySymbolF" $ do
        x <- range
        y <- range
        [ expect (x <> y) $ ApplySymbolF $ Application sigma [x, y] ]
    , testGroup "BottomF" [ isn't $ BottomF (Bottom sort) ]
    , testGroup "CeilF" $ map (isn't . CeilF) (Ceil sort sort <$> range)
    , testGroup "DomainValueF" $ do
        x <- range
        [ expect x $ DomainValueF (DomainValue sort x)]
    , testGroup "EqualsF" $
        map (isn't . EqualsF) (Equals sort sort <$> range <*> range)
    , testGroup "FloorF" $ map (isn't . FloorF) (Floor sort sort <$> range)
    , testGroup "IffF" $ map (isn't . IffF) (Iff sort <$> range <*> range)
    , testGroup "ImpliesF" $
        map (isn't . ImpliesF) (Implies sort <$> range <*> range)
    , testGroup "InF" $ map (isn't . InF) (In sort sort <$> range <*> range)
    , testGroup "NextF" $ do
        x <- range
        [ expect x $ NextF (Next sort x) ]
    , testGroup "NotF" $ map (isn't . NotF) (Not sort <$> range)
    , testGroup "OrF" $ map (isn't . OrF) (Or sort <$> range <*> range)
    , testGroup "RewritesF" $
        map (isn't . RewritesF) (Rewrites sort <$> range <*> range)
    , testGroup "TopF" [ isn't $ TopF (Top sort) ]
    , testGroup "ExistsF" $ map (isn't . ExistsF) (Exists sort Mock.x <$> range)
    , testGroup "ForallF" $ map (isn't . ForallF) (Forall sort Mock.x <$> range)
    , testGroup "VariableF" [ is $ VariableF Mock.x ]
    , testGroup "MuF" $ map (isn't . MuF) (Mu (SetVariable Mock.x) <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu (SetVariable Mock.x) <$> range)
    , testGroup "SetVariableF" [ isn't $ SetVariableF (SetVariable Mock.x) ]
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol

    functional = Functional True
    nonFunctional = Functional False
    range = [functional, nonFunctional]

    check
        :: GHC.HasCallStack
        => TestName
        -> (Functional -> Bool)
        -> TermLikeF Variable Functional
        -> TestTree
    check name checking termLikeF =
        testCase name $ do
            let actual = synthetic termLikeF
            assertBool "" (checking actual)

    is :: GHC.HasCallStack => TermLikeF Variable Functional -> TestTree
    is = check "Functional pattern" isFunctional

    isn't :: GHC.HasCallStack => TermLikeF Variable Functional -> TestTree
    isn't = check "Non-functional pattern" (not . isFunctional)

    expect
        :: GHC.HasCallStack
        => Functional
        -> TermLikeF Variable Functional
        -> TestTree
    expect x
      | isFunctional x = is
      | otherwise      = isn't
