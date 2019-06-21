module Test.Kore.Attribute.Pattern.Defined where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Synthetic
import Kore.Internal.TermLike
       ( TermLikeF (..) )
import Kore.Syntax hiding
       ( PatternF (..) )

import qualified Test.Kore.Step.MockSymbols as Mock

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF" $ map (isn't . AndF) (And sort <$> range <*> range)
    , testGroup "BottomF" [ isn't $ BottomF (Bottom sort) ]
    , testGroup "CeilF" $ map (isn't . CeilF) (Ceil sort sort <$> range)
    , testGroup "EqualsF" $
        map (isn't . EqualsF) (Equals sort sort <$> range <*> range)
    , testGroup "FloorF" $ map (isn't . FloorF) (Floor sort sort <$> range)
    , testGroup "IffF" $ map (isn't . IffF) (Iff sort <$> range <*> range)
    , testGroup "ImpliesF" $
        map (isn't . ImpliesF) (Implies sort <$> range <*> range)
    , testGroup "InF" $ map (isn't . InF) (In sort sort <$> range <*> range)
    , testGroup "NotF" $ map (isn't . NotF) (Not sort <$> range)
    , testGroup "OrF" $ map (isn't . OrF) (Or sort <$> range <*> range)
    , testGroup "RewritesF" $
        map (isn't . RewritesF) (Rewrites sort <$> range <*> range)
    , testGroup "TopF" [ is $ TopF (Top sort) ]
    , testGroup "ExistsF" $ map (isn't . ExistsF) (Exists sort Mock.x <$> range)
    , testGroup "ForallF" $ map (isn't . ForallF) (Forall sort Mock.x <$> range)
    , testGroup "VariableF" [ is $ VariableF Mock.x ]
    , testGroup "MuF" $ map (isn't . MuF) (Mu (SetVariable Mock.x) <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu (SetVariable Mock.x) <$> range)
    , testGroup "SetVariableF" [ isn't $ SetVariableF (SetVariable Mock.x) ]
    -- Interesting cases
    , testGroup "ApplySymbolF" $ do
        x <- range
        y <- range
        [ expect (x <> y) $ ApplySymbolF $ Application sigma [x, y] ]
    , testGroup "DomainValueF" $ do
        x <- range
        [ expect x $ DomainValueF (DomainValue sort x)]
    , testGroup "NextF" $ do
        x <- range
        [ expect x $ NextF (Next sort x) ]
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol

    defined = Defined True
    nonDefined = Defined False
    range = [defined, nonDefined]

    check
        :: GHC.HasCallStack
        => TestName
        -> (Defined -> Bool)
        -> TermLikeF Variable Defined
        -> TestTree
    check name checking termLikeF =
        testCase name $ do
            let actual = synthetic termLikeF
            assertBool "" (checking actual)

    is :: GHC.HasCallStack => TermLikeF Variable Defined -> TestTree
    is = check "Defined pattern" isDefined

    isn't :: GHC.HasCallStack => TermLikeF Variable Defined -> TestTree
    isn't = check "Non-defined pattern" (not . isDefined)

    expect
        :: GHC.HasCallStack
        => Defined
        -> TermLikeF Variable Defined
        -> TestTree
    expect x
      | isDefined x = is
      | otherwise      = isn't
