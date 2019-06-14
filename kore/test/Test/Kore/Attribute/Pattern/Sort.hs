module Test.Kore.Attribute.Pattern.Sort where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Comonad.Trans.Cofree
import qualified Control.Exception as Exception
import qualified GHC.Stack as GHC

import Kore.Attribute.Synthetic
import Kore.Internal.TermLike
       ( TermLikeF (..) )
import Kore.Sort
import Kore.Syntax hiding
       ( PatternF (..) )

import qualified Test.Kore.Step.MockSymbols as Mock

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF"
        [ success $ AndF (And sort sort0 sort0)
        , failure $ AndF (And sort sort0 sort1)
        ]
    , testGroup "ApplySymbolF"
        [ success $ ApplySymbolF (Application sigma [sort, sort])
        ]
    , testGroup "BottomF"
        [ success $ BottomF (Bottom sort)
        ]
    , testGroup "CeilF"
        [ success $ CeilF (Ceil sort0 sort sort1)
        ]
    , testGroup "DomainValueF"
        [ success $ DomainValueF (DomainValue sort0 stringMetaSort)
        ]
    , testGroup "EqualsF"
        [ success $ EqualsF (Equals sort0 sort sort0 sort0)
        , failure $ EqualsF (Equals sort0 sort sort0 sort1)
        ]
    , testGroup "FloorF"
        [ success $ FloorF (Floor sort0 sort sort1)
        ]
    , testGroup "IffF"
        [ success $ IffF (Iff sort sort0 sort0)
        , failure $ IffF (Iff sort sort0 sort1)
        ]
    , testGroup "ImpliesF"
        [ success $ ImpliesF (Implies sort sort0 sort0)
        , failure $ ImpliesF (Implies sort sort0 sort1)
        ]
    , testGroup "InF"
        [ success $ InF (In sort0 sort sort0 sort0)
        , failure $ InF (In sort0 sort sort0 sort1)
        ]
    , testGroup "NextF"
        [ success $ NextF (Next sort sort0)
        ]
    , testGroup "NotF"
        [ success $ NotF (Not sort sort0)
        ]
    , testGroup "OrF"
        [ success $ OrF (Or sort sort0 sort0)
        , failure $ OrF (Or sort sort0 sort1)
        ]
    , testGroup "RewritesF"
        [ success $ RewritesF (Rewrites sort sort0 sort0)
        , failure $ RewritesF (Rewrites sort sort0 sort1)
        ]
    , success $ TopF (Top sort)
    , testGroup "ExistsF"
        [ success $ ExistsF (Exists sort Mock.x sort0)
        ]
    , testGroup "ForallF"
        [ success $ ForallF (Forall sort Mock.x sort0)
        ]
    , success $ VariableF Mock.x0
    ]
  where
    sort = Mock.testSort
    sort0 = Mock.testSort0
    sort1 = Mock.testSort1
    sigma = Mock.sigmaSymbol
    expected = sort0
    success
        :: GHC.HasCallStack
        => TermLikeF Variable Sort
        -> TestTree
    success termLikeF =
        testCase "Sorts agree" $ do
            let actual = synthetic (expected :< termLikeF)
            assertEqual "" expected actual
    failure
        :: GHC.HasCallStack
        => TermLikeF Variable Sort
        -> TestTree
    failure termLikeF =
        testCase "Sorts disagree" $ do
            let original = synthetic (sort :< termLikeF)
            actual <- Exception.try (Exception.evaluate original)
            assertEqual "" (Left $ SortsDisagree sort0 sort1) actual
