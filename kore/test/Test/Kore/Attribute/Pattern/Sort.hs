module Test.Kore.Attribute.Pattern.Sort where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Exception as Exception
import qualified GHC.Stack as GHC

import Kore.Attribute.Synthetic
import Kore.Internal.TermLike
    ( TermLikeF (..)
    )
import Kore.Sort
import Kore.Syntax hiding
    ( PatternF (..)
    )
import Kore.Variables.UnifiedVariable

import qualified Test.Kore.Step.MockSymbols as Mock

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF"
        [ success $ AndF (And sort sort sort)
        , failure $ AndF (And sort sort0 sort)
        , failure $ AndF (And sort sort sort0)
        ]
    , testGroup "ApplySymbolF"
        [ success $ ApplySymbolF (Application sigma [sort, sort])
        , failure $ ApplySymbolF (Application sigma [sort0, sort])
        , failure $ ApplySymbolF (Application sigma [sort, sort0])
        ]
    , testGroup "BottomF"
        [ success $ BottomF (Bottom sort)
        ]
    , testGroup "CeilF"
        [ success $ CeilF (Ceil sort0 sort sort0)
        , failure $ CeilF (Ceil sort sort sort0)
        ]
    , testGroup "DomainValueF"
        [ success $ DomainValueF (DomainValue sort stringMetaSort)
        ]
    , testGroup "EqualsF"
        [ success $ EqualsF (Equals sort0 sort sort0 sort0)
        , failure $ EqualsF (Equals sort sort0 sort0 sort)
        , failure $ EqualsF (Equals sort sort0 sort sort0)
        ]
    , testGroup "FloorF"
        [ success $ FloorF (Floor sort0 sort sort0)
        , failure $ FloorF (Floor sort sort0 sort0)
        ]
    , testGroup "IffF"
        [ success $ IffF (Iff sort sort sort)
        , failure $ IffF (Iff sort sort0 sort)
        , failure $ IffF (Iff sort sort sort0)
        ]
    , testGroup "ImpliesF"
        [ success $ ImpliesF (Implies sort sort sort)
        , failure $ ImpliesF (Implies sort sort0 sort)
        , failure $ ImpliesF (Implies sort sort sort0)
        ]
    , testGroup "InF"
        [ success $ InF (In sort0 sort sort0 sort0)
        , failure $ InF (In sort sort0 sort0 sort)
        , failure $ InF (In sort sort0 sort sort0)
        ]
    , testGroup "NextF"
        [ success $ NextF (Next sort sort)
        , failure $ NextF (Next sort sort0)
        ]
    , testGroup "NotF"
        [ success $ NotF (Not sort sort)
        , failure $ NotF (Not sort sort0)
        ]
    , testGroup "OrF"
        [ success $ OrF (Or sort sort sort)
        , failure $ OrF (Or sort sort0 sort)
        , failure $ OrF (Or sort sort sort0)
        ]
    , testGroup "RewritesF"
        [ success $ RewritesF (Rewrites sort sort sort)
        , failure $ RewritesF (Rewrites sort sort0 sort)
        , failure $ RewritesF (Rewrites sort sort sort0)
        ]
    , testGroup "TopF"
        [ success $ TopF (Top sort)
        ]
    , testGroup "ExistsF"
        [ success $ ExistsF (Exists sort Mock.x sort)
        , failure $ ExistsF (Exists sort Mock.x sort0)
        ]
    , testGroup "ForallF"
        [ success $ ForallF (Forall sort Mock.x sort)
        , failure $ ForallF (Forall sort Mock.x sort0)
        ]
    , testGroup "VariableF"
        [ success $ VariableF (Const (ElemVar Mock.x))
        ]
    , testGroup "MuF"
        [ success $ MuF (Mu Mock.setX sort)
        , failure $ MuF (Mu Mock.setX sort0)
        ]
    , testGroup "NuF"
        [ success $ NuF (Nu Mock.setX sort)
        , failure $ NuF (Nu Mock.setX sort0)
        ]
    ]
  where
    sort = Mock.testSort
    sort0 = Mock.testSort0
    sigma = Mock.sigmaSymbol
    expected = sort
    success
        :: GHC.HasCallStack
        => TermLikeF Variable Sort
        -> TestTree
    success termLikeF =
        testCase "Sorts match" $ do
            let actual = synthetic termLikeF
            assertEqual "" expected actual
    failure
        :: GHC.HasCallStack
        => TermLikeF Variable Sort
        -> TestTree
    failure termLikeF =
        testCase "Sorts mismatch" $ do
            let original = synthetic termLikeF
            actual <- Exception.try (Exception.evaluate original)
            assertEqual "" (Left $ SortMismatch sort sort0) actual
