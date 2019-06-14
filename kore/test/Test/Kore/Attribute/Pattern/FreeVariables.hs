module Test.Kore.Attribute.Pattern.FreeVariables where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Comonad.Trans.Cofree
import qualified GHC.Stack as GHC

import           Kore.Attribute.Pattern.FreeVariables
                 ( FreeVariables )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import           Kore.Attribute.Synthetic
import           Kore.Internal.TermLike
                 ( TermLikeF (..) )
import           Kore.Syntax hiding
                 ( PatternF (..) )

import qualified Test.Kore.Step.MockSymbols as Mock

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ AndF         (And sort x y)             `gives` xy     $ "AndF"
    , ApplySymbolF (Application sigma [x, y]) `gives` xy     $ "ApplySymbolF"
    , BottomF      (Bottom sort)              `gives` mempty $ "BottomF"
    , CeilF        (Ceil sort sort x)         `gives` x      $ "CeilF"
    , DomainValueF (DomainValue sort x)       `gives` x      $ "DomainValueF"
    , EqualsF      (Equals sort sort x y)     `gives` xy     $ "EqualsF"
    , FloorF       (Floor sort sort x)        `gives` x      $ "FloorF"
    , IffF         (Iff sort x y)             `gives` xy     $ "IffF"
    , ImpliesF     (Implies sort x y)         `gives` xy     $ "ImpliesF"
    , InF          (In sort sort x y)         `gives` xy     $ "InF"
    , NextF        (Next sort x)              `gives` x      $ "NextF"
    , NotF         (Not sort x)               `gives` x      $ "NotF"
    , OrF          (Or sort x y)              `gives` xy     $ "OrF"
    , RewritesF    (Rewrites sort x y)        `gives` xy     $ "RewritesF"
    , TopF         (Top sort)                 `gives` mempty $ "TopF"
    -- Binders and variables are the only interesting cases:
    , ExistsF      (Exists sort Mock.x xy)    `gives` y      $ "ExistsF - Bound"
    , ExistsF      (Exists sort Mock.x y)     `gives` y      $ "ExistsF - Free"
    , ForallF      (Forall sort Mock.x xy)    `gives` y      $ "ForallF - Bound"
    , ForallF      (Forall sort Mock.x y)     `gives` y      $ "ForallF - Free"
    , VariableF    Mock.x                     `gives` x      $ "VariableF"
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol
    x = FreeVariables.insert Mock.x mempty
    y = FreeVariables.insert Mock.y mempty
    xy = x <> y
    gives
        :: GHC.HasCallStack
        => TermLikeF Variable (FreeVariables Variable)
        -> FreeVariables Variable
        -> String
        -> TestTree
    gives original expected name =
        testCase name $ do
            let actual = synthetic (() :< original)
            assertEqual "" expected actual
