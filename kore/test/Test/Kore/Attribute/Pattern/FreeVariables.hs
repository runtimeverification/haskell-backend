module Test.Kore.Attribute.Pattern.FreeVariables where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import           Kore.Attribute.Pattern.FreeVariables
                 ( FreeVariables )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import           Kore.Attribute.Synthetic
import           Kore.Internal.TermLike
                 ( Symbol, TermLikeF (..) )
import           Kore.Syntax hiding
                 ( PatternF (..) )

import qualified Test.Kore.Step.MockSymbols as Mock

test_Synthetic :: [TestTree]
test_Synthetic =
    [ And sort x y             `gives` xy     $ "And"
    , Application sigma [x, y] `gives` xy     $ "ApplySymbol"
    , Bottom sort              `gives` mempty $ "Bottom"
    , Ceil sort sort x         `gives` x      $ "Ceil"
    , DomainValue sort x       `gives` x      $ "DomainValue"
    , Equals sort sort x y     `gives` xy     $ "Equals"
    , Floor sort sort x        `gives` x      $ "Floor"
    , Iff sort x y             `gives` xy     $ "Iff"
    , Implies sort x y         `gives` xy     $ "Implies"
    , In sort sort x y         `gives` xy     $ "In"
    , Next sort x              `gives` x      $ "Next"
    , Not sort x               `gives` x      $ "Not"
    , Or sort x y              `gives` xy     $ "Or"
    , Rewrites sort x y        `gives` xy     $ "Rewrites"
    , Top sort                 `gives` mempty $ "Top"
    -- Binders and variables are the only interesting cases:
    , Exists sort Mock.x xy    `gives` y      $ "Exists - Bound"
    , Exists sort Mock.x y     `gives` y      $ "Exists - Free"
    , Forall sort Mock.x xy    `gives` y      $ "Forall - Bound"
    , Forall sort Mock.x y     `gives` y      $ "Forall - Free"
    ]

test_instance_Synthetic_TermLike :: [TestTree]
test_instance_Synthetic_TermLike =
    [ AndF         (And sort x y)             `gives'` xy     $ "AndF"
    , ApplySymbolF (Application sigma [x, y]) `gives'` xy     $ "ApplySymbolF"
    , BottomF      (Bottom sort)              `gives'` mempty $ "BottomF"
    , CeilF        (Ceil sort sort x)         `gives'` x      $ "CeilF"
    , DomainValueF (DomainValue sort x)       `gives'` x      $ "DomainValueF"
    , EqualsF      (Equals sort sort x y)     `gives'` xy     $ "EqualsF"
    , FloorF       (Floor sort sort x)        `gives'` x      $ "FloorF"
    , IffF         (Iff sort x y)             `gives'` xy     $ "IffF"
    , ImpliesF     (Implies sort x y)         `gives'` xy     $ "ImpliesF"
    , InF          (In sort sort x y)         `gives'` xy     $ "InF"
    , NextF        (Next sort x)              `gives'` x      $ "NextF"
    , NotF         (Not sort x)               `gives'` x      $ "NotF"
    , OrF          (Or sort x y)              `gives'` xy     $ "OrF"
    , RewritesF    (Rewrites sort x y)        `gives'` xy     $ "RewritesF"
    , TopF         (Top sort)                 `gives'` mempty $ "TopF"
    -- Binders and variables are the only interesting cases:
    , ExistsF      (Exists sort Mock.x xy)    `gives'` y      $ "ExistsF - Bound"
    , ExistsF      (Exists sort Mock.x y)     `gives'` y      $ "ExistsF - Free"
    , ForallF      (Forall sort Mock.x xy)    `gives'` y      $ "ForallF - Bound"
    , ForallF      (Forall sort Mock.x y)     `gives'` y      $ "ForallF - Free"
    , VariableF    Mock.x                     `gives'` x      $ "VariableF"
    ]
  where
    gives' = gives @(TermLikeF Variable)

sort :: Sort
sort = Mock.testSort

sigma :: Symbol
sigma = Mock.sigmaSymbol

x, y, xy :: FreeVariables Variable
x = FreeVariables.insert Mock.x mempty
y = FreeVariables.insert Mock.y mempty
xy = x <> y

gives
    :: (Synthetic base (FreeVariables Variable), GHC.HasCallStack)
    => base (FreeVariables Variable)
    -> FreeVariables Variable
    -> String
    -> TestTree
gives original expected name =
    testCase name $ do
        let actual = synthetic original
        assertEqual "" expected actual
