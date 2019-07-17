module Test.Kore.Attribute.Pattern.FreeSetVariables where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import           Kore.Attribute.Pattern.FreeSetVariables
                 ( FreeSetVariables )
import qualified Kore.Attribute.Pattern.FreeSetVariables as FreeSetVariables
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
    , Exists sort Mock.x x     `gives` x      $ "Exists"
    , Floor sort sort x        `gives` x      $ "Floor"
    , Forall sort Mock.x x     `gives` x      $ "Forall"
    , Iff sort x y             `gives` xy     $ "Iff"
    , Implies sort x y         `gives` xy     $ "Implies"
    , In sort sort x y         `gives` xy     $ "In"
    , Next sort x              `gives` x      $ "Next"
    , Not sort x               `gives` x      $ "Not"
    , Or sort x y              `gives` xy     $ "Or"
    , Rewrites sort x y        `gives` xy     $ "Rewrites"
    , Top sort                 `gives` mempty $ "Top"
    -- Binders and variables are the only interesting cases:
    , Mu Mock.setX xy          `gives` y      $ "Mu - Bound"
    , Mu Mock.setX y           `gives` y      $ "Mu - Free"
    , Nu Mock.setX xy          `gives` y      $ "Nu - Bound"
    , Nu Mock.setX y           `gives` y      $ "Nu - Free"
    ]

test_instance_Synthetic_TermLike :: [TestTree]
test_instance_Synthetic_TermLike =
    [ AndF         (And sort x y)             `gives'` xy     $ "AndF"
    , ApplySymbolF (Application sigma [x, y]) `gives'` xy     $ "ApplySymbolF"
    , BottomF      (Bottom sort)              `gives'` mempty $ "BottomF"
    , CeilF        (Ceil sort sort x)         `gives'` x      $ "CeilF"
    , DomainValueF (DomainValue sort x)       `gives'` x      $ "DomainValueF"
    , EqualsF      (Equals sort sort x y)     `gives'` xy     $ "EqualsF"
    , ExistsF      (Exists sort Mock.x x)     `gives'` x      $ "ExistsF"
    , FloorF       (Floor sort sort x)        `gives'` x      $ "FloorF"
    , ForallF      (Forall sort Mock.x x)     `gives'` x      $ "ForallF"
    , IffF         (Iff sort x y)             `gives'` xy     $ "IffF"
    , ImpliesF     (Implies sort x y)         `gives'` xy     $ "ImpliesF"
    , InF          (In sort sort x y)         `gives'` xy     $ "InF"
    , NextF        (Next sort x)              `gives'` x      $ "NextF"
    , NotF         (Not sort x)               `gives'` x      $ "NotF"
    , OrF          (Or sort x y)              `gives'` xy     $ "OrF"
    , RewritesF    (Rewrites sort x y)        `gives'` xy     $ "RewritesF"
    , TopF         (Top sort)                 `gives'` mempty $ "TopF"
    , VariableF    Mock.x                     `gives'` mempty $ "VariableF"
    -- Binders and variables are the only interesting cases:
    , MuF          (Mu Mock.setX xy)          `gives'` y      $ "MuF - Bound"
    , MuF          (Mu Mock.setX y)           `gives'` y      $ "MuF - Free"
    , NuF          (Nu Mock.setX xy)          `gives'` y      $ "NuF - Bound"
    , NuF          (Nu Mock.setX y)           `gives'` y      $ "NuF - Free"
    , SetVariableF Mock.setX                  `gives'` x      $ "SetVariableF"
    ]
  where
    gives' = gives @(TermLikeF Variable)

sort :: Sort
sort = Mock.testSort

sigma :: Symbol
sigma = Mock.sigmaSymbol

x, y, xy :: FreeSetVariables Variable
x = FreeSetVariables.freeSetVariable Mock.x
y = FreeSetVariables.freeSetVariable Mock.y
xy = x <> y

gives
    :: (Synthetic base (FreeSetVariables Variable), GHC.HasCallStack)
    => base (FreeSetVariables Variable)
    -> FreeSetVariables Variable
    -> String
    -> TestTree
gives original expected name =
    testCase name $ do
        let actual = synthetic original
        assertEqual "" expected actual
