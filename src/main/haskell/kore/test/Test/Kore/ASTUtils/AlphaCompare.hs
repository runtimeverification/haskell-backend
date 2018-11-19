{-|
Module      : Test.Kore.ASTUtils.AlphaCompare
Description : Compare
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Test.Kore.ASTUtils.AlphaCompare
    ( test_alphaEq
    ) where

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.AlphaCompare
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.Step.Pattern

import Test.Kore

import Test.Tasty
import Test.Tasty.QuickCheck as QC

test_alphaEq :: TestTree
test_alphaEq = testGroup ""
    [ alphaComparePositives
    , alphaCompareNegatives
    , alphaEq1
    , alphaEqMap
    , alphaEqList
    ]

alphaComparePositives :: TestTree
alphaComparePositives =
    QC.testProperty
    "alphaCompare x x == True" $
    forAll (stepPatternGen Object) $
    (\(x :: CommonStepPattern Object) -> alphaEq x x)

alphaCompareNegatives :: TestTree
alphaCompareNegatives =
    QC.testProperty
    "x /y ==> alphaCompare x y == False" $
    forAll pairs $
    (\(x, y) -> (x /= y) ==> not (alphaEq x y))
      where
       pairs = (,) <$> stepPatternGen Object <*> stepPatternGen Object

alphaEq1 :: TestTree
alphaEq1 =
    QC.testProperty
    "(forall a. a) = (forall b. b)" $
    alphaEq (Forall_ s v1 (Var_ v1)) (Forall_ s v2 (Var_ v2))

alphaEqList :: TestTree
alphaEqList =
    QC.testProperty
    "forall a. [a, x] = forall b. [b, x]" $
    alphaEq
        (Forall_ s v1
            (DV_ s $ Domain.BuiltinList $ Seq.fromList [Var_ v1, Var_ v3]))
        (Forall_ s v2
            (DV_ s $ Domain.BuiltinList $ Seq.fromList [Var_ v2, Var_ v3]))


alphaEqMap :: TestTree
alphaEqMap =
    QC.testProperty
    "(forall a. x |-> a) = (forall b. x |-> b)" $
    alphaEq
        (Forall_ s v1
            (DV_ s $ Domain.BuiltinMap $ Map.fromList [(Top_ s, Var_ v1)]))
        (Forall_ s v2
            (DV_ s $ Domain.BuiltinMap $ Map.fromList [(Top_ s, Var_ v2)]))

s :: Sort Object
s = mkSort "S"
v1, v2, v3 :: Variable Object
v1 = varS "a" s
v2 = varS "b" s
v3 = varS "c" s
