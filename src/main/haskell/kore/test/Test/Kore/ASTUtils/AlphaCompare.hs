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

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTUtils.AlphaCompare
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns

import Test.Kore

import Test.Tasty
import Test.Tasty.QuickCheck as QC

test_alphaEq :: TestTree
test_alphaEq = testGroup ""
    [ alphaComparePositives
    , alphaCompareNegatives
    , alphaEq1
    ]

alphaComparePositives :: TestTree
alphaComparePositives =
    QC.testProperty
    "alphaCompare x x == True" $
    forAll (purePatternGen Object) $
    (\(x :: CommonPurePattern Object) -> alphaEq x x)

alphaCompareNegatives :: TestTree
alphaCompareNegatives =
    QC.testProperty
    "x /y ==> alphaCompare x y == False" $
    forAll pairs $
    (\(x, y) -> (x /= y) ==> not (alphaEq x y))
      where
       pairs = do
            a <- purePatternGen Object
            b <- purePatternGen Object
            return (a, b)

alphaEq1 :: TestTree
alphaEq1 =
    QC.testProperty
    "" $
    alphaEq (Forall_ s v1 (Var_ v1)) (Forall_ s v2 (Var_ v2))
      where
        s = mkSort "S"
        v1 = varS "a" s :: Variable Object
        v2 = varS "b" s :: Variable Object
