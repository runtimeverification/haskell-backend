{-|
Module      : Test.Kore.ASTUtils.AlphaCompare
Description : Compare
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Test.Kore.ASTUtils.AlphaCompare where

import           Hedgehog
                 ( Gen )
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

import Control.Monad
       ( when )

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.ASTUtils.AlphaCompare
import Kore.Step.Pattern

import           Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock

test_alphaComparePositives :: TestTree
test_alphaComparePositives =
    testProperty "alphaCompare x x == True" $ Hedgehog.property $ do
        x :: CommonStepPattern Object <- Hedgehog.forAll stepPatternGen
        Hedgehog.assert (alphaEq x x)

test_alphaCompareNegatives :: TestTree
test_alphaCompareNegatives =
    testProperty "x /y ==> alphaCompare x y == False" $ Hedgehog.property $ do
        (x, y) <- Hedgehog.forAll pairs
        when (x == y) Hedgehog.discard
        Hedgehog.assert (not $ alphaEq x y)
  where
    pairs :: Gen (CommonStepPattern Object, CommonStepPattern Object)
    pairs = (,) <$> stepPatternGen <*> stepPatternGen

test_alphaEq1 :: TestTree
test_alphaEq1 =
    testProperty "(forall a. a) = (forall b. b)" $ Hedgehog.property $ do
        let forall1 = mkForall v1 (mkVar v1)
            forall2 = mkForall v2 (mkVar v2)
        Hedgehog.assert (alphaEq forall1 forall2)

test_alphaEqList :: TestTree
test_alphaEqList =
    testProperty "forall a. [a, x] = forall b. [b, x]" $ Hedgehog.property $ do
        let forall1 = mkForall v1 $ Mock.builtinList [mkVar v1, mkVar v3]
            forall2 = mkForall v2 $ Mock.builtinList [mkVar v2, mkVar v3]
        Hedgehog.assert (alphaEq forall1 forall2)

test_alphaEqMap :: TestTree
test_alphaEqMap =
    testProperty
        "(forall a. x |-> a) = (forall b. x |-> b)"
        $ Hedgehog.property $ do
            let forall1 = mkForall v1 $ Mock.builtinMap [(mkTop_, mkVar v1)]
                forall2 = mkForall v2 $ Mock.builtinMap [(mkTop_, mkVar v2)]
            Hedgehog.assert (alphaEq forall1 forall2)

s :: Sort Object
s = mkSort "S"

v1, v2, v3 :: Variable Object
v1 = varS "a" s
v2 = varS "b" s
v3 = varS "c" s
