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

import Test.Tasty
import Test.Tasty.QuickCheck as QC

import Data.Reflection
       ( give )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTUtils.AlphaCompare
import Kore.ASTUtils.SmartConstructors
import Kore.IndexedModule.MetadataTools
       ( SymbolOrAliasSorts )
import Kore.Step.Pattern

import           Test.Kore
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSymbols as Mock

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
    give symbolOrAliasSorts $
    QC.testProperty
    "(forall a. a) = (forall b. b)" $
    alphaEq (mkForall v1 (mkVar v1)) (mkForall v2 (mkVar v2))

alphaEqList :: TestTree
alphaEqList =
    give symbolOrAliasSorts $
    QC.testProperty
    "forall a. [a, x] = forall b. [b, x]" $
    alphaEq
        (mkForall v1 $ Mock.builtinList [mkVar v1, mkVar v3])
        (mkForall v2 $ Mock.builtinList [mkVar v2, mkVar v3])


alphaEqMap :: TestTree
alphaEqMap =
    give symbolOrAliasSorts $
    QC.testProperty
    "(forall a. x |-> a) = (forall b. x |-> b)" $
    alphaEq
        (mkForall v1 $ Mock.builtinMap [(mkTop, mkVar v1)])
        (mkForall v2 $ Mock.builtinMap [(mkTop, mkVar v2)])

s :: Sort Object
s = mkSort "S"
v1, v2, v3 :: Variable Object
v1 = varS "a" s
v2 = varS "b" s
v3 = varS "c" s

symbolOrAliasSorts :: SymbolOrAliasSorts Object
symbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
