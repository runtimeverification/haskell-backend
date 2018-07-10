{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module  Data.Kore.ASTUtils.ASTUtilsTest
    ( astUtilsTests
    ) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Test.Tasty.HUnit                 (assertEqual, testCase)


import           Control.Lens
import           Data.Reflection

import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.AST.Common 
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

astUtilsTests :: TestTree
astUtilsTests = testGroup "astUtils" [ substitutions, sortAgreement ]

substitutions :: TestTree
substitutions = testGroup "substitutions" 
  [ testCase "subTrivial" $ assertEqual "" subTrivial subTrivialSolution
  , testCase "subShadow"  $ assertEqual "" subShadow subShadowSolution
  , testCase "subAlphaRename1" $ 
      assertEqual "" 
        subAlphaRename1
        subAlphaRename1Solution
  , testCase "subAlphaRename2" $ 
      assertEqual "" 
        (subAlphaRename2 ^? inPath [0]) 
        (Just $ Var_ $ var "b")
  ]

sortAgreement :: TestTree
sortAgreement = testGroup "Sort agreement"
  [ testCase "sortAgreement1" $ 
      assertEqual "" 
        (sortAgreement1 ^? inPath [1])
        (Just $ Bottom_ (testSort "X"))
  , testCase "sortAgreement2.1" $ 
      assertEqual "" 
        (sortAgreement2 ^? inPath [0])
        (Just $ Bottom_ (testSort "Y"))
  , testCase "sortAgreement2.2" $ 
      assertEqual "" 
        (sortAgreement2 ^? (inPath [1] . resultSort ))
        (Just $ testSort "Y")
  , testCase "flexibleSort.1" $ 
      assertEqual ""
        (dummyEnvironment mkBottom ^? resultSort)
        (Just (flexibleSort :: Sort Object))
  , testCase "flexibleSort.2" $ 
      assertEqual ""
        (dummyEnvironment mkTop ^? resultSort)
        (Just (flexibleSort :: Sort Object))
  , testCase "flexibleSort.3" $ 
      assertEqual ""
        (dummyEnvironment (mkExists (var_ "a" "A") mkBottom) ^? resultSort)
        (Just (flexibleSort :: Sort Object))
  , testGroup "testManySimplePatterns" $ 
      dummyEnvironment testManySimplePatterns
  ]


subTrivial :: CommonPurePattern Object 
subTrivial = dummyEnvironment $ 
  subst (Var_ $ var "a") (Var_ $ var "b") $ 
  mkExists (var "p") (Var_ $ var "a")

subTrivialSolution :: CommonPurePattern Object 
subTrivialSolution = dummyEnvironment $ 
  mkExists (var "p") (Var_ $ var "b")

subShadow :: CommonPurePattern Object 
subShadow = dummyEnvironment $ 
  subst (Var_ $ var "a") (Var_ $ var "b") $ 
  mkExists (var "a") (Var_ $ var "q")

subShadowSolution :: CommonPurePattern Object 
subShadowSolution = dummyEnvironment $ 
  mkExists (var "a") (Var_ $ var "q")

subAlphaRename1 :: CommonPurePattern Object 
subAlphaRename1 = dummyEnvironment $ 
  subst (Var_ $ var "a") (Var_ $ var "b") $ 
  mkExists (var "b") (Var_ $ var "q")

subAlphaRename1Solution :: CommonPurePattern Object 
subAlphaRename1Solution = dummyEnvironment $ 
  mkExists (var "b0") (Var_ $ var "q") 

subAlphaRename2 :: CommonPurePattern Object 
subAlphaRename2 = dummyEnvironment $ 
  subst (Var_ $ var "a") (Var_ $ var "b") $ 
  mkExists (var "b") (Var_ $ var "a")

-- subAlphaRename2Solution :: CommonPurePattern Object 
-- subAlphaRename2Solution = dummyEnvironment @Object $ 
--   subst (Var_ $ var "a") (Var_ $ var "b") $ 
--   mkExists (var "b0") (Var_ $ var "b")

-- the a : X forces bottom : X
sortAgreement1 :: CommonPurePattern Object
sortAgreement1 = dummyEnvironment $ 
  mkOr (Var_ $ var_ "a" "X") mkBottom

-- the y : Y should force everything else to be Y
sortAgreement2 :: CommonPurePattern Object
sortAgreement2 = dummyEnvironment $ 
  mkImplies mkBottom $
  mkIff
    (mkEquals (Var_ $ var_ "foo" "X") (Var_ $ var_ "bar" "X"))
    (Var_ $ var_ "y" "Y")

varX :: (Given (MetadataTools Object)) => CommonPurePattern Object
varX = mkVar $ var_ "x" "X"

testManySimplePatterns 
  :: (Given (MetadataTools Object))
  => [TestTree]
testManySimplePatterns = do 
  flexibleZeroArg <- [mkBottom, mkTop]
  (a,b) <- [(varX, flexibleZeroArg), (flexibleZeroArg, varX), (varX, varX)]
  shouldHaveSortXOneArg <- 
    [ mkForall (var "a") varX
    , mkExists (var "a") varX
    , mkNot varX
    , mkNext varX 
    ]
  shouldHaveSortXTwoArgs <- 
    [ mkAnd a b
    , mkOr a b
    , mkImplies a b
    , mkIff a b
    , mkRewrites a b
    ]
  shouldHaveFlexibleSortTwoArgs <- 
    [ mkEquals a b
    , mkIn a b
    ]
  shoudlHaveFlexibleSortOneArg <- 
    [ mkCeil a
    , mkFloor a
    ]
  let assert1 = return $ testCase "" $ assertEqual "" 
       (getSort shouldHaveSortXOneArg) 
       (testSort "X")
  let assert2 = return $ testCase "" $ assertEqual ""
       (getSort shouldHaveSortXTwoArgs)
       (testSort "X")
  let assert3 = return $ testCase "" $ assertEqual "" 
       (getSort shoudlHaveFlexibleSortOneArg)
       flexibleSort
  let assert4 = return $ testCase "" $ assertEqual "" 
       (getSort shouldHaveFlexibleSortTwoArgs)
       flexibleSort
  assert1 ++ assert2 ++ assert3 ++ assert4 

var :: MetaOrObject level => String -> Variable level
var x = 
  Variable (noLocationId x) (testSort "S")  


var_ :: MetaOrObject level => String -> String -> Variable level
var_ x s = 
  Variable (noLocationId x) (testSort s) 

dummyEnvironment
  :: forall r . MetaOrObject Object 
  => (Given (MetadataTools Object) => r) 
  -> r
dummyEnvironment = give (dummyMetadataTools @Object)

dummyMetadataTools 
  :: MetaOrObject level 
  => MetadataTools level
dummyMetadataTools = MetadataTools
    { isConstructor    = const True 
    , isFunctional     = const True 
    , isFunction       = const True
    , getArgumentSorts = const [] 
    , getResultSort    = const $ testSort "S"
    }

testSort 
  :: MetaOrObject level 
  => String
  -> Sort level
testSort name =
  SortVariableSort $ SortVariable
    { getSortVariable = noLocationId name } --FIXME
