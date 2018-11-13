{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Test.Kore.ASTUtils
    ( test_substitutions
    , test_sortAgreement
    , var
    , var_
    , mkSort
    , dummyEnvironment
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Lens
import           Data.Reflection
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.ASTUtils.Substitution
import Kore.IndexedModule.MetadataTools

import Kore.ASTUtils.AlphaCompare

test_substitutions :: TestTree
test_substitutions = testGroup "Substitutions"
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
    , testCase "subTermForTerm" $
          assertEqual ""
              subTermForTerm
              subTermForTermSolution
    ]

test_sortAgreement :: TestTree
test_sortAgreement = testGroup "Sort agreement"
    [ testCase "sortAgreement1" $
          assertEqual ""
              (sortAgreement1 ^? inPath [1])
              (Just $ Bottom_ (mkSort "X"))
    , testCase "sortAgreement2.1" $
          assertEqual ""
              (sortAgreement2 ^? inPath [0])
              (Just $ Bottom_ (mkSort "Y"))
    , testCase "sortAgreement2.2" $
          assertEqual ""
              (sortAgreement2 ^? (inPath [1] . resultSort ))
              (Just $ mkSort "Y")
    , testCase "predicateSort.1" $
          assertEqual ""
              (dummyEnvironment mkBottom ^? resultSort)
              (Just (predicateSort :: Sort Object))
    , testCase "predicateSort.2" $
          assertEqual ""
              (dummyEnvironment mkTop ^? resultSort)
              (Just (predicateSort :: Sort Object))
    , testCase "predicateSort.3" $
          assertEqual ""
              (dummyEnvironment (mkExists (var_ "a" "A") mkBottom) ^? resultSort)
              (Just (predicateSort :: Sort Object))
    , testGroup "sortAgreementManySimplePatterns" $
          dummyEnvironment sortAgreementManySimplePatterns
    , testGetSetIdentity 5
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

subTermForTerm :: CommonPurePattern Object
subTermForTerm = dummyEnvironment $
    subst (mkOr mkTop mkBottom) (mkAnd mkTop mkBottom) $
    mkImplies (mkOr mkTop mkBottom) mkTop

subTermForTermSolution :: CommonPurePattern Object
subTermForTermSolution = dummyEnvironment $
    mkImplies (mkAnd mkTop mkBottom) mkTop

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

varX :: (Given (SymbolOrAliasSorts Object)) => CommonPurePattern Object
varX = mkVar $ var_ "x" "X"

sortAgreementManySimplePatterns
  :: (Given (SymbolOrAliasSorts Object))
  => [TestTree]
sortAgreementManySimplePatterns = do
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
    shouldHavepredicateSortTwoArgs <-
        [ mkEquals a b
        , mkIn a b
        ]
    shoudlHavepredicateSortOneArg <-
        [ mkCeil a
        , mkFloor a
        ]
    let assert1 = return $ testCase "" $ assertEqual ""
            (getSort shouldHaveSortXOneArg)
            (mkSort "X")
    let assert2 = return $ testCase "" $ assertEqual ""
            (getSort shouldHaveSortXTwoArgs)
            (mkSort "X")
    let assert3 = return $ testCase "" $ assertEqual ""
            (getSort shoudlHavepredicateSortOneArg)
            predicateSort
    let assert4 = return $ testCase "" $ assertEqual ""
            (getSort shouldHavepredicateSortTwoArgs)
            predicateSort
    assert1 ++ assert2 ++ assert3 ++ assert4

substitutionGetSetIdentity a b pat =
  assertEqual ""
  (subst b a pat)
  (subst b a $ subst a b pat)

generatePatterns
  :: Given (SymbolOrAliasSorts Object)
  => Int
  -> [CommonPurePattern Object]
generatePatterns size = genBinaryPatterns size ++ genUnaryPatterns size
genBinaryPatterns
  :: Given (SymbolOrAliasSorts Object)
  => Int
  -> [CommonPurePattern Object]
genBinaryPatterns 0 = []
genBinaryPatterns size = do
  sa <- [1..size-1]
  let sb = size - sa
  a <- generatePatterns sa
  b <- generatePatterns sb
  [mkAnd a b, mkOr a b, mkImplies a b, mkIff a b, mkRewrites a b]
genUnaryPatterns
  :: Given (SymbolOrAliasSorts Object)
  => Int
  -> [CommonPurePattern Object]
genUnaryPatterns 0 = []
genUnaryPatterns 1 = [Var_ $ var_ "x" "X"]
genUnaryPatterns size = do
  a <- generatePatterns (size - 1)
  [mkNot a, mkNext a, mkForall (var $ Text.pack $ show size) a]

--FIXME: Make a proper Tasty generator instead
testGetSetIdentity
  :: Int
  -> TestTree
testGetSetIdentity size = dummyEnvironment $ testGroup "getSetIdent" $ do
  a <- generatePatterns (size `div` 3)
  b <- generatePatterns (size `div` 3)
  pat <- generatePatterns size
  return $ testCase "" $ substitutionGetSetIdentity a b pat

var :: MetaOrObject level => Text -> Variable level
var x =
  Variable (noLocationId x) (mkSort "S")

var_ :: MetaOrObject level => Text -> Text -> Variable level
var_ x s =
  Variable (noLocationId x) (mkSort s)

dummyEnvironment
  :: forall r . MetaOrObject Object
  => (Given (SymbolOrAliasSorts Object) => r)
  -> r
dummyEnvironment = give (dummySymbolOrAliasSorts @Object)

dummySymbolOrAliasSorts :: MetaOrObject level => SymbolOrAliasSorts level
dummySymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult   = mkSort "S"
    }
