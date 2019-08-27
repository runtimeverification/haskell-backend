module Test.Kore.Unification.SubstitutionNormalization
    (test_substitutionNormalization) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Monad.Except as Except
import qualified Data.Default as Default
import qualified Data.Map.Strict as Map

import qualified Kore.Internal.Pattern as Conditional
import           Kore.Internal.Symbol
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.SubstitutionNormalization

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.SMT
import           Test.Tasty.HUnit.Extensions

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    [ testCase "Empty substitution" $
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution []
    , testCase "Simple substitution" $
        assertEqualWithExplanation "" (Right [(v1 Mock.testSort, mkTop_)])
            =<< runNormalizeSubstitution [(v1 Mock.testSort, mkTop_)]
    , testCase "Simple unnormalized substitution" $
        assertEqualWithExplanation ""
            (Right
                [ (v1 Mock.testSort, mkTop Mock.testSort)
                , (x1 Mock.testSort, mkTop Mock.testSort)
                ]
            )
            =<< runNormalizeSubstitution
                [ (v1 Mock.testSort, mkVar $ x1 Mock.testSort)
                , (x1 Mock.testSort, mkTop Mock.testSort)
                ]
    , testCase "Unnormalized substitution with 'and'" $
        assertEqualWithExplanation ""
            (Right
                [   ( v1 Mock.testSort
                    , mkAnd mkTop_ (mkTop Mock.testSort)
                    )
                , (x1 Mock.testSort, mkTop Mock.testSort)
                ]
            )
            =<< runNormalizeSubstitution
                [   ( v1 Mock.testSort
                    , mkAnd (mkVar $ x1 Mock.testSort) mkTop_
                    )
                ,   (x1 Mock.testSort, mkTop Mock.testSort)
                ]
    , testCase "Simplest cycle" $ do
        let var1 = v1 Mock.testSort
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution [(var1, mkVar $ v1 Mock.testSort)]
    , testCase "Cycle with extra substitution" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation "" (Right [(varx1, mkVar var1)])
            =<< runNormalizeSubstitution
                    [ (var1, mkVar var1)
                    , (varx1, mkVar var1)
                    ]
    , testCase "Function cycle" $ do
        let var1 = v1 Mock.testSort
        assertEqualWithExplanation ""
            (Left (NonCtorCircularVariableDependency [var1]))
            =<< runNormalizeSubstitution
                [ ( var1 , mkApplySymbol f [mkVar var1] ) ]
    , testCase "Length 2 cycle" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution
                [ (var1, mkVar varx1)
                , (varx1, mkVar var1)
                ]
    , testCase "Cycle with 'and'" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution
                [ (var1, mkAnd (mkVar varx1) mkTop_)
                , (varx1, mkAnd (mkVar var1) mkTop_)
                ]
    , testCase "Length 2 non-ctor cycle" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation ""
            (Left (NonCtorCircularVariableDependency [var1, varx1]))
            =<< runNormalizeSubstitution
                [ (var1, mkApplySymbol f [mkVar varx1])
                , (varx1, mkVar var1)
                ]
    , testCase "Constructor cycle" $
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution
                [ (Mock.x, Mock.constr10 (mkVar Mock.x)) ]
    , testCase "Constructor with side function cycle" $
        assertEqualWithExplanation "" (Right [])
            =<< runNormalizeSubstitution
                [(Mock.x, Mock.constr20 (Mock.f (mkVar Mock.x)) (mkVar Mock.x))]
    , testCase "Constructor with function cycle" $
        assertEqualWithExplanation ""
            (Left (NonCtorCircularVariableDependency [Mock.x]))
            =<< runNormalizeSubstitution
                [ (Mock.x, Mock.constr10 (Mock.f (mkVar Mock.x))) ]
    ]
  where
    v1 :: Sort -> Variable
    v1 = Variable (testId "v1") mempty
    x1 :: Sort -> Variable
    x1 = Variable (testId "x1") mempty
    f = Symbol
        { symbolConstructor = testId "f"
        , symbolParams = []
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts [Mock.testSort] Mock.testSort
        }

runNormalizeSubstitution
    :: [(Variable, TermLike Variable)]
    -> IO (Either SubstitutionError [(Variable, TermLike Variable)])
runNormalizeSubstitution substitution =
    (fmap . fmap) (Substitution.unwrap . Conditional.substitution)
    $ Test.SMT.runSMT
    $ evalSimplifier Mock.env
    $ Except.runExceptT
    $ normalizeSubstitution (Map.fromList substitution)
