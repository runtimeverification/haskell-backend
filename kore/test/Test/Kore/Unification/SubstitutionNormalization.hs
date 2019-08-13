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
import           Kore.TopBottom
                 ( isBottom )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.SubstitutionNormalization
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.SMT
import           Test.Tasty.HUnit.Extensions

data NormalizationResult
  = Substitution ![(UnifiedVariable Variable, TermLike Variable)]
  | SubstitutionBottom
  | Error !SubstitutionError
  deriving (Show)

instance SumEqualWithExplanation NormalizationResult
  where
    sumConstructorPair (Substitution s1) (Substitution s2) =
        SumConstructorSameWithArguments (EqWrap "Substitution" s1 s2)
    sumConstructorPair pattern1@(Substitution _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)
    sumConstructorPair SubstitutionBottom SubstitutionBottom =
        SumConstructorSameNoArguments
    sumConstructorPair pattern1@SubstitutionBottom pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)
    sumConstructorPair (Error s1) (Error s2) =
        SumConstructorSameWithArguments (EqWrap "Error" s1 s2)
    sumConstructorPair pattern1@(Error _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

instance EqualWithExplanation NormalizationResult where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    [ testCase "Empty substitution" $
        assertEqualWithExplanation "" (Substitution [])
            =<< runNormalizeSubstitution []
    , testCase "Simple substitution" $
        assertEqualWithExplanation ""
            (Substitution [(ElemVar $ v1 Mock.testSort, mkTop_)])
            =<< runNormalizeSubstitution [(ElemVar $ v1 Mock.testSort, mkTop_)]
    , testCase "Simple unnormalized substitution" $
        assertEqualWithExplanation ""
            (Substitution
                [ (ElemVar $ v1 Mock.testSort, mkTop Mock.testSort)
                , (ElemVar $ x1 Mock.testSort, mkTop Mock.testSort)
                ]
            )
            =<< runNormalizeSubstitution
                [ (ElemVar $ v1 Mock.testSort, mkElemVar $ x1 Mock.testSort)
                , (ElemVar $ x1 Mock.testSort, mkTop Mock.testSort)
                ]
    , testCase "Unnormalized substitution with 'and'" $
        assertEqualWithExplanation ""
            (Substitution
                [   ( ElemVar $ v1 Mock.testSort
                    , mkAnd mkTop_ (mkTop Mock.testSort)
                    )
                , (ElemVar $ x1 Mock.testSort, mkTop Mock.testSort)
                ]
            )
            =<< runNormalizeSubstitution
                [   (ElemVar $ v1 Mock.testSort
                    , mkAnd (mkElemVar $ x1 Mock.testSort) mkTop_
                    )
                ,   (ElemVar $ x1 Mock.testSort, mkTop Mock.testSort)
                ]
    , testCase "Simplest cycle" $ do
        let var1 = v1 Mock.testSort
        assertEqualWithExplanation "" (Substitution [])
            =<< runNormalizeSubstitution
                [(ElemVar var1, mkElemVar $ v1 Mock.testSort)]
    , testCase "Cycle with extra substitution" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation ""
            (Substitution [(ElemVar varx1, mkElemVar var1)])
            =<< runNormalizeSubstitution
                    [ (ElemVar var1, mkElemVar var1)
                    , (ElemVar varx1, mkElemVar var1)
                    ]
    , testCase "SetVariable Simplest cycle" $ do
        let var1 = Mock.makeTestUnifiedVariable "@x"
        assertEqualWithExplanation "" (Substitution [])
            =<< runNormalizeSubstitution [(var1, mkVar var1)]
    , testCase "SetVariable Cycle with extra substitution" $ do
        let
            var1 = Mock.makeTestUnifiedVariable "@v"
            varx1 = Mock.makeTestUnifiedVariable "@x"
        assertEqualWithExplanation ""
            (Substitution [(varx1, mkVar var1)])
            =<< runNormalizeSubstitution
                    [ (var1, mkVar var1)
                    , (varx1, mkVar var1)
                    ]
    , testCase "Function cycle" $ do
        let var1 = v1 Mock.testSort
        assertEqualWithExplanation ""
            (Error (NonCtorCircularVariableDependency [ElemVar var1]))
            =<< runNormalizeSubstitution
                [ (ElemVar  var1 , mkApplySymbol f [mkElemVar var1] ) ]
    , testCase "onlyThisLength 2 cycle" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertErrorIO
            (assertSubstring ""
                "order on variables should prevent only-variable-cycles"
            )
            (runNormalizeSubstitution
                [ (ElemVar var1, mkElemVar varx1)
                , (ElemVar varx1, mkElemVar var1)
                ]
            )
     , testCase "SetVariable Length 2 cycle" $ do
        let
            var1 = Mock.makeTestUnifiedVariable "@v"
            varx1 = Mock.makeTestUnifiedVariable "@x"
        assertErrorIO
            (assertSubstring ""
                "order on variables should prevent only-variable-cycles"
            )
            (runNormalizeSubstitution
                [ (var1, mkVar varx1)
                , (varx1, mkVar var1)
                ]
            )
     , testCase "Cycle with 'and'" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation ""
            (Error
                (NonCtorCircularVariableDependency
                    [ElemVar var1, ElemVar varx1]
                )
            )
            =<< runNormalizeSubstitution
                [ (ElemVar var1, mkAnd (mkElemVar varx1) mkTop_)
                , (ElemVar varx1, mkAnd (mkElemVar var1) mkTop_)
                ]
     , testCase "SetVariable Cycle with 'and'" $ do
        let
            var1 = Mock.makeTestUnifiedVariable "@v"
            varx1 = Mock.makeTestUnifiedVariable "@x"
        assertEqualWithExplanation ""
            (Error
              (NonCtorCircularVariableDependency [var1, varx1])
            )
            =<< runNormalizeSubstitution
                [ (var1, mkAnd (mkVar varx1) mkTop_)
                , (varx1, mkAnd (mkVar var1) mkTop_)
                ]
    , testCase "Length 2 non-ctor cycle" $ do
        let
            var1 = v1 Mock.testSort
            varx1 = x1 Mock.testSort
        assertEqualWithExplanation ""
            (Error
                (NonCtorCircularVariableDependency [ElemVar var1, ElemVar varx1]
                )
            )
            =<< runNormalizeSubstitution
                [ (ElemVar var1, mkApplySymbol f [mkElemVar varx1])
                , (ElemVar varx1, mkElemVar var1)
                ]
    , testCase "Constructor cycle" $
        assertEqualWithExplanation "" SubstitutionBottom
            =<< runNormalizeSubstitution
                [ (ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.x)) ]
    , testCase "SetVariable Constructor cycle" $ do
        let var1 = Mock.makeTestUnifiedVariable "@x"
        assertEqualWithExplanation ""
            (Substitution [(var1, mkBottom Mock.testSort)])
            =<< runNormalizeSubstitution
                [ (var1, Mock.constr10 (mkVar var1)) ]
    , testCase "Constructor with side function cycle" $
        assertEqualWithExplanation "" SubstitutionBottom
            =<< runNormalizeSubstitution
                [ ( ElemVar Mock.x
                  , Mock.constr20 (Mock.f (mkElemVar Mock.x)) (mkElemVar Mock.x)
                  )
                ]
    , testCase "Constructor with function cycle" $
        assertEqualWithExplanation ""
            (Error (NonCtorCircularVariableDependency [ElemVar Mock.x]))
            =<< runNormalizeSubstitution
                [ (ElemVar Mock.x, Mock.constr10 (Mock.f (mkElemVar Mock.x))) ]
    ]
  where
    v1 :: Sort -> ElementVariable Variable
    v1 = ElementVariable . Variable (testId "v1") mempty
    x1 :: Sort -> ElementVariable Variable
    x1 = ElementVariable . Variable (testId "x1") mempty
    f = Symbol
        { symbolConstructor = testId "f"
        , symbolParams = []
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts [Mock.testSort] Mock.testSort
        }

runNormalizeSubstitution
    :: [(UnifiedVariable Variable, TermLike Variable)]
    -> IO NormalizationResult
runNormalizeSubstitution substitution = do
    normalizedSubstitution <- Test.SMT.runSMT
        $ evalSimplifier Mock.env
        $ Except.runExceptT
        $ normalizeSubstitution (Map.fromList substitution)
    case normalizedSubstitution of
        Left err -> return (Error err)
        Right predicate
          | isBottom predicate -> return SubstitutionBottom
          | otherwise -> return . Substitution
              . Substitution.unwrap . Conditional.substitution
              $ predicate
