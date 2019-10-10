{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Unification.SubstitutionNormalization
    ( test_normalizeSubstitution
    ) where

import Test.Tasty

import qualified Data.Map.Strict as Map
import qualified Generics.SOP as SOP
import GHC.Exts
    ( IsList (..)
    )
import qualified GHC.Generics as GHC

import Kore.Debug
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.TermLike
import Kore.TopBottom
    ( isBottom
    )
import Kore.Unification.Error
    ( SubstitutionError (..)
    )
import Kore.Unification.Substitution
    ( UnwrappedSubstitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

data NormalizationResult
    = Substitution ![(UnifiedVariable Variable, TermLike Variable)]
    | SubstitutionBottom
    | Error !SubstitutionError
    deriving (GHC.Generic, Show)

instance IsList NormalizationResult where
    type Item NormalizationResult =
        (UnifiedVariable Variable, TermLike Variable)

    fromList = Substitution
    toList = undefined

instance SOP.Generic NormalizationResult

instance SOP.HasDatatypeInfo NormalizationResult

instance Debug NormalizationResult

instance Diff NormalizationResult

test_normalizeSubstitution :: [TestTree]
test_normalizeSubstitution =
    [ test "empty substitution"
        []
        []
    , test "normalized substitution"
        [(y, a)]
        [(y, a)]
    , test "unnormalized substitution, variable-only"
        [(y, mkVar x), (x, a)]
        [(x, a), (y, a)]
    , test "unnormalized substitution, variable under symbol"
        [(y, sigma (mkVar x) b), (x, a)]
        [(x, a), (y, sigma a b)]
    , testGroup "element-variable-only cycle"
        [ test "length 1, alone"
            [(x, mkVar x)]
            []
        , test "length 1, beside related substitution"
            [(x, mkVar x), (z, mkVar x)]
            [(z, mkVar x)]
        , test "length 1, beside unrelated substitution"
            [(x, mkVar x), (z, a)]
            [(z, a)]
        , testCase "length 2" $ assertVariableOnlyCycle
            $ runNormalizeSubstitution [(x, mkVar y), (y, mkVar x)]
        ]
    , testGroup "set-variable-only cycle"
        [ test "length 1, alone"
            [(xs, mkVar xs)]
            []
        , test "length 1, beside related substitution"
            [(xs, mkVar xs), (ys, mkVar xs)]
            [(ys, mkVar xs)]
        , test "length 1, beside unrelated substitution"
            [(xs, mkVar xs), (z, a)]
            [(z, a)]
        , testCase "length 2" $ assertVariableOnlyCycle
            $ runNormalizeSubstitution [(xs, mkVar ys), (ys, mkVar xs)]
        ]
    , testGroup "element variable simplifiable cycle"
        [ testError "length 1, alone"
            [(x, f (mkVar x))]
            [x]
        , testError "length 1, beside related substitution"
            [(x, f (mkVar x)), (y, mkVar x)]
            [x]
        , testError "length 1, beside unrelated substitution"
            [(x, f (mkVar x)), (y, a)]
            [x]
        , testError "length 1, with constructor"
            [(x, (constr1 . f) (mkVar x))]
            [x]
        , testError "length 2, alone"
            [(x, f (mkVar y)), (y, g (mkVar x))]
            [x, y]
        , testError "length 2, beside related substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, mkVar y)]
            [x, y]
        , testError "length 2, beside unrelated substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, a)]
            [x, y]
        , testError "length 2, with And"
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
            [x, y]
        ]
    , testGroup "set variable simplifiable cycle"
        [ testError "length 1, alone"
            [(xs, f (mkVar xs))]
            [xs]
        , testError "length 1, beside related substitution"
            [(xs, f (mkVar xs)), (ys, mkVar xs)]
            [xs]
        , testError "length 1, beside unrelated substitution"
            [(xs, f (mkVar xs)), (ys, a)]
            [xs]
        , testError "length 2, alone"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            [xs, ys]
        , testError "length 2, beside related substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, mkVar ys)]
            [xs, ys]
        , testError "length 2, beside unrelated substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, a)]
            [xs, ys]
        , testError "length 2, with And"
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            [xs, ys]
        ]
    , testGroup "element variable non-simplifiable cycle"
        [ testBottom "alone"
            [(x, constr1 (mkVar x))]
        , testBottom "beside simplifiable cycle"
            [(x, sigma (f (mkVar x)) (mkVar x))]
        ]
    , testGroup "set variable non-simplifiable cycle"
        [ test "alone"
            [(xs, constr1 (mkVar xs))]
            [(xs, mkBottom testSort)]
        , test "beside unrelated substitution"
            [(xs, constr1 (mkVar xs)), (z, a)]
            [(z, a), (xs, mkBottom testSort)]
        , test "beside related substitution"
            [(xs, constr1 (mkVar xs)), (ys, f (mkVar xs))]
            [(xs, mkBottom testSort), (ys, f (mkBottom testSort))]
        ]
    ]
  where
    test
        :: TestName
        -> UnwrappedSubstitution Variable
        -> NormalizationResult
        -> TestTree
    test testName input expect =
        testCase testName $ do
            actual <- runNormalizeSubstitution input
            assertEqual "" expect actual

    testBottom testName input =
        test testName input SubstitutionBottom

    testError testName input variables =
        test testName input $ Error $ SimplifiableCycle variables

x, y, z, xs, ys :: UnifiedVariable Variable
x = ElemVar Mock.x
y = ElemVar Mock.y
z = ElemVar Mock.z
xs = SetVar Mock.setX
ys = SetVar Mock.setY

a, b :: TermLike Variable
a = Mock.a
b = Mock.b

f, g, constr1 :: TermLike Variable -> TermLike Variable
f = Mock.f
g = Mock.g
constr1 = Mock.constr10

sigma :: TermLike Variable -> TermLike Variable -> TermLike Variable
sigma = Mock.sigma

testSort :: Sort
testSort = Mock.testSort

assertVariableOnlyCycle :: IO a -> IO ()
assertVariableOnlyCycle =
    assertErrorIO $ assertSubstring ""
        "order on variables should prevent variable-only cycles"

runNormalizeSubstitution
    :: [(UnifiedVariable Variable, TermLike Variable)]
    -> IO NormalizationResult
runNormalizeSubstitution substitution = do
    case normalizeSubstitution (Map.fromList substitution) of
        Left err -> return (Error err)
        Right predicate
          | isBottom predicate -> return SubstitutionBottom
          | otherwise ->
            return . Substitution
            . Substitution.unwrap . Conditional.substitution
            $ predicate
