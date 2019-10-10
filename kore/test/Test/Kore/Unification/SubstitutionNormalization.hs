{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Unification.SubstitutionNormalization
    ( test_normalize
    ) where

import Test.Tasty

import Control.Exception
    ( evaluate
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import qualified Kore.Internal.Predicate as Predicate
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
import Kore.Unparser
    ( unparse
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_normalize :: [TestTree]
test_normalize =
    [ test "empty substitution"
        []
        []
        []
    , test "normalized substitution"
        [(y, a)]
        [(y, a)]
        []
    , test "unnormalized substitution, variable-only"
        [(y, mkVar x), (x, a)]
        [(x, a), (y, a)]
        []
    , test "unnormalized substitution, variable under symbol"
        [(y, sigma (mkVar x) b), (x, a)]
        [(x, a), (y, sigma a b)]
        []
    , testGroup "element-variable-only cycle"
        [ test "length 1, alone"
            [(x, mkVar x)]
            []
            []
        , test "length 1, beside related substitution"
            [(x, mkVar x), (z, mkVar x)]
            [(z, mkVar x)]
            []
        , test "length 1, beside unrelated substitution"
            [(x, mkVar x), (z, a)]
            [(z, a)]
            []
        , testCase "length 2" $ assertVariableOnlyCycle
            $ normalizeSubstitution [(x, mkVar y), (y, mkVar x)]
        ]
    , testGroup "set-variable-only cycle"
        [ test "length 1, alone"
            [(xs, mkVar xs)]
            []
            []
        , test "length 1, beside related substitution"
            [(xs, mkVar xs), (ys, mkVar xs)]
            [(ys, mkVar xs)]
            []
        , test "length 1, beside unrelated substitution"
            [(xs, mkVar xs), (z, a)]
            [(z, a)]
            []
        , testCase "length 2" $ assertVariableOnlyCycle
            $ normalizeSubstitution [(xs, mkVar ys), (ys, mkVar xs)]
        ]
    , testGroup "element variable simplifiable cycle"
        [ test "length 1, alone"
            [(x, f (mkVar x))]
            []
            [(x, f (mkVar x))]
        , test "length 1, beside related substitution"
            [(x, f (mkVar x)), (y, mkVar x)]
            [(y, mkVar x)]
            [(x, f (mkVar x))]
        , test "length 1, beside unrelated substitution"
            [(x, f (mkVar x)), (y, a)]
            [(y, a)]
            [(x, f (mkVar x))]
        , test "length 1, beside unrelated substitutions"
            [(x, f (mkVar x)), (y, g (mkVar z)), (z, b)]
            [(z, b), (y, g b)]
            [(x, f (mkVar x))]
        , test "length 1, with constructor"
            [(x, (constr1 . f) (mkVar x))]
            []
            [(x, (constr1 . f) (mkVar x))]
        , test "length 2, alone"
            [(x, f (mkVar y)), (y, g (mkVar x))]
            []
            [(x, f (mkVar y)), (y, g (mkVar x))]
        , test "length 2, beside related substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, mkVar y)]
            [(z, mkVar y)]
            [(x, f (mkVar y)), (y, g (mkVar x))]
        , test "length 2, beside unrelated substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, a)]
            [(z, a)]
            [(x, f (mkVar y)), (y, g (mkVar x))]
        , test "length 2, with And"
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
            []
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
        ]
    , testGroup "set variable simplifiable cycle"
        [ test "length 1, alone"
            [(xs, f (mkVar xs))]
            []
            [(xs, f (mkVar xs))]
        , test "length 1, beside related substitution"
            [(xs, f (mkVar xs)), (ys, mkVar xs)]
            [(ys, mkVar xs)]
            [(xs, f (mkVar xs))]
        , test "length 1, beside unrelated substitution"
            [(xs, f (mkVar xs)), (ys, a)]
            [(ys, a)]
            [(xs, f (mkVar xs))]
        , test "length 1, beside unrelated substitutions"
            [(xs, f (mkVar xs)), (y, g (mkVar z)), (z, b)]
            [(z, b), (y, g b)]
            [(xs, f (mkVar xs))]
        , test "length 2, alone"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            []
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
        , test "length 2, beside related substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, mkVar ys)]
            [(z, mkVar ys)]
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
        , test "length 2, beside unrelated substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, a)]
            [(z, a)]
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
        , test "length 2, with And"
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            []
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
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
            []
        , test "beside unrelated substitution"
            [(xs, constr1 (mkVar xs)), (z, a)]
            [(xs, mkBottom testSort), (z, a)]
            []
        , test "beside related substitution"
            [(xs, constr1 (mkVar xs)), (ys, f (mkVar xs))]
            [(xs, mkBottom testSort), (ys, f (mkBottom testSort))]
            []
        ]
    ]
  where
    test
        :: GHC.HasCallStack
        => TestName
        -> Map (UnifiedVariable Variable) (TermLike Variable)
        -- ^ Test input
        -> UnwrappedSubstitution Variable
        -- ^ Expected normalized output
        -> UnwrappedSubstitution Variable
        -- ^ Expected denormalized output
        -> TestTree
    test testName input normalized denormalized =
        testGroup testName
            [ testCase "normalize" $ do
                let actual = normalize input
                let expect = Normalization { normalized, denormalized }
                assertEqual "" (Just expect) actual
            , testCase "normalizeSubstitution" $ do
                let actual = normalizeSubstitution input
                let expect
                      | null denormalized =
                        Right
                        $ Predicate.fromSubstitution
                        $ Substitution.wrap normalized
                      | otherwise =
                        Left $ SimplifiableCycle (fst <$> denormalized)
                assertEqual "" expect actual
            ]

    testBottom
        :: GHC.HasCallStack
        => TestName
        -> Map (UnifiedVariable Variable) (TermLike Variable)
        -- ^ Test input
        -> TestTree
    testBottom testName input =
        testGroup testName
            [ testCase "normalize" $ do
                let actual = normalize input
                assertEqual "" Nothing actual
            , testCase "normalizeSubstitution" $ do
                let Right actual = normalizeSubstitution input
                    message =
                        (show . Pretty.vsep)
                            [ "Expected \\bottom, but found:"
                            , Pretty.indent 4 (unparse actual)
                            ]
                assertBool message (isBottom actual)
            ]

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

assertVariableOnlyCycle :: a -> IO ()
assertVariableOnlyCycle anything =
    assertErrorIO
        (assertSubstring ""
            "order on variables should prevent variable-only cycles"
        )
        (evaluate anything)
