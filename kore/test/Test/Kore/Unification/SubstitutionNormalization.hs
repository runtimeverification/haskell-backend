{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Unification.SubstitutionNormalization
    ( test_normalize
    ) where

import Prelude.Kore

import Test.Tasty

import Control.Exception
    ( evaluate
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.TopBottom
    ( isBottom
    )
import Kore.Unification.Error
    ( SubstitutionError (..)
    )
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
        Normalization
            { normalized = []
            , denormalized = []
            }
    , test "normalized substitution"
        [(y, a)]
        Normalization
            { normalized = [(y, a)]
            , denormalized = []
            }
    , test "unnormalized substitution, variable-only"
        [(y, mkVar x), (x, a)]
        Normalization
            { normalized = [(x, a), (y, a)]
            , denormalized = []
            }
    , test "unnormalized substitution, variable under symbol"
        [(y, sigma (mkVar x) b), (x, a)]
        Normalization
            { normalized = [(x, a), (y, sigma a b)]
            , denormalized = []
            }
    , testGroup "element-variable-only cycle"
        [ test "length 1, alone"
            [(x, mkVar x)]
            Normalization
                { normalized = []
                , denormalized = []
                }
        , test "length 1, beside related substitution"
            [(x, mkVar x), (z, mkVar x)]
            Normalization
                { normalized = [(z, mkVar x)]
                , denormalized = []
                }
        , test "length 1, beside unrelated substitution"
            [(x, mkVar x), (z, a)]
            Normalization
                { normalized = [(z, a)]
                , denormalized = []
                }
        , testCase "length 2" $ assertVariableOnlyCycle
            $ normalizeSubstitution [(x, mkVar y), (y, mkVar x)]
        ]
    , testGroup "set-variable-only cycle"
        [ test "length 1, alone"
            [(xs, mkVar xs)]
            Normalization
                { normalized = []
                , denormalized = []
                }
        , test "length 1, beside related substitution"
            [(xs, mkVar xs), (ys, mkVar xs)]
            Normalization
                { normalized = [(ys, mkVar xs)]
                , denormalized = []
                }
        , test "length 1, beside unrelated substitution"
            [(xs, mkVar xs), (z, a)]
            Normalization
                { normalized = [(z, a)]
                , denormalized = []
                }
        , testCase "length 2" $ assertVariableOnlyCycle
            $ normalizeSubstitution [(xs, mkVar ys), (ys, mkVar xs)]
        ]
    , testGroup "element variable simplifiable cycle"
        [ test "length 1, alone"
            [(x, f (mkVar x))]
            Normalization
                { normalized = []
                , denormalized = [(x, f (mkVar x))]
                }
        , test "length 1, beside related substitution"
            [(x, f (mkVar x)), (y, mkVar x)]
            Normalization
                { normalized = [(y, mkVar x)]
                , denormalized = [(x, f (mkVar x))]
                }
        , test "length 1, beside unrelated substitution"
            [(x, f (mkVar x)), (y, a)]
            Normalization
                { normalized = [(y, a)]
                , denormalized = [(x, f (mkVar x))]
                }
        , test "length 1, beside unrelated substitutions"
            [(x, f (mkVar x)), (y, g (mkVar z)), (z, b)]
            Normalization
                { normalized = [(z, b), (y, g b)]
                , denormalized = [(x, f (mkVar x))]
                }
        , test "length 1, with constructor"
            [(x, (constr1 . f) (mkVar x))]
            Normalization
                { normalized = []
                , denormalized = [(x, (constr1 . f) (mkVar x))]
                }
        , test "length 2, alone"
            [(x, f (mkVar y)), (y, g (mkVar x))]
            Normalization
                { normalized = []
                , denormalized = [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test "length 2, beside related substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, mkVar y)]
            Normalization
                { normalized = [(z, mkVar y)]
                , denormalized = [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test "length 2, beside unrelated substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, a)]
            Normalization
                { normalized = [(z, a)]
                , denormalized = [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test "length 2, with And"
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
            Normalization
                { normalized = []
                , denormalized =
                    [ (x, mkAnd (mkVar y) a)
                    , (y, mkAnd (mkVar x) b)
                    ]
                }
        , test "two cycles"
            [(x, f (mkVar x)), (y, g (mkVar y)), (z, c)]
            Normalization
                { normalized = [(z, c)]
                , denormalized = [(x, f (mkVar x)), (y, g (mkVar y))]
                }
        ]
    , testGroup "set variable simplifiable cycle"
        [ test "length 1, alone"
            [(xs, f (mkVar xs))]
            Normalization
                { normalized = []
                , denormalized = [(xs, f (mkVar xs))]
                }
        , test "length 1, beside related substitution"
            [(xs, f (mkVar xs)), (ys, mkVar xs)]
            Normalization
                { normalized = [(ys, mkVar xs)]
                , denormalized = [(xs, f (mkVar xs))]
                }
        , test "length 1, beside unrelated substitution"
            [(xs, f (mkVar xs)), (ys, a)]
            Normalization
                { normalized = [(ys, a)]
                , denormalized = [(xs, f (mkVar xs))]
                }
        , test "length 1, beside unrelated substitutions"
            [(xs, f (mkVar xs)), (y, g (mkVar z)), (z, b)]
            Normalization
                { normalized = [(z, b), (y, g b)]
                , denormalized = [(xs, f (mkVar xs))]
                }
        , test "length 2, alone"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            Normalization
                { normalized = []
                , denormalized = [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test "length 2, beside related substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, mkVar ys)]
            Normalization
                { normalized = [(z, mkVar ys)]
                , denormalized = [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test "length 2, beside unrelated substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, a)]
            Normalization
                { normalized = [(z, a)]
                , denormalized = [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test "length 2, with And"
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            Normalization
                { normalized = []
                , denormalized =
                    [ (xs, mkAnd (mkVar ys) a)
                    , (ys, mkAnd (mkVar xs) b)
                    ]
                }
        , test "two cycles"
            [(xs, f (mkVar xs)), (ys, g (mkVar ys)), (z, c)]
            Normalization
                { normalized = [(z, c)]
                , denormalized = [(xs, f (mkVar xs)), (ys, g (mkVar ys))]
                }
        ]
    , test "two simplifiable cycles, set and element variables"
        [(xs, f (mkVar xs)), (y, g (mkVar y)), (z, c)]
        Normalization
            { normalized = [(z, c)]
            , denormalized = [(y, g (mkVar y)), (xs, f (mkVar xs))]
            }
    , testGroup "element variable non-simplifiable cycle"
        [ testBottom "alone"
            [(x, constr1 (mkVar x))]
        , testBottom "beside simplifiable cycle"
            [(x, sigma (f (mkVar x)) (mkVar x))]
        ]
    , testGroup "set variable non-simplifiable cycle"
        [ test "alone"
            [(xs, constr1 (mkVar xs))]
            Normalization
                { normalized = [(xs, mkBottom testSort)]
                , denormalized = []
                }
        , test "beside unrelated substitution"
            [(xs, constr1 (mkVar xs)), (z, a)]
            Normalization
                { normalized = [(xs, mkBottom testSort), (z, a)]
                , denormalized = []
                }
        , test "beside related substitution"
            [(xs, constr1 (mkVar xs)), (ys, f (mkVar xs))]
            Normalization
                { normalized =
                    [ (xs, mkBottom testSort)
                    , (ys, f (mkBottom testSort))
                    ]
                , denormalized = []
                }
        ]
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> Map (UnifiedVariable Variable) (TermLike Variable)
        -- ^ Test input
        -> Normalization Variable
        -- ^ Expected output
        -> TestTree
    test testName input normalization =
        testGroup testName
            [ testCase "normalize" $ do
                let actual = normalize input
                let expect = normalization
                assertEqual "" (Just expect) actual
            , testCase "normalizeSubstitution" $ do
                let actual = normalizeSubstitution input
                let expect
                      | null denormalized =
                        Right
                        $ Condition.fromSubstitution
                        $ Substitution.wrap normalized
                      | otherwise =
                        Left $ SimplifiableCycle
                            (fst <$> denormalized)
                            normalization
                assertEqual "" expect actual
            ]
      where
        Normalization { normalized, denormalized } = normalization

    testBottom
        :: HasCallStack
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
                let actual =
                        either (error . show) id
                        $ normalizeSubstitution input
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

a, b, c :: TermLike Variable
a = Mock.a
b = Mock.b
c = Mock.c

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
