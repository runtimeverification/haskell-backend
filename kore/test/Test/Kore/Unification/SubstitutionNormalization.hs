{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Unification.SubstitutionNormalization (
    test_normalize,
) where

import Data.Map.Strict (
    Map,
 )
import Kore.Internal.Substitution (
    mkUnwrappedSubstitution,
 )
import Kore.Internal.TermLike
import Kore.Unification.SubstitutionNormalization
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_normalize :: [TestTree]
test_normalize =
    [ test
        "empty substitution"
        []
        Normalization
            { normalized = []
            , denormalized = []
            }
    , test
        "normalized substitution"
        [(y, a)]
        Normalization
            { normalized =
                mkUnwrappedSubstitution [(y, a)]
            , denormalized = []
            }
    , -- TODO(Ana): this test should work with x and y swapped
      test
        "unnormalized substitution, variable-only"
        [(x, mkVar y), (y, a)]
        Normalization
            { normalized =
                mkUnwrappedSubstitution [(y, a), (x, a)]
            , denormalized = []
            }
    , test
        "unnormalized substitution, variable under symbol"
        [(y, sigma (mkVar x) b), (x, a)]
        Normalization
            { normalized =
                mkUnwrappedSubstitution [(x, a), (y, sigma a b)]
            , denormalized = []
            }
    , testGroup
        "element-variable-only cycle"
        [ test
            "length 1, alone"
            [(x, mkVar x)]
            Normalization
                { normalized = []
                , denormalized = []
                }
        , test
            "length 1, beside related substitution"
            [(x, mkVar x), (z, mkVar x)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, mkVar x)]
                , denormalized = []
                }
        , test
            "length 1, beside unrelated substitution"
            [(x, mkVar x), (z, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, a)]
                , denormalized = []
                }
        ]
    , testGroup
        "set-variable-only cycle"
        [ test
            "length 1, alone"
            [(xs, mkVar xs)]
            Normalization
                { normalized = []
                , denormalized = []
                }
        , test
            "length 1, beside related substitution"
            [(xs, mkVar xs), (ys, mkVar xs)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(ys, mkVar xs)]
                , denormalized = []
                }
        , test
            "length 1, beside unrelated substitution"
            [(xs, mkVar xs), (z, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, a)]
                , denormalized = []
                }
        ]
    , testGroup
        "element variable simplifiable cycle"
        [ test
            "length 1, alone"
            [(x, f (mkVar x))]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar x))]
                }
        , test
            "length 1, beside related substitution"
            [(x, f (mkVar x)), (y, mkVar x)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(y, mkVar x)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar x))]
                }
        , test
            "length 1, beside unrelated substitution"
            [(x, f (mkVar x)), (y, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(y, a)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar x))]
                }
        , test
            "length 1, beside unrelated substitutions"
            [(x, f (mkVar x)), (y, g (mkVar z)), (z, b)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, b), (y, g b)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar x))]
                }
        , test
            "length 1, with constructor"
            [(x, (constr1 . f) (mkVar x))]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution [(x, (constr1 . f) (mkVar x))]
                }
        , test
            "length 2, alone"
            [(x, f (mkVar y)), (y, g (mkVar x))]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test
            "length 2, beside related substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, mkVar y)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, mkVar y)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test
            "length 2, beside unrelated substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, a)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar y)), (y, g (mkVar x))]
                }
        , test
            "length 2, with And"
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution
                        [ (x, mkAnd (mkVar y) a)
                        , (y, mkAnd (mkVar x) b)
                        ]
                }
        , test
            "two cycles"
            [(x, f (mkVar x)), (y, g (mkVar y)), (z, c)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, c)]
                , denormalized =
                    mkUnwrappedSubstitution [(x, f (mkVar x)), (y, g (mkVar y))]
                }
        ]
    , testGroup
        "set variable simplifiable cycle"
        [ test
            "length 1, alone"
            [(xs, f (mkVar xs))]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution [(xs, f (mkVar xs))]
                }
        , test
            "length 1, beside related substitution"
            [(xs, f (mkVar xs)), (ys, mkVar xs)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(ys, mkVar xs)]
                , denormalized =
                    mkUnwrappedSubstitution [(xs, f (mkVar xs))]
                }
        , test
            "length 1, beside unrelated substitution"
            [(xs, f (mkVar xs)), (ys, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(ys, a)]
                , denormalized =
                    mkUnwrappedSubstitution [(xs, f (mkVar xs))]
                }
        , test
            "length 1, beside unrelated substitutions"
            [(xs, f (mkVar xs)), (y, g (mkVar z)), (z, b)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, b), (y, g b)]
                , denormalized =
                    mkUnwrappedSubstitution [(xs, f (mkVar xs))]
                }
        , test
            "length 2, alone"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution
                        [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test
            "length 2, beside related substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, mkVar ys)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, mkVar ys)]
                , denormalized =
                    mkUnwrappedSubstitution
                        [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test
            "length 2, beside unrelated substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, a)]
                , denormalized =
                    mkUnwrappedSubstitution
                        [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
                }
        , test
            "length 2, with And"
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            Normalization
                { normalized = []
                , denormalized =
                    mkUnwrappedSubstitution
                        [ (xs, mkAnd (mkVar ys) a)
                        , (ys, mkAnd (mkVar xs) b)
                        ]
                }
        , test
            "two cycles"
            [(xs, f (mkVar xs)), (ys, g (mkVar ys)), (z, c)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(z, c)]
                , denormalized =
                    mkUnwrappedSubstitution
                        [(xs, f (mkVar xs)), (ys, g (mkVar ys))]
                }
        ]
    , test
        "two simplifiable cycles, set and element variables"
        [(xs, f (mkVar xs)), (y, g (mkVar y)), (z, c)]
        Normalization
            { normalized =
                mkUnwrappedSubstitution [(z, c)]
            , denormalized =
                mkUnwrappedSubstitution
                    [(y, g (mkVar y)), (xs, f (mkVar xs))]
            }
    , testGroup
        "element variable non-simplifiable cycle"
        [ testBottom
            "alone"
            [(x, constr1 (mkVar x))]
        , testBottom
            "beside simplifiable cycle"
            [(x, sigma (f (mkVar x)) (mkVar x))]
        ]
    , testGroup
        "set variable non-simplifiable cycle"
        [ test
            "alone"
            [(xs, constr1 (mkVar xs))]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution [(xs, mkBottom testSort)]
                , denormalized = []
                }
        , test
            "beside unrelated substitution"
            [(xs, constr1 (mkVar xs)), (z, a)]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution
                        [(xs, mkBottom testSort), (z, a)]
                , denormalized = []
                }
        , test
            "beside related substitution"
            [(xs, constr1 (mkVar xs)), (ys, f (mkVar xs))]
            Normalization
                { normalized =
                    mkUnwrappedSubstitution
                        [ (xs, mkBottom testSort)
                        , (ys, f (mkBottom testSort))
                        ]
                , denormalized = []
                }
        ]
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        -- | Test input
        Map (SomeVariable VariableName) (TermLike VariableName) ->
        -- | Expected output
        Normalization VariableName ->
        TestTree
    test testName input normalization =
        testCase testName $ do
            let actual = normalize input
            let expect = normalization
            assertEqual "" (Just expect) actual

    testBottom ::
        HasCallStack =>
        TestName ->
        -- | Test input
        Map (SomeVariable VariableName) (TermLike VariableName) ->
        TestTree
    testBottom testName input =
        testCase testName $ do
            let actual = normalize input
            assertEqual "" Nothing actual

x, y, z, xs, ys :: SomeVariable VariableName
x = inject Mock.x
y = inject Mock.y
z = inject Mock.z
xs = inject Mock.setX
ys = inject Mock.setY

a, b, c :: TermLike VariableName
a = Mock.a
b = Mock.b
c = Mock.c

f, g, constr1 :: TermLike VariableName -> TermLike VariableName
f = Mock.f
g = Mock.g
constr1 = Mock.constr10

sigma :: TermLike VariableName -> TermLike VariableName -> TermLike VariableName
sigma = Mock.sigma

testSort :: Sort
testSort = Mock.testSort
