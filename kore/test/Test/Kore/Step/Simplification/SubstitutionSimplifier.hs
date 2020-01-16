{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Step.Simplification.SubstitutionSimplifier
    ( test_SubstitutionSimplifier
    ) where

import Test.Tasty

import qualified GHC.Stack as GHC

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    )
import qualified Kore.Step.Simplification.SubstitutionSimplifier as Simplification
import Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationOrSubstitutionError (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
import qualified Kore.Unification.SubstitutionSimplifier as Unification
    ( substitutionSimplifier
    )
import Kore.Unification.UnifierT
    ( runUnifierT
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
    ( runSimplifier
    )
import Test.Tasty.HUnit.Ext

test_SubstitutionSimplifier :: [TestTree]
test_SubstitutionSimplifier =
    [ test "empty substitution"
        []
        [ mempty ]
    , test "normalized substitution"
        [(y, a)]
        [ Normalization [(y, a)] [] ]
    , test "unnormalized substitution, variable-only"
        [(y, mkVar x), (x, a)]
        [ Normalization [(x, a), (y, a)] [] ]
    , test "unnormalized substitution, variable under symbol"
        [(y, sigma (mkVar x) b), (x, a)]
        [ Normalization [(x, a), (y, sigma a b)] [] ]
    , test "simplification generates substitution"
        [(x, sigma (mkAnd a (mkVar y)) b)]
        [ Normalization [(x, sigma a b), (y, a)] [] ]
    , testGroup "element-variable-only cycle"
        [ test "length 1, alone"
            [(x, mkVar x)]
            [ mempty ]
        , test "length 1, beside related substitution"
            [(x, mkVar x), (z, f (mkVar x))]
            [ Normalization [(z, f (mkVar x))] [] ]
        , test "length 1, beside unrelated substitution"
            [(x, mkVar x), (z, a)]
            [ Normalization [(z, a)] [] ]
        ]
    , testGroup "set-variable-only cycle"
        [ test "length 1, alone"
            [(xs, mkVar xs)]
            [ mempty ]
        -- UnificationError: UnsupportedPatterns
        -- , test "length 1, beside related substitution"
        --     [(xs, mkVar xs), (ys, mkVar xs)]
        --     [([(ys, mkVar xs)], [])]
        , test "length 1, beside unrelated substitution"
            [(xs, mkVar xs), (z, a)]
            [ Normalization [(z, a)] [] ]
        ]
    , testGroup "element variable simplifiable cycle"
        [ test "length 1, alone"
            [(x, f (mkVar x))]
            [ Normalization [] [(x, f (mkVar x))] ]
        , test "length 1, beside related substitution"
            [(x, f (mkVar x)), (y, g (mkVar x))]
            [ Normalization [(y, g (mkVar x))] [(x, f (mkVar x))] ]
        , test "length 1, beside unrelated substitution"
            [(x, f (mkVar x)), (y, a)]
            [ Normalization [(y, a)] [(x, f (mkVar x))] ]
        , test "length 1, beside unrelated substitutions"
            [(x, f (mkVar x)), (y, g (mkVar z)), (z, b)]
            [ Normalization [(z, b), (y, g b)] [(x, f (mkVar x))] ]
        , test "length 1, with constructor"
            [(x, (constr1 . f) (mkVar x))]
            [ Normalization [] [(x, (constr1 . f) (mkVar x))] ]
        , test "length 2, alone"
            [(x, f (mkVar y)), (y, g (mkVar x))]
            [ Normalization [] [(x, f (mkVar y)), (y, g (mkVar x))] ]
        , test "length 2, beside related substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, h (mkVar y))]
            [ Normalization
                [(z, h (mkVar y))]
                [(x, f (mkVar y)), (y, g (mkVar x))]
            ]
        , test "length 2, beside unrelated substitution"
            [(x, f (mkVar y)), (y, g (mkVar x)), (z, a)]
            [ Normalization [(z, a)] [(x, f (mkVar y)), (y, g (mkVar x))] ]
        , test "two cycles"
            [(x, f (mkVar x)), (y, g (mkVar y)), (z, c)]
            [ Normalization [(z, c)] [(x, f (mkVar x)), (y, g (mkVar y))] ]
        ]
    , testGroup "set variable simplifiable cycle"
        [ test "length 1, alone"
            [(xs, f (mkVar xs))]
            [ Normalization [] [(xs, f (mkVar xs))] ]
        -- UnificationError: UnsupportedPatterns
        -- , test "length 1, beside related substitution"
        --     [(xs, f (mkVar xs)), (ys, mkVar xs)]
        --     [([(ys, mkVar xs)], [(xs, f (mkVar xs))])]
        , test "length 1, beside unrelated substitution"
            [(xs, f (mkVar xs)), (ys, a)]
            [ Normalization [(ys, a)] [(xs, f (mkVar xs))] ]
        , test "length 1, beside unrelated substitutions"
            [(xs, f (mkVar xs)), (y, g (mkVar z)), (z, b)]
            [ Normalization [(z, b), (y, g b)] [(xs, f (mkVar xs))] ]
        , test "length 2, alone"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            [ Normalization [] [(xs, f (mkVar ys)), (ys, g (mkVar xs))] ]
        , test "length 2, beside related substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, h (mkVar ys))]
            [ Normalization
                [(z, h (mkVar ys))]
                [(xs, f (mkVar ys)), (ys, g (mkVar xs))]
            ]
        , test "length 2, beside unrelated substitution"
            [(xs, f (mkVar ys)), (ys, g (mkVar xs)), (z, a)]
            [ Normalization [(z, a)] [(xs, f (mkVar ys)), (ys, g (mkVar xs))] ]
        , test "length 2, with And"
            [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            [ Normalization
                []
                [(xs, mkAnd (mkVar ys) a), (ys, mkAnd (mkVar xs) b)]
            ]
        , test "two cycles"
            [(xs, f (mkVar xs)), (ys, g (mkVar ys)), (z, c)]
            [ Normalization [(z, c)] [(xs, f (mkVar xs)), (ys, g (mkVar ys))] ]
        ]
    , test "two simplifiable cycles, set and element variables"
        [(xs, f (mkVar xs)), (y, g (mkVar y)), (z, c)]
        [ Normalization [(z, c)] [(y, g (mkVar y)), (xs, f (mkVar xs))] ]
    , testGroup "element variable non-simplifiable cycle"
        [ test "alone"
            [(x, constr1 (mkVar x))]
            []
        , test "beside simplifiable cycle"
            [(x, sigma (f (mkVar x)) (mkVar x))]
            []
        , test "length 2, with And"
            [(x, mkAnd (mkVar y) a), (y, mkAnd (mkVar x) b)]
            []
        ]
    , testGroup "set variable non-simplifiable cycle"
        [ test "alone"
            [(xs, constr1 (mkVar xs))]
            [ Normalization [(xs, mkBottom testSort)] [] ]
        , test "beside unrelated substitution"
            [(xs, constr1 (mkVar xs)), (z, a)]
            [ Normalization [(xs, mkBottom testSort), (z, a)] [] ]
        , test "beside related substitution"
            [(xs, constr1 (mkVar xs)), (ys, f (mkVar xs))]
            [ Normalization
                [(xs, mkBottom testSort), (ys, f (mkBottom testSort))]
                []
            ]
        ]
    ]
  where
    test
        :: GHC.HasCallStack
        => TestName
        -> [(UnifiedVariable Variable, TermLike Variable)]
        -- ^ Test input
        -> [Normalization Variable]
        -- ^ Expected normalized, denormalized outputs
        -> TestTree
    test testName (Substitution.wrap -> input) results =
        testGroup testName
            [ testCase "simplification" $ do
                let SubstitutionSimplifier { simplifySubstitution } =
                        Simplification.substitutionSimplifier
                actual <- runSimplifier Mock.env
                    $ simplifySubstitution SideCondition.top input
                let expect = Condition.fromNormalizationSimplified <$> results
                    actualConditions = OrCondition.toConditions actual
                    actualSubstitutions =
                        Condition.substitution <$> actualConditions
                assertEqual ""
                    (fixExpectedSorts expect actualConditions)
                    actualConditions
                assertBool "Expected normalized substitutions"
                    (all Substitution.isNormalized actualSubstitutions)
            , testCase "unification" $ do
                let SubstitutionSimplifier { simplifySubstitution } =
                        Unification.substitutionSimplifier
                actual <-
                    runSimplifier Mock.env . runUnifierT
                    $ simplifySubstitution SideCondition.top input
                let expect1 normalization@Normalization { denormalized }
                      | null denormalized =
                        Right $
                            Condition.fromNormalizationSimplified normalization
                      | otherwise =
                        Left . SubstitutionError
                        $ SimplifiableCycle (fst <$> denormalized) normalization
                    expect
                      | null results = Right []
                      | otherwise    = (: []) <$> traverse expect1 results
                    actualConditions = map OrCondition.toConditions <$> actual
                    actualSubstitutions =
                        (map . map) Condition.substitution <$> actualConditions
                    allNormalized = (all . all . all) Substitution.isNormalized
                    expectSorted = case actualConditions of
                        Left _ -> expect
                        Right r ->
                            map (\expct' -> fixExpectedSorts expct' (concat r))
                            <$> expect
                assertEqual ""
                    expectSorted
                    actualConditions
                assertBool "Expected normalized substitutions"
                    (allNormalized actualSubstitutions)
            ]

    fixExpectedSorts expect actual =
        case actual of
            [] -> expect
            first:_ ->
                let sort = Condition.conditionSort first
                in map (Condition.coerceSort sort) expect

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

f, g, h, constr1 :: TermLike Variable -> TermLike Variable
f = Mock.f
g = Mock.g
h = Mock.h
constr1 = Mock.constr10

sigma :: TermLike Variable -> TermLike Variable -> TermLike Variable
sigma = Mock.sigma

testSort :: Sort
testSort = Mock.testSort
