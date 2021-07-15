module Test.Kore.Internal.From (
    test_Predicate,
) where

import qualified Data.Functor.Foldable as Recursive
import Kore.Internal.From
import Kore.Internal.Predicate (
    Predicate,
    PredicateF (..),
 )
import Kore.Internal.TermLike (mkElemVar)
import Kore.Syntax.And
import Kore.Syntax.Ceil
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Not
import Kore.Syntax.Or
import Kore.Syntax.Variable
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit

fromPredicate ::
    Predicate VariableName ->
    PredicateF VariableName (Predicate VariableName)
fromPredicate predicate =
    let _ :< predicateF = Recursive.project predicate
     in predicateF

test_Predicate :: [TestTree]
test_Predicate =
    [ testCase "\\ceil(f(a))" $ do
        let actual = fromCeil_ (Mock.f Mock.a)
        case fromPredicate actual of
            CeilF Ceil{ceilChild} -> do
                assertEqual "Expected f(a)" (Mock.f Mock.a) ceilChild
            _ -> assertFailure "Expected CeilF"
    , testCase "\\floor(f(a))" $ do
        let actual = fromFloor_ (Mock.f Mock.a)
        case fromPredicate actual of
            FloorF Floor{floorChild} -> do
                assertEqual "Expected f(a)" (Mock.f Mock.a) floorChild
            _ -> assertFailure "Expected FloorF"
    , testCase "\\top()" $ do
        let actual = fromTop_
        case fromPredicate actual of
            TopF _ -> pure ()
            _ -> assertFailure "Expected TopF"
    , testCase "\\bottom()" $ do
        let actual = fromBottom_
        case fromPredicate actual of
            BottomF _ -> pure ()
            _ -> assertFailure "Expected BottomF"
    , testCase "\\equals(f(a), g(b))" $ do
        let actual = fromEquals_ (Mock.f Mock.a) (Mock.g Mock.b)
        case fromPredicate actual of
            EqualsF Equals{equalsFirst, equalsSecond} -> do
                assertEqual "Expected f(a)" (Mock.f Mock.a) equalsFirst
                assertEqual "Expected g(b)" (Mock.g Mock.b) equalsSecond
            _ -> assertFailure "Expected EqualsF"
    , testCase "\\in(f(a), g(b))" $ do
        let actual = fromIn_ (Mock.f Mock.a) (Mock.g Mock.b)
        case fromPredicate actual of
            InF In{inContainedChild, inContainingChild} -> do
                assertEqual "Expected f(a)" (Mock.f Mock.a) inContainedChild
                assertEqual "Expected g(b)" (Mock.g Mock.b) inContainingChild
            _ -> assertFailure "Expected InF"
    , testCase "\\exists(x, \\ceil(f(x)))" $ do
        let actual =
                fromExists
                    Mock.x
                    (fromCeil_ (Mock.f (mkElemVar Mock.x)))
        case fromPredicate actual of
            ExistsF Exists{existsVariable, existsChild} -> do
                assertEqual "Expected x" Mock.x existsVariable
                assertEqual
                    "Expected f(x)"
                    (fromCeil_ (Mock.f (mkElemVar Mock.x)))
                    existsChild
            _ -> assertFailure "Expected ExistsF"
    , testCase "\\forall(x, \\ceil(f(x)))" $ do
        let actual =
                fromForall
                    Mock.x
                    (fromCeil_ (Mock.f (mkElemVar Mock.x)))
        case fromPredicate actual of
            ForallF Forall{forallVariable, forallChild} -> do
                assertEqual "Expected x" Mock.x forallVariable
                assertEqual
                    "Expected f(x)"
                    (fromCeil_ (Mock.f (mkElemVar Mock.x)))
                    forallChild
            _ -> assertFailure "Expected ForallF"
    , testCase "\\and(\\top(), \\bottom())" $ do
        let actual = fromAnd fromTop_ fromBottom_
        case fromPredicate actual of
            AndF And{andFirst, andSecond} -> do
                assertEqual "Expected \\top" fromTop_ andFirst
                assertEqual "Expected \\bottom" fromBottom_ andSecond
            _ -> assertFailure "Expected AndF"
    , testCase "\\or(\\top(), \\bottom())" $ do
        let actual = fromOr fromTop_ fromBottom_
        case fromPredicate actual of
            OrF Or{orFirst, orSecond} -> do
                assertEqual "Expected \\top" fromTop_ orFirst
                assertEqual "Expected \\bottom" fromBottom_ orSecond
            _ -> assertFailure "Expected OrF"
    , testCase "\\implies(\\top(), \\bottom())" $ do
        let actual = fromImplies fromTop_ fromBottom_
        case fromPredicate actual of
            ImpliesF Implies{impliesFirst, impliesSecond} -> do
                assertEqual "Expected \\top" fromTop_ impliesFirst
                assertEqual "Expected \\bottom" fromBottom_ impliesSecond
            _ -> assertFailure "Expected ImpliesF"
    , testCase "\\iff(\\top(), \\bottom())" $ do
        let actual = fromIff fromTop_ fromBottom_
        case fromPredicate actual of
            IffF Iff{iffFirst, iffSecond} -> do
                assertEqual "Expected \\top" fromTop_ iffFirst
                assertEqual "Expected \\bottom" fromBottom_ iffSecond
            _ -> assertFailure "Expected IffF"
    , testCase "\\not(\\top())" $ do
        let actual = fromNot fromTop_
        case fromPredicate actual of
            NotF Not{notChild} -> do
                assertEqual "Expected \\top" fromTop_ notChild
            _ -> assertFailure "Expected NotF"
    ]
