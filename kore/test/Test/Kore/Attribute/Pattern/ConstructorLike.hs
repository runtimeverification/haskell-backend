module Test.Kore.Attribute.Pattern.ConstructorLike (
    test_TermLike,
) where

import Kore.Internal.TermLike
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_TermLike :: [TestTree]
test_TermLike =
    [ testCase "Constructor-like BuiltinInt" $
        Mock.builtinInt 3 `shouldBeConstructorLike` True
    , testCase "Constructor-like BuiltinBool" $
        Mock.builtinBool True `shouldBeConstructorLike` True
    , testCase "Constructor-like BuiltinString" $
        Mock.builtinString "test" `shouldBeConstructorLike` True
    , testCase "Constructor-like DomainValue" $
        domainValue `shouldBeConstructorLike` True
    , testCase "Simplifiable empty BuiltinSet" $
        Mock.builtinSet [] `shouldBeConstructorLike` True
    , testCase "Simplifiable constructor-like BuiltinSet" $
        Mock.builtinSet [Mock.a, Mock.b] `shouldBeConstructorLike` True
    , testCase "Simplifiable empty BuiltinMap" $
        Mock.builtinMap [] `shouldBeConstructorLike` True
    , testCase "Simplifiable constructor-like BuiltinMap" $
        Mock.builtinMap [(Mock.a, Mock.c), (Mock.b, Mock.c)]
            `shouldBeConstructorLike` True
    , testCase "Simplifiable non-constructor-like BuiltinMap" $
        Mock.builtinMap [(Mock.a, Mock.c), (Mock.b, Mock.f Mock.c)]
            `shouldBeConstructorLike` False
    , testCase "Single constructor is constructor-like" $
        Mock.a `shouldBeConstructorLike` True
    , testCase "Constructor-like with constructor at the top" $
        Mock.constr10 (Mock.builtinInt 3) `shouldBeConstructorLike` True
    , testCase "Simplifiable pattern contains symbol which is only functional" $
        Mock.constr10 (Mock.f Mock.a) `shouldBeConstructorLike` False
    , testCase "Constructor-like pattern with constructor and sort injection" $
        Mock.constr10
            ( Mock.sortInjection
                Mock.testSort
                (Mock.builtinInt 3)
            )
            `shouldBeConstructorLike` True
    , testCase "Two consecutive sort injections are simplifiable" $
        Mock.sortInjection
            Mock.intSort
            ( Mock.sortInjection
                Mock.testSort
                ( Mock.builtinInt 3
                )
            )
            `shouldBeConstructorLike` False
    , testCase "Constructor-like pattern with two non-consecutive sort injections" $
        Mock.sortInjection
            Mock.intSort
            ( Mock.constr10
                ( Mock.sortInjection
                    Mock.testSort
                    (Mock.builtinInt 3)
                )
            )
            `shouldBeConstructorLike` True
    ]
  where
    domainValue =
        mkDomainValue $ DomainValue Mock.testSort (mkStringLiteral "testDV")

shouldBeConstructorLike ::
    HasCallStack =>
    TermLike VariableName ->
    Bool ->
    IO ()
shouldBeConstructorLike term expected = do
    let actual = isConstructorLike term
    assertEqual "" actual expected
