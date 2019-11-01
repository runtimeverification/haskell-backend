module Test.Kore.Attribute.Pattern.NonSimplifiable where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Internal.TermLike

import qualified Test.Kore.Step.MockSymbols as Mock

test_TermLike :: [TestTree]
test_TermLike =
    [ testCase "Non-simplifiable BuiltinInt" $
        Mock.builtinInt 3 `shouldBeNonSimplifiable` True
    , testCase "Non-simplifiable BuiltinBool" $
        Mock.builtinBool True `shouldBeNonSimplifiable` True
    , testCase "Non-simplifiable BuiltinString" $
        Mock.builtinString "test" `shouldBeNonSimplifiable` True
    , testCase "Non-simplifiable DomainValue" $
        domainValue `shouldBeNonSimplifiable` True
    , testCase "Simplifiable BuiltinSet" $
        Mock.builtinSet [Mock.a, Mock.b] `shouldBeNonSimplifiable` False
    , testCase "Single constructor is non-simplifiable" $
        Mock.a `shouldBeNonSimplifiable` True
    , testCase "Non-simplifiable with constructor at the top" $
        Mock.constr10 (Mock.builtinInt 3) `shouldBeNonSimplifiable` True
    , testCase "Simplifiable pattern contains symbol which is only functional" $
        Mock.constr10 (Mock.f Mock.a) `shouldBeNonSimplifiable` False
    , testCase "Non-simplifiable pattern with constructor and sort injection" $
        Mock.constr10
            ( Mock.sortInjection
                Mock.testSort
                (Mock.builtinInt 3)
            )
        `shouldBeNonSimplifiable` True
    , testCase "Two consecutive sort injections are simplifiable" $
        Mock.sortInjection
            Mock.intSort
            ( Mock.sortInjection
                Mock.testSort
                (Mock.builtinInt 3
                )
            )
        `shouldBeNonSimplifiable` False
    , testCase "Non-simplifiable pattern with two non-consecutive sort injections" $
        Mock.sortInjection
            Mock.intSort
            ( Mock.constr10
                ( Mock.sortInjection
                    Mock.testSort
                    (Mock.builtinInt 3)
                )
            )
        `shouldBeNonSimplifiable` True
    ]
  where
    domainValue =
        mkDomainValue
            ( DomainValue
                Mock.testSort
                (mkStringLiteral "testDV")
            )

shouldBeNonSimplifiable
    :: TermLike Variable
    -> Bool
    -> IO ()
shouldBeNonSimplifiable term expected = do
    let actual = isNonSimplifiable term
    assertEqual "" actual expected
