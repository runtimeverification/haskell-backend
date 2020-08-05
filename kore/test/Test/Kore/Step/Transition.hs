module Test.Kore.Step.Transition
    ( test_ifte
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Step.Transition

import Test.Tasty.HUnit.Ext

test_ifte :: [TestTree]
test_ifte =
    [ testGroup "\"else\" branch"
        [ testCase "returns value" $ do
            let expect = return False
                actual =
                    ifte
                        empty
                        (\() -> return True)
                        (return False)
            check expect actual
        , testCase "returns multiple values" $ do
            let expect, actual :: Transition Integer Integer
                expect = return 1 <|> return 2
                actual =
                    ifte
                        empty
                        (\() -> return 0)
                        (return 1 <|> return 2)
            check expect actual
        , testCase "forgets accumulator from conditional" $ do
            let expect = return False
                actual =
                    ifte
                        (addRule 0 >> empty)
                        (\() -> return True)
                        (return False)
            check expect actual
        ]
    , testGroup "\"then\" branch"
        [ testCase "returns value" $ do
            let expect = return True
                actual =
                    ifte
                        (return ())
                        (\() -> return True)
                        (return False)
            check expect actual
        , testCase "returns multiple values" $ do
            let expect, actual :: Transition Integer Integer
                expect = return 1 <|> return 2
                actual =
                    ifte
                        (return ())
                        (\() -> return 1 <|> return 2)
                        (return 0)
            check expect actual
        , testCase "branches on multiple values" $ do
            let expect = return True <|> return True
                actual =
                    ifte
                        (return () <|> return ())
                        (\() -> return True)
                        (return False)
            check expect actual
        ]
    ]
  where
    check
        :: HasCallStack
        => (Debug a, Diff a)
        => Transition Integer a
        -> Transition Integer a
        -> Assertion
    check expect actual =
        on (assertEqual "") runTransition expect actual
