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
        [ testCase "chooses value" $ do
            let expect = return False
                actual =
                    ifte
                        empty
                        (\() -> return True)
                        (return False)
            check expect actual
        ]
    , testGroup "\"then\" branch"
        [ testCase "chooses value" $ do
            let expect = return True
                actual =
                    ifte
                        (return ())
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
