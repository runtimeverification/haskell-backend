module Test.Kore.Step.Transition
    ( test_ifte
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Step.Transition

import Test.Tasty.HUnit.Ext

test_ifte :: [TestTree]
test_ifte =
    [ testCase "chooses \"else\" branch" $ do
        let expect = return False
            actual =
                ifte
                    (empty :: Transition Integer Integer)
                    (\_ -> return True)
                    (return False)
        on (assertEqual "") runTransition expect actual
    , testCase "chooses the \"then\" branch" $ do
        let expect = return True
            actual =
                ifte
                    (return 1 :: Transition Integer Integer)
                    (\_ -> return True)
                    (return False)
        on (assertEqual "") runTransition expect actual
    ]
