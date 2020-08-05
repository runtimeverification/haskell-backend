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
            let thenBranch () = return True
                elseBranch = return False
            checkElse empty thenBranch elseBranch
        , testCase "returns multiple values" $ do
            let thenBranch () = return True
                elseBranch = return False <|> return False
            checkElse empty thenBranch elseBranch
        , testCase "forgets accumulator from conditional" $ do
            let thenBranch () = return True
                elseBranch = return False
                condition = addRule 0 >> empty
            checkElse condition thenBranch elseBranch
        ]
    , testGroup "\"then\" branch"
        [ testCase "returns value" $ do
            let thenBranch () = return True
                elseBranch = return False
                condition = return ()
            checkThen condition thenBranch elseBranch
        , testCase "returns multiple values" $ do
            let thenBranch () = return True <|> return True
                elseBranch = return False
                condition = return ()
            checkThen condition thenBranch elseBranch
        , testCase "branches on multiple values" $ do
            let thenBranch () = return True
                elseBranch = return False
                condition = return () <|> return ()
            checkThen condition thenBranch elseBranch
        , testCase "remembers accumulator from conditional" $ do
            let thenBranch () = return True
                elseBranch = return False
                condition = addRule 0 >> return ()
            checkThen condition thenBranch elseBranch
        ]
    ]
  where
    check
        :: HasCallStack
        => (Debug a, Diff a)
        => Transition Integer a
        -> Transition Integer a
        -> Assertion
    check = on (assertEqual "") runTransition

    checkThen
        :: HasCallStack
        => Transition Integer a
        -> (a -> Transition Integer Bool)
        -> Transition Integer Bool
        -> Assertion
    checkThen condition thenBranch elseBranch =
        let expect = condition >>= thenBranch
            actual = ifte condition thenBranch elseBranch
        in check expect actual

    checkElse
        :: HasCallStack
        => Transition Integer a
        -> (a -> Transition Integer Bool)
        -> Transition Integer Bool
        -> Assertion
    checkElse condition thenBranch elseBranch =
        let expect = elseBranch
            actual = ifte condition thenBranch elseBranch
        in check expect actual
