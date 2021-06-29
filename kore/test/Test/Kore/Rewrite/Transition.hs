module Test.Kore.Rewrite.Transition (
    test_ifte,
) where

import Kore.Rewrite.Transition
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_ifte :: [TestTree]
test_ifte =
    [ testGroup
        "\"else\" branch"
        [ testCase "returns value" $ do
            let thenBranch () = return True
                elseBranch = return False
            checkElse empty thenBranch elseBranch
        , testCase "returns multiple values" $ do
            let thenBranch () = return True
                elseBranch = return False <|> return False
            checkElse empty thenBranch elseBranch
        , testCase "is empty when branch is empty" $ do
            let thenBranch () = return True
                elseBranch = empty
                condition = empty
            checkElse condition thenBranch elseBranch
        , testCase "forgets accumulator from conditional" $ do
            let thenBranch () = return True
                elseBranch = return False
                condition = addRule 0 >> empty
            checkElse condition thenBranch elseBranch
        , testCase "takes accumulator from branch" $ do
            let thenBranch () = return True
                elseBranch = addRule 2 >> return False
            checkElse empty thenBranch elseBranch
        ]
    , testGroup
        "\"then\" branch"
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
        , testCase "is empty when branch is empty" $ do
            let thenBranch () = empty
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
        , testCase "takes accumulator from branch" $ do
            let thenBranch () = addRule 1 >> return True
                elseBranch = return False
                condition = addRule 0 >> return ()
            checkThen condition thenBranch elseBranch
        ]
    ]
  where
    check ::
        HasCallStack =>
        (Debug a, Diff a) =>
        Transition Integer a ->
        Transition Integer a ->
        Assertion
    check = on (assertEqual "") runTransition

    checkThen ::
        HasCallStack =>
        Transition Integer a ->
        (a -> Transition Integer Bool) ->
        Transition Integer Bool ->
        Assertion
    checkThen condition thenBranch elseBranch =
        let expect = condition >>= thenBranch
            actual = ifte condition thenBranch elseBranch
         in check expect actual

    checkElse ::
        HasCallStack =>
        Transition Integer a ->
        (a -> Transition Integer Bool) ->
        Transition Integer Bool ->
        Assertion
    checkElse condition thenBranch elseBranch =
        let expect = elseBranch
            actual = ifte condition thenBranch elseBranch
         in check expect actual
