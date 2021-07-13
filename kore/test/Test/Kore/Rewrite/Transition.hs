module Test.Kore.Rewrite.Transition (
    test_ifte,
    test_record,
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

test_record :: [TestTree]
test_record =
    [ testCase "no results" $ do
        let expect = []
            transit = empty
        check expect transit
    , testCase "empty record" $ do
        let expect = [[]]
            transit = return ()
        check expect transit
    , testCase "multiple empty branches" $ do
        let expect = [[], [], []]
            transit = return () <|> return () <|> return ()
        check expect transit
    , testCase "added rules" $ do
        let expect = [[1, 2, 3]]
            transit = addRules [1, 2, 3]
        check expect transit
    , testCase "separate branches" $ do
        let numbers = [[1, 2], [3, 4], [5, 6]]
        let expect = numbers
            transit = asum $ map addRules numbers
        check expect transit
    , testCase "add rule after branching" $ do
        let before = return () <|> return () <|> return ()
            expect = [[1], [1], [1]]
            transit = addRule 1
        checkWith before expect transit
    , testCase "common prefix" $ do
        let expect = [[1, 2], [1, 3], [1, 4]]
            transit = addRule 1 >> asum (map addRule [2, 3, 4])
        check expect transit
    , testCase "behaves like Control.Monad.Writer.listen" $ do
        let before = addRule 1
            expect = [[2, 3]]
            transit = addRules [2, 3]
        checkWith before expect transit
    ]
  where
    check ::
        HasCallStack =>
        [[Integer]] ->
        Transition Integer a ->
        Assertion
    check = checkWith (return ())

    -- Allows running some Transition action before the recorded action.
    checkWith ::
        HasCallStack =>
        Transition Integer a ->
        [[Integer]] ->
        Transition Integer b ->
        Assertion
    checkWith before expected transition =
        let branchResults = runTransition $ before >> record transition
            branchRecords = map (toList . snd . fst) branchResults
         in assertEqual "" expected branchRecords
