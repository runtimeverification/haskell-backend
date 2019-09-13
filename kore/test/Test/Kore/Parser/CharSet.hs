module Test.Kore.Parser.CharSet (test_charSet) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( assertBool
    , testCase
    )

import Kore.Parser.CharSet as CharSet

test_charSet :: [TestTree]
test_charSet =
    [ testCase "Testing make, existing value."
        (assertBool "'a' should be in makeSet."
            ('a' `CharSet.elem` makeSet))
    , testCase "Testing make, existing value."
        (assertBool "'B' should be in makeSet."
            ('B' `CharSet.elem` makeSet))

    , testCase "Testing make, non-existing value."
        (assertBool "'A' should not be in makeSet."
            (not ('A' `CharSet.elem` makeSet)))
    , testCase "Testing make, non-existing value."
        (assertBool "';' should not be in makeSet."
            (not (';' `CharSet.elem` makeSet)))
    , testCase "Testing make, extreme value."
        (assertBool "'\\0' should not be in makeSet."
            (not ('\0' `CharSet.elem` makeSet)))
    , testCase "Testing make, extreme value."
        (assertBool "'\\255' should not be in makeSet."
            (not ('\255' `CharSet.elem` makeSet)))
    ]
  where
    makeSet = makeCharSet "aBc"
