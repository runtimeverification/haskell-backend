module Test.Kore.Parser.CharDict (test_charDict) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( assertEqual
    , testCase
    )

import Kore.Parser.CharDict

test_charDict :: [TestTree]
test_charDict =
    [ testCase "Testing make, given value."
        (assertEqual "makeDict['a'] should be 2." (makeDict ! 'a') 2)
    , testCase "Testing make, given value."
        (assertEqual "makeDict['B'] should be 3." (makeDict ! 'B') 3)
    , testCase "Testing make, default value."
        (assertEqual "makeDict['A'] should be 1." (makeDict ! 'A') 1)
    , testCase "Testing make, default value."
        (assertEqual "makeDict['z'] should be 1." (makeDict ! 'z') 1)
    , testCase "Testing make, extreme index."
        (assertEqual "makeDict['\\0'] should be 1." (makeDict ! '\0') 1)
    , testCase "Testing make, extreme index."
        (assertEqual "makeDict['\\255'] should be 1." (makeDict ! '\255') 1)

    , testCase "Testing memoize, given value."
        (assertEqual "memoizeDict['A'] should be 5." (memoizeDict ! 'A') 5)
    , testCase "Testing memoize, given value."
        (assertEqual "memoizeDict['b'] should be 6." (memoizeDict ! 'b') 6)
    , testCase "Testing memoize, default value."
        (assertEqual "memoizeDict['a'] should be 7." (memoizeDict ! 'a') 7)
    , testCase "Testing memoize, default value."
        (assertEqual "memoizeDict['z'] should be 7." (memoizeDict ! 'z') 7)
    , testCase "Testing memoize, extreme index."
        (assertEqual "memoizeDict['\\0'] should be 7."
            (memoizeDict ! '\0')
            7)
    , testCase "Testing memoize, extreme index."
        (assertEqual "memoizeDict['\\255'] should be 7."
            (memoizeDict ! '\255')
            7)
    ]
  where
    makeDict :: CharDict Int
    makeDict = makeCharDict [('a', 2), ('B', 3)] 1
    memoizeDict = memoize f
    f :: Char -> Int
    f 'A' = 5
    f 'b' = 6
    f _   = 7
