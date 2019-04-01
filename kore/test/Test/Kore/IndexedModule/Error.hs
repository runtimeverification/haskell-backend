{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Test.Kore.IndexedModule.Error where

-- import Test.Kore
--        ( testId )
import Test.Tasty
-- import Test.Tasty.HUnit
-- import Test.Terse

-- import Kore.IndexedModule.Error

test_undefineds :: TestTree
test_undefineds =
    testGroup "error strings for undefined objects"
        [ -- noSort (testId "a") `equals_` "Sort '#a' not defined"
        ]

-- Awaiting Tom's fix to string explanations
