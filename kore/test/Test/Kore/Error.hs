{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Test.Kore.Error where

import Test.Tasty
-- import Test.Tasty.HUnit
-- import Test.Terse

import Data.Void
       ( Void )
import Kore.Error

type DontCare = Void
type Wrapper = Either (Error DontCare) String

test_assertRight :: TestTree
test_assertRight =
    testGroup "assertRight"
        [ -- assertRight (Right "wrapped" :: Wrapper) `equals_` "wrapped"
        ]

-- The above test depends on Tom's PR test for tomorrow.
