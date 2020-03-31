module Test.Expect
    ( expectRight
    , expectLeft
    ) where

import Prelude.Kore

import Debug

import Test.Tasty.HUnit.Ext

expectRight :: HasCallStack => Debug left => Either left right -> IO right
expectRight = either (assertFailure . show . debug) return

expectLeft :: HasCallStack => Debug right => Either left right -> IO left
expectLeft = either return (assertFailure . show . debug)
