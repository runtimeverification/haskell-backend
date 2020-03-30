module Test.Expect
    ( expectRight
    , expectLeft
    ) where

import Prelude.Kore

import Debug

import Test.Tasty.HUnit.Ext

expectRight :: Debug left => Either left right -> IO right
expectRight = either (assertFailure . show . debug) return

expectLeft :: Debug right => Either left right -> IO left
expectLeft = either return (assertFailure . show . debug)
