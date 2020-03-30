module Test.Expect
    ( expectRight
    ) where

import Prelude.Kore

import Debug

import Test.Tasty.HUnit.Ext

expectRight :: Debug left => Either left right -> IO right
expectRight = either (assertFailure . show . debug) return
