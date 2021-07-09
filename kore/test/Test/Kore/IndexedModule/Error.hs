{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Test.Kore.IndexedModule.Error (
    test_undefineds,
) where

import Kore.IndexedModule.Error
import Prelude.Kore ()
import Test.Kore (
    testId,
 )
import Test.Tasty
import Test.Terse

test_undefineds :: TestTree
test_undefineds =
    testGroup
        "error strings for undefined objects"
        [ noAlias (testId "#a") `equals_` "Alias '#a' not defined."
        , noSymbol (testId "#b") `equals_` "Symbol '#b' not defined."
        -- The following two lines print full structure dumps.
        -- They should perhaps print something better?
        -- , noHead (builtinSymbol "#c") `equals_` "Head '#c' not defined."
        -- s, noSort (testId "#d") `equals_` "Sort '#d' not defined."
        ]
