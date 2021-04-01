{-# LANGUAGE Strict #-}
module Test.Kore.Syntax.Id (
    test_Id,

    -- * Re-exports
    testId,
    module Kore.Syntax.Id,
) where

import Kore.Syntax.Id
import Prelude.Kore
import Test.Kore (
    testId,
 )
import Test.Tasty
import Test.Terse

test_Id :: [TestTree]
test_Id =
    [ equals (testId "x") (noLocationId "x") "Eq"
    , on equals hash (testId "x") (noLocationId "x") "Hashable"
    , equals
        (idLocation $ generatedId "generated")
        AstLocationGeneratedVariable
        "generatedId"
    ]
