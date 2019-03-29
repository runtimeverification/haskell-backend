{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Test.Kore.Error where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Test.Terse

import Control.Exception
import Data.Void
import Kore.Error

type DontCare = Void
type Wrapper = Either (Error DontCare) String

test_assertRight :: TestTree
test_assertRight =
    testGroup "assertRight"
        [ assertRight (mkRight "expected") `equals_` "expected"
    --    , assertRight (mkLeft someError) `throws_` (printerr someError)
        , testCase "case" $ handler (assertRight (mkLeft $ koreError "foo"))
        ]
    where
        someError = koreError "the error message"
        mkRight x = Right x :: Wrapper
        mkLeft x = Left x :: Wrapper
        mkError msg =
            Error { errorContext = ["test context"], errorError = msg }

        handler :: a -> Assertion
        handler x =
            do
              catch (evaluate x >> assertFailure "didn't throw") $ \ (ErrorCall msg) ->
                assertEqualWithExplanation "ksdj" msg (printError (mkError "foo"))
              return ()
