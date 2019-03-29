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

test_assertRight :: TestTree
test_assertRight =
    testGroup "assertRight"
        [ assertRight (mkRight "expected") `equals_` "expected"
    --    , assertRight (mkLeft someError) `throws_` (printerr someError)
        , testCase "case" $ handler (assertRight (mkLeft someError))
        ]
    where
        someError = koreError "the error message"

        handler :: a -> Assertion
        handler x =
            do
              catch (evaluate x >> assertFailure "didn't throw") $ \ (ErrorCall msg) ->
                assertEqualWithExplanation "ksdj" msg (printError someError)
              return ()


type DontCare = Void
type Wrapper = Either (Error DontCare) String

mkRight :: String -> Wrapper
mkRight r = Right r :: Wrapper

mkLeft :: Error DontCare -> Wrapper
mkLeft l = Left l :: Wrapper
