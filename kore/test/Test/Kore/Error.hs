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
        [ try (mkRight "expected") `equals_` "expected"
        , try (mkLeft   someError) `throws_` (printError someError)
        ]
    where
        try = assertRight
        someError = koreError "the error message"



throws_ :: a -> String -> TestTree
throws_ lazyValue expected =
    testCase "throws" $ do
        catch (evaluate lazyValue >> missingThrow) messageChecker
        return ()
  where
    missingThrow =
        assertFailure "No `error` was raised."

    messageChecker (ErrorCall msg) =
        assertEqualWithExplanation "assertion" msg expected




type DontCare = Void
type Wrapper = Either (Error DontCare) String

mkRight :: String -> Wrapper
mkRight = Right

mkLeft :: Error DontCare -> Wrapper
mkLeft = Left
