{-# LANGUAGE FlexibleContexts #-}

module Test.Tasty.HUnit.Extensions where

import           Control.Monad
import           Data.CallStack
import           Test.Tasty.HUnit (assertFailure)

assertEqualWithPrinter
    :: (Eq a, HasCallStack)
    => (a -> String)
    -> String -- ^ The message prefix
    -> a -- ^ The expected value
    -> a -- ^ The actual value
    -> IO ()
assertEqualWithPrinter printer preface expected actual =
    unless (actual == expected) (assertFailure msg)
  where
    msg =
        (if null preface
             then ""
             else preface ++ "\n")
        ++ "expected: " ++ printer expected ++ "\n but got: " ++ printer actual
