{-# LANGUAGE FlexibleContexts #-}
module Test.Tasty.HUnit.Extensions where
import           Control.Exception (SomeException, catch, evaluate)
import           Control.Monad
import           Data.CallStack
import           Data.List         (isInfixOf)
import           Test.Tasty.HUnit  (assertBool, assertFailure)

assertEqualWithPrinter
    :: (Eq a, HasCallStack)
    => (a -> String)
    -> String -- ^ The message prefix
    -> a      -- ^ The expected value
    -> a      -- ^ The actual value
    -> IO ()
assertEqualWithPrinter printer preface expected actual =
    unless (actual == expected) (assertFailure msg)
  where
    msg =
        (if null preface then "" else preface ++ "\n")
        ++ "expected: " ++ printer expected ++ "\n but got: " ++ printer actual

assertError :: (String -> IO()) -> a -> IO()
assertError errorTest action = do
    maybeErr <-
        catch
            (do
                evaluate action
                return Nothing
            )
            (\err -> return (Just (show (err :: SomeException))))
    case maybeErr of
        Nothing  -> assertFailure "No error during action."
        Just err -> errorTest err

assertSubstring :: String -> String -> String -> IO()
assertSubstring message first second =
    assertBool
        (  message
        ++ ": '"
        ++ first
        ++ "' is not a substring of '"
        ++ second
        ++ "'"
        )
        (first `isInfixOf` second)
