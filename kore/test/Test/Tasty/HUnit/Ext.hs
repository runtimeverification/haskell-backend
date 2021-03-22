module Test.Tasty.HUnit.Ext (
    assertEqual,
    (@=?),
    (@?=),
    assertSubstring,
    assertErrorIO,
    module Test.Tasty.HUnit,
    module Kore.Debug,
) where

import Control.Exception (
    SomeException,
 )
import qualified Control.Exception as Exception
import Data.List (
    isInfixOf,
 )
import Kore.Debug
import Prelude.Kore
import qualified Pretty
import Test.Tasty.HUnit hiding (
    assertEqual,
    (@=?),
    (@?=),
 )

assertEqual ::
    (Diff a, MonadIO io, HasCallStack) =>
    -- | The message prefix
    String ->
    -- | The expected value
    a ->
    -- | The actual value
    a ->
    io ()
assertEqual preface expected actual =
    case diff expected actual of
        Nothing -> return ()
        Just ab -> liftIO $ assertFailure message
          where
            message
                | null preface = show ab
                | otherwise = (show . Pretty.vsep) [Pretty.pretty preface, ab]

(@=?) ::
    (Diff a, HasCallStack) =>
    -- | The expected value
    a ->
    -- | The actual value
    a ->
    Assertion
(@=?) expected actual = assertEqual "" expected actual

(@?=) ::
    (Diff a, HasCallStack) =>
    -- | The actual value
    a ->
    -- | The expected value
    a ->
    Assertion
(@?=) actual expected = assertEqual "" expected actual

assertSubstring :: HasCallStack => String -> String -> String -> IO ()
assertSubstring preface a b =
    assertBool message (a `isInfixOf` b)
  where
    message =
        (show . Pretty.vsep)
            [ Pretty.pretty preface
            , debug a
            , "is not a substring of"
            , debug b
            ]

assertErrorIO :: HasCallStack => (String -> IO ()) -> IO a -> IO ()
assertErrorIO errorTest action = do
    maybeErr <-
        Exception.catch
            ( do
                value <- action
                _ <- Exception.evaluate value
                return Nothing
            )
            (\err -> return (Just (show (err :: SomeException))))
    case maybeErr of
        Nothing -> assertFailure "No error during action."
        Just err -> errorTest err
