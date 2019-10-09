module Test.Tasty.HUnit.Ext
    ( assertEqual , (@=?), (@?=)
    , assertSubstring
    , assertErrorIO
    , module Test.Tasty.HUnit
    , module Kore.Debug
    ) where

import Test.Tasty.HUnit hiding
    ( assertEqual
    , (@=?)
    , (@?=)
    )

import Control.Exception
    ( SomeException
    )
import qualified Control.Exception as Exception
import Control.Monad.IO.Class
import Data.List
    ( isInfixOf
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import Kore.Debug

assertEqual
    :: (Diff a, MonadIO io, GHC.HasCallStack)
    => String  -- ^ The message prefix
    -> a  -- ^ The expected value
    -> a  -- ^ The actual value
    -> io ()
assertEqual preface expected actual =
    case diff expected actual of
        Nothing -> return ()
        Just ab -> liftIO $ assertFailure message
          where
            message
              | null preface = show ab
              | otherwise    = (show . Pretty.vsep) [Pretty.pretty preface, ab]

(@=?)
    :: (Diff a, GHC.HasCallStack)
    => a  -- ^ The expected value
    -> a  -- ^ The actual value
    -> Assertion
(@=?) expected actual = assertEqual "" expected actual

(@?=)
    :: (Diff a, GHC.HasCallStack)
    => a  -- ^ The actual value
    -> a  -- ^ The expected value
    -> Assertion
(@?=) actual expected = assertEqual "" expected actual

assertSubstring :: GHC.HasCallStack => String -> String -> String -> IO()
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

assertErrorIO :: HasCallStack => (String -> IO()) -> IO a -> IO()
assertErrorIO errorTest action = do
    maybeErr <-
        Exception.catch
            (do
                value <- action
                _ <- Exception.evaluate value
                return Nothing
            )
            (\err -> return (Just (show (err :: SomeException))))
    case maybeErr of
        Nothing  -> assertFailure "No error during action."
        Just err -> errorTest err
