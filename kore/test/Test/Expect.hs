module Test.Expect
    ( expectRight
    , expectLeft
    , expectJust
    , expectOne
    , assertNull
    , assertTop
    , expectBool
    , expectJustT
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    , maybeT
    )

import Debug
import Kore.Internal.InternalBool
import Kore.Internal.TermLike
import Kore.TopBottom

import Test.Tasty.HUnit.Ext

expectRight :: HasCallStack => Debug left => Either left right -> IO right
expectRight = either (assertFailure . show . debug) return

expectLeft :: HasCallStack => Debug right => Either left right -> IO left
expectLeft = either return (assertFailure . show . debug)

expectJust :: HasCallStack => Maybe a -> IO a
expectJust = maybe (assertFailure "expected Just _, found Nothing") return

expectOne :: Foldable fold => HasCallStack => Debug [a] => fold a -> IO a
expectOne as =
    case toList as of
        [a] -> return a
        as' -> (assertFailure . show) (debug as')

assertNull :: Foldable fold => HasCallStack => Debug [a] => fold a -> IO ()
assertNull as =
    case toList as of
        [] -> return ()
        as' -> (assertFailure . show) (debug as')

assertTop :: HasCallStack => TopBottom a => Debug a => a -> IO ()
assertTop a
  | isTop a = return ()
  | otherwise = (assertFailure . show) (debug a)

expectBool :: HasCallStack => TermLike VariableName -> IO Bool
expectBool (BuiltinBool_ internalBool) = return (internalBoolValue internalBool)
expectBool term = (assertFailure . show) (debug term)

expectJustT :: MonadIO io => HasCallStack => MaybeT io a -> io a
expectJustT =
    maybeT
        (liftIO $ assertFailure "expected Just")
        return
