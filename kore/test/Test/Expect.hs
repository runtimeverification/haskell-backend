module Test.Expect
    ( expectRight
    , expectLeft
    , expectOne
    , assertNull
    , assertTop
    , expectBool
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable

import Debug
import Kore.Domain.Builtin
import Kore.Internal.TermLike
import Kore.TopBottom

import Test.Tasty.HUnit.Ext

expectRight :: HasCallStack => Debug left => Either left right -> IO right
expectRight = either (assertFailure . show . debug) return

expectLeft :: HasCallStack => Debug right => Either left right -> IO left
expectLeft = either return (assertFailure . show . debug)

expectOne :: Foldable fold => HasCallStack => Debug [a] => fold a -> IO a
expectOne as =
    case Foldable.toList as of
        [a] -> return a
        as' -> (assertFailure . show) (debug as')

assertNull :: Foldable fold => HasCallStack => Debug [a] => fold a -> IO ()
assertNull as =
    case Foldable.toList as of
        [] -> return ()
        as' -> (assertFailure . show) (debug as')

assertTop :: HasCallStack => TopBottom a => Debug a => a -> IO ()
assertTop a
  | isTop a = return ()
  | otherwise = (assertFailure . show) (debug a)

expectBool :: HasCallStack => TermLike VariableName -> IO Bool
expectBool (BuiltinBool_ internalBool) = return (builtinBoolValue internalBool)
expectBool term = (assertFailure . show) (debug term)
