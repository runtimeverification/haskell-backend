{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

{-# OPTIONS_GHC -fno-prof-auto #-}

module Prof
    ( MonadProf (..)
    , defaultTraceProf
    ) where

import Prelude.Kore hiding
    ( traceEventIO
    )

import Control.Monad.Catch
    ( MonadMask
    , bracket_
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Debug.Trace.Text
    ( traceEventIO
    )

class Monad prof => MonadProf prof where
    {- | Attribute an action to a particular name for profiling.
     -}
    traceProf
        :: Text  -- ^ name for profiling
        -> prof a  -- ^ action
        -> prof a

instance MonadProf IO where
    traceProf = defaultTraceProf
    {-# INLINE traceProf #-}

defaultTraceProf
    :: (MonadIO mask, MonadMask mask)
    => Text
    -> mask a
    -> mask a
defaultTraceProf name =
    bracket_ open close
  where
    open = liftIO $ traceEventIO (Text.cons 'O' name)
    close = liftIO $ traceEventIO (Text.cons 'C' name)
{-# INLINE defaultTraceProf #-}
