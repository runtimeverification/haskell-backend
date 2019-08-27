{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Profiler.Data
    ( MonadProfiler (..)
    , profileDurationEvent
    , profileDurationStartEnd
    , ProfileEvent (..)
    , Configuration (..)
    ) where

import           Control.Monad.IO.Class
                 ( MonadIO (liftIO) )
import           Control.Monad.Morph
                 ( MFunctor (..) )
import           Control.Monad.Reader
                 ( ReaderT )
import qualified Control.Monad.State.Strict as Strict
import           Control.Monad.Trans.Accum
                 ( AccumT (AccumT), runAccumT )
import           Control.Monad.Trans.Except
                 ( ExceptT )
import           Control.Monad.Trans.Identity
                 ( IdentityT )
import           Control.Monad.Trans.Maybe
                 ( MaybeT )
import           Data.Functor.Identity
                 ( Identity )
import           Debug.Trace.String
                 ( traceEventIO )
import           System.Clock
                 ( Clock (Monotonic), TimeSpec (TimeSpec), getTime )
import qualified System.Clock as Clock.DoNotUse

import           ListT
                 ( ListT (..) )
import qualified ListT
                 ( mapListT )

{- Monad that can also handle profiling events.
-}
class Monad profiler => MonadProfiler profiler where
    profileDuration :: [String] -> profiler a -> profiler a
    default profileDuration
        :: (MonadProfiler m, MFunctor t, profiler ~ t m)
        => [String] -> profiler a -> profiler a
    profileDuration a = hoist (profileDuration a)
    {-# INLINE profileDuration #-}

    -- TODO(virgil): Add a command line flag for this.
    profileConfiguration :: profiler Configuration
    profileConfiguration =
        return Configuration
            {identifierFilter = Nothing, dumpIdentifier = Nothing}
    {-# INLINE profileConfiguration #-}

-- Instance for tests.
instance MonadProfiler Identity where
    profileDuration _ = id
    profileConfiguration =
        return Configuration
            { identifierFilter = Nothing
            , dumpIdentifier = Nothing
            }

data Configuration =
    Configuration
        { identifierFilter :: !(Maybe String)
        -- ^ If present, only emits events for this identifier.
        , dumpIdentifier :: !(Maybe String)
        -- ^ If present, dump extra information for this identifier.
        }

{- A profiler event.

The profiler generates two @ProfileEvent@s for each actual event:
one at the start, with @endPico=Nothing@, and one at the end with an @Just@
value for @endPico@
-}
data ProfileEvent
    = ProfileEvent
        { startPico :: !Integer
        -- The start CPU time, in picoseconds.
        , endPico :: !(Maybe Integer)
        -- The end CPU time, in picoseconds. Nothing if this is a start event.
        , tags :: ![String]
        -- Tags for the event. If @tags=[t1, t2, t3]@ then this event will be
        -- counted as part of @t1@, @t1-t2@ and @t1-t2-t3@.
        }
    deriving (Show, Read)

getTimePicos :: IO Integer
getTimePicos = timeSpecToPicos <$> getTime Monotonic
  where
    timeSpecToPicos TimeSpec {sec, nsec} =
         ((toInteger sec * 1000 * 1000 * 1000) + toInteger nsec) * 1000

{- Times an action.
-}
profileDurationEvent :: MonadIO profiler => [String] -> profiler a -> profiler a
profileDurationEvent tags action = do
    startTime <- liftIO getTimePicos
    let event = ProfileEvent
            { startPico = startTime
            , endPico = Nothing
            , tags
            }
    liftIO $ traceEventIO (show event)
    a <- action
    endTime <- liftIO (getTime Monotonic)
    liftIO $ traceEventIO
        (show event {endPico = Just (timeSpecToPicos endTime)})
    return a
  where
    timeSpecToPicos TimeSpec {sec, nsec} =
         ((toInteger sec * 1000 * 1000 * 1000) + toInteger nsec) * 1000

{- Times an action in the format required by @ghc-events-analyze@.
-}
profileDurationStartEnd
    :: MonadIO profiler => [String] -> profiler a -> profiler a
profileDurationStartEnd event action = do
    liftIO $ traceEventIO ("START " ++ show event)
    a <- action
    liftIO $ traceEventIO ("END " ++ show event)
    return a

instance (MonadProfiler m) => MonadProfiler (ReaderT thing m )

instance MonadProfiler m => MonadProfiler (Strict.StateT s m)

instance MonadProfiler m => MonadProfiler (MaybeT m)

instance MonadProfiler m => MonadProfiler (IdentityT m)

instance MonadProfiler m => MonadProfiler (ExceptT e m)

instance MonadProfiler m => MonadProfiler (ListT m) where
    profileDuration a action =
        ListT.mapListT (profileDuration a) action
    {-# INLINE profileDuration #-}

instance (MonadProfiler m, Monoid w) => MonadProfiler (AccumT w m)
  where
    profileDuration a action = AccumT (profileDuration a . runAccumT action)
    {-# INLINE profileDuration #-}
