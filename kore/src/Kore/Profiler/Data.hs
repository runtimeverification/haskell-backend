{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Profiler.Data
    ( MonadProfiler (..)
    , nullProfileDuration
    , profileDurationEvent
    , profileDurationStartEnd
    , ProfileEvent (..)
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
import           Debug.Trace
                 ( traceEventIO )
import           ListT
                 ( ListT (..) )
import qualified ListT
                 ( mapListT )
import           System.CPUTime
                 ( getCPUTime )

{- Monad that can also handle profiling events.
-}
class Monad profiler => MonadProfiler profiler where
    --
    profileDuration :: [String] -> profiler a -> profiler a
    default profileDuration
        :: (MonadProfiler m, MFunctor t, profiler ~ t m)
        => [String] -> profiler a -> profiler a
    profileDuration a = hoist (profileDuration a)
    {-# INLINE profileDuration #-}

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

{- Times an action.
-}
profileDurationEvent :: MonadIO profiler => [String] -> profiler a -> profiler a
profileDurationEvent tags action = do
    startTime <- liftIO getCPUTime
    let event = ProfileEvent
            { startPico = startTime
            , endPico = Nothing
            , tags
            }
    liftIO $ traceEventIO (show event)
    a <- action
    endTime <- liftIO getCPUTime
    liftIO $ traceEventIO (show event {endPico = Just endTime})
    return a

{- Times an action in the format required by @ghc-events-analyze@.
-}
profileDurationStartEnd
    :: MonadIO profiler => [String] -> profiler a -> profiler a
profileDurationStartEnd event action = do
    liftIO $ traceEventIO ("START " ++ show event)
    a <- action
    liftIO $ traceEventIO ("END " ++ show event)
    return a

{- Null timing function, to be used when not interested in profiling.
-}
nullProfileDuration :: Monad profiler => [String] -> profiler a -> profiler a
nullProfileDuration _ = id

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
