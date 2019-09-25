{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Profiler.Data
    ( MonadProfiler (..)
    , profileEvent
    , profileValue
    , ProfileEvent (..)
    , Configuration (..)
    , Destination (..)
    ) where

import Control.Monad
    ( when
    )
import Control.Monad.IO.Class
    ( MonadIO (liftIO)
    )
import Control.Monad.Morph
    ( MFunctor (..)
    )
import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Monad.State.Strict as Strict
import Control.Monad.Trans.Accum
    ( AccumT (AccumT)
    , runAccumT
    )
import Control.Monad.Trans.Except
    ( ExceptT
    )
import Control.Monad.Trans.Identity
    ( IdentityT
    )
import Control.Monad.Trans.Maybe
    ( MaybeT
    )
import Data.Functor.Identity
    ( Identity
    )
import Data.List
    ( intercalate
    )
import qualified Data.List as List
import Debug.Trace
    ( traceIO
    , traceM
    )
import Debug.Trace.String
    ( traceEventIO
    )
import System.Clock
    ( Clock (Monotonic)
    , TimeSpec
    , diffTimeSpec
    , getTime
    , toNanoSecs
    )

import ListT
    ( ListT (..)
    )
import qualified ListT
    ( mapListT
    )

{- Monad that can also handle profiling events.
-}
class Monad profiler => MonadProfiler profiler where
    profile
        :: [String]
        -> profiler a
        -> profiler a
    default profile
        :: (MonadProfiler m, MFunctor t, profiler ~ t m)
        => [String]
        -> profiler a
        -> profiler a
    profile a = hoist (profile a)
    {-# INLINE profile #-}

    -- TODO(virgil): Add a command line flag for this.
    profileConfiguration :: profiler Configuration
    profileConfiguration =
        return Configuration
            { identifierFilter = Nothing
            , dumpIdentifier = Nothing
            , destination = KoreProfiler
            , logBranching = False
            , logStrategy = True
            , logSimplification = False
            , logInitialization = False
            , logEvaluation = True
            , logSmt = True
            }
    {-# INLINE profileConfiguration #-}

profileValue :: MonadProfiler profiler => [String] -> Int -> profiler ()
profileValue tags value = do
    Configuration {destination} <- profileConfiguration
    when (isHumanReadable destination)
        (traceM (intercalate "-" tags ++ " --> " ++ show value))

-- Instance for tests.
instance MonadProfiler Identity where
    profile = \_ x -> x
    {-# INLINE profile #-}

    profileConfiguration =
        return Configuration
            { identifierFilter = Nothing
            , dumpIdentifier = Nothing
            , destination = HumanReadable
            , logBranching = False
            , logStrategy = False
            , logSimplification = False
            , logInitialization = False
            , logEvaluation = False
            , logSmt = False
            }
    {-# INLINE profileConfiguration #-}

data Destination =
    GhcEventsAnalyze
  | KoreProfiler
  | HumanReadable
    -- ^ Suggestions for the human readable output:
    --
    -- * Pipe through @sed 's/-/ /g' | sed "s/'//g"@ to remove characters
    --   that will confuse the next steps.
    -- * Pipe through @tr '\n' '~'@ to remove newlines.
    -- * Pipe through something like
    --   @sed '^\s*timing.*{~\s*} timing.*e [2-9]s~'@
    --   to remove timings that are too low (i.e. with negative exponents)
    --   and which do not contain other timings inside (sed command not
    --   copy-pasted from actual command-line)
    -- * Pipe repeatedly through the sed command above to remove all low timings
    -- * Put newlines back with @tr '~' '\n'@
    -- * Pipe through astyle to indent
    -- * Use an editor which collapses sections to explore (Visual Studio Code
    --   defines sections based on indentation levels by default and seems
    --   to be fast enough for exploring profiling output files).

data Configuration =
    Configuration
        { identifierFilter :: !(Maybe String)
        -- ^ If present, only emits events for this identifier.
        , dumpIdentifier :: !(Maybe String)
        -- ^ If present, dump extra information for this identifier.
        , destination :: Destination
        , logBranching :: !Bool
        , logStrategy :: !Bool
        , logSimplification :: !Bool
        , logInitialization :: !Bool
        , logEvaluation :: !Bool
        , logSmt :: !Bool
        }

{- A profiler event.

The profiler generates two @ProfileEvent@s for each actual event:
one at the start, with @duration=Nothing@, and one at the end with an @Just@
value for @end@
-}
data ProfileEvent
    = ProfileEvent
        { start :: !TimeSpec
        -- ^ The start CPU time.
        , end :: !(Maybe TimeSpec)
        -- ^ The cpu time at the end of the event.
        -- Nothing if this is a start event.
        , tags :: ![String]
        -- ^ Tags for the event. If @tags=[t1, t2, t3]@ then this event will be
        -- counted as part of @t1@, @t1-t2@ and @t1-t2-t3@.
        }
    deriving (Show, Read)

isHumanReadable :: Destination -> Bool
isHumanReadable HumanReadable = True
isHumanReadable _ = False

nanosToSeconds :: Integer -> Double
nanosToSeconds nanos =
    fromInteger nanos / (1000 * 1000 * 1000)

traceStderr
    :: ProfileEvent -> IO ()
traceStderr
    ProfileEvent { end = Nothing, tags }
  =
    traceIO (intercalate "-" tags ++ " {")
traceStderr
    ProfileEvent { start, end = Just endTime, tags }
  =
    traceIO
        (  "} "
        ++ intercalate "-" tags
        ++ " "
        ++ show (nanosToSeconds (toNanoSecs (diffTimeSpec endTime start)))
        ++ "s"
        )

profileEvent
    :: (MonadIO profiler)
    => Configuration -> [String] -> profiler a -> profiler a
profileEvent
    Configuration {destination}
    event
    action
  = case destination of
        GhcEventsAnalyze -> profileGhcEventsAnalyze event action
        KoreProfiler -> profileKoreProfiler event action
        HumanReadable -> profileHumanReadable event action

{- Times an action in a human readable way.
-}
profileHumanReadable
    :: MonadIO profiler
    => [String] -> profiler a -> profiler a
profileHumanReadable tags action = do
    startTime <- liftIO (getTime Monotonic)
    let event = ProfileEvent
            { start = startTime
            , end = Nothing
            , tags
            }
    liftIO $ traceStderr event
    a <- action
    endTime <- liftIO (getTime Monotonic)
    liftIO $ traceStderr
        event {end = Just endTime}
    return a

{- Times an action for the kore-profiler tool.
-}
profileKoreProfiler
    :: MonadIO profiler
    => [String] -> profiler a -> profiler a
profileKoreProfiler tags action = do
    startTime <- liftIO (getTime Monotonic)
    let event = ProfileEvent
            { start = startTime
            , end = Nothing
            , tags
            }
    liftIO $ traceEventIO (show event)
    a <- action
    endTime <- liftIO (getTime Monotonic)
    liftIO $ traceEventIO $ show
        event {end = Just endTime}
    return a

{- Times an action in the format required by @ghc-events-analyze@.
-}
profileGhcEventsAnalyze
    :: MonadIO profiler
    => [String] -> profiler a -> profiler a
profileGhcEventsAnalyze event action = do
    liftIO $ traceEventIO ("START " ++ List.intercalate "/" event)
    a <- action
    liftIO $ traceEventIO ("STOP " ++ List.intercalate "/" event)
    return a

instance (MonadProfiler m) => MonadProfiler (ReaderT thing m )

instance MonadProfiler m => MonadProfiler (Strict.StateT s m)

instance MonadProfiler m => MonadProfiler (MaybeT m)

instance MonadProfiler m => MonadProfiler (IdentityT m)

instance MonadProfiler m => MonadProfiler (ExceptT e m)

instance MonadProfiler m => MonadProfiler (ListT m) where
    profile a action =
        ListT.mapListT (profile a) action
    {-# INLINE profile #-}

instance (MonadProfiler m, Monoid w) => MonadProfiler (AccumT w m)
  where
    profile a action = AccumT (profile a . runAccumT action)
    {-# INLINE profile #-}
