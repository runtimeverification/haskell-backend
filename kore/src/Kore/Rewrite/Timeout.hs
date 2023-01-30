{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Timeouts for rewrite steps
-}
module Kore.Rewrite.Timeout (
  StepMovingAverage (..),
  StepTimeout (..),
  TimeoutMode (..),
  EnableMovingAverage (..),
  updateStepMovingAverage,
  getStepMovingAverage,
  getTimeout,
  getTimeoutMode,
  timeAction
  ) where

import Control.Concurrent (
  MVar,
  tryTakeMVar,
  putMVar,
  tryReadMVar
  )
import Data.Aeson (
  FromJSON,
  )
import System.Clock (
  getTime,
  Clock (..),
  diffTimeSpec,
  toNanoSecs
  )
import Prelude.Kore

-- | Moving average of steps in microseconds.
newtype StepMovingAverage = StepMovingAverage
    { movingAverage :: Int
    }
    deriving stock (Eq, Show)

-- | Step timeout in milliseconds.
newtype StepTimeout = StepTimeout
    { unStepTimeout :: Int
    }
    deriving stock (Eq, Ord, Show)
    deriving newtype (FromJSON)

data EnableMovingAverage
  = DisableMovingAverage
  | EnableMovingAverage

data TimeoutMode
  = MovingAverage Int
  | ManualTimeout Int

updateStepMovingAverage :: MonadIO m => MVar StepMovingAverage -> Int -> m ()
updateStepMovingAverage ma stepTime =
  liftIO (tryTakeMVar ma) >>= \case
     Nothing -> liftIO . putMVar ma $ StepMovingAverage stepTime
     Just (StepMovingAverage movingAverage) -> do
          let w = 0.95
              newMA = floor @Double
                $ w * fromIntegral movingAverage + (1 - w) * fromIntegral stepTime
          liftIO . putMVar ma $ StepMovingAverage newMA

getStepMovingAverage :: MonadIO m => MVar StepMovingAverage -> m Int
getStepMovingAverage sma =
    liftIO (tryReadMVar sma) >>= \case
       Nothing -> pure defaultDelay
       Just (StepMovingAverage ma) -> pure ma
    where
      defaultDelay = 3000000

getTimeout :: TimeoutMode -> Int
getTimeout (ManualTimeout t) = t
getTimeout (MovingAverage t) =
  -- two times slower than moving average
  let threshold = 2
  in t * threshold

-- | Decide what timeout to use for the next step
getTimeoutMode ::
  MonadIO m =>
  Maybe StepTimeout ->
  EnableMovingAverage ->
  MVar StepMovingAverage ->
  m (Maybe TimeoutMode)
getTimeoutMode stepTimeout enableMA sma =
  case (stepTimeout, enableMA) of
      (Nothing, DisableMovingAverage) -> pure Nothing
      (Just (StepTimeout st), DisableMovingAverage) ->
          pure . Just $ ManualTimeout $ st * 1000
      (Nothing, EnableMovingAverage) -> do
          ma <- getStepMovingAverage sma
          pure . Just $ MovingAverage ma
      (Just (StepTimeout st), EnableMovingAverage) -> do
          ma <- getStepMovingAverage sma
          let manualST = st * 1000
          pure . Just $ if ma < manualST
                        then MovingAverage ma
                        else ManualTimeout manualST

-- | Get time spent on action in microseconds.
timeAction :: MonadIO m => m t -> m (Int, t)
timeAction act = do
    start <- liftIO $ getTime Realtime
    result <- act
    end   <- liftIO $ getTime Realtime
    let diff = fromInteger $ toNanoSecs (diffTimeSpec end start) `div` 1000
    return (diff, result)
