{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

This module provides infrastructure for "Timing State Machines" (TSM),
which analyse an eventlog file for specific _marker events_ that
instrument a component.

The markers indicate transitions between states of a state machine
defined as an instance of @'TimingStateMachine'@, and the tool
produces a graph of these transitions with timing information on each
edge.

All sequences of visited states (i.e., marker events) are extracted
from the event log, collecting timing information about the time
spent inside each state before transitioning into the subsequent state
(plus the total).

The state machine is specified by a `transitionLabels` table
containing all allowed transitions. Transitions with empty labels are
allowed but will be omitted from the output graph. On unexpected
transitions (i.e., marker event sequences that are unexpected), the
tool currently throws an error.
-}
module Kore.Util.TSM (
    module Kore.Util.TSM, --temporary
) where

import Control.Monad.Extra (fold1M)
import Control.Monad.State
import Data.Bifunctor (first)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Float (log)
import GHC.RTS.Events
import Prelude.Kore
import Text.Printf

graphOf ::
    forall tag.
    TimingStateMachine tag =>
    Proxy tag ->
    FilePath ->
    IO String
graphOf proxy file =
    logStats_ proxy file
        >>= pure . printf "digraph \"%s\" {\n%s\n}\n" file . unlines

logStats ::
    forall tag.
    TimingStateMachine tag =>
    Proxy tag ->
    FilePath ->
    IO [String]
logStats _ file = do
    timingMap <- collectTimings @tag . getMarkers <$> readLog file
    let statMap = mapStatistics timingMap
    pure $ map (uncurry printForDot) $ Map.assocs statMap

logStats_ ::
    forall tag. TimingStateMachine tag => Proxy tag -> FilePath -> IO [String]
logStats_ _ file = do
    statMap <- collectStats @tag . getMarkers <$> readLog file
    pure $ map (uncurry printForDot) $ Map.assocs statMap

readLog :: FilePath -> IO [Event]
readLog file =
    readEventLogFromFile file
        >>= either error (pure . sortOn evTime . events . dat)

getMarkers ::
    forall tag. TimingStateMachine tag => [Event] -> [(Timestamp, tag)]
getMarkers = mapMaybe getMarker
  where
    getMarker Event{..}
        | UserMarker{markername} <- evSpec =
            fmap (evTime,) $ readTag markername
        | otherwise =
            Nothing

label :: TimingStateMachine tag => tag -> tag -> Maybe Text
label prior next = Map.lookup (prior, next) transitionLabels

------------------------------------------------------------

{- | Type class for a timing state machine based on GHC marker events.
  Minimal definition: @'transitionLabels'@
-}
class (Show tag, Ord tag) => TimingStateMachine tag where
    -- | Specifies the allowed transitions. Transitions with empty
    -- label will be omitted from the output.
    transitionLabels :: Map (tag, tag) Text

    -- | Tag decoder for reading from the event log. The signature is
    -- simple to keep it flexible and not impose format constraints.
    -- By default, it will look up text in the @'tagMap'@ provided.
    readTag :: Text -> Maybe tag
    readTag = flip Map.lookup tagMap

    -- | Helper for decoding tags. Defaults to all tags used in the
    -- transition label map.
    tagMap :: Map Text tag
    tagMap =
        Map.fromList
            [ (Text.pack $ show tag, tag)
            | let keys = Map.keys transitionLabels
            , tag <- uncurry (<>) $ unzip keys
            ]

-- | Helper for the transitionLabels
(-->) :: tag -> tag -> Text -> ((tag, tag), Text)
t1 --> t2 = ((t1, t2),)

-----------------------------------------------------------

{- Collect timings for all state transitions in the machine above from
 the trace event sequence. 'UnifyTag's are trace markers indicating
 transition into the next state. Timings are stored in a 'Map
 (tag,tag) [Int]'.  Time unit is _microseconds_ (GHC events use
 nanoseconds).
-}
collectTimings ::
    forall tag.
    TimingStateMachine tag =>
    [(Timestamp, tag)] ->
    Map (tag, tag) [Double]
collectTimings =
    snd
        . flip runState Map.empty
        . fold1M collect
        . map (first ((/ 1000) . fromIntegral)) -- microsecond timestamps
  where
    collect ::
        (Double, tag) ->
        (Double, tag) ->
        State (Map (tag, tag) [Double]) (Double, tag)
    collect (t1, prior) (t2, next) = do
        case label prior next of
            Nothing -> do
                traceM $
                    "WARNING: Undefined transition " <> show prior <> " --> " <> show next
                modify $ Map.insertWith (++) (prior, next) [t2 - t1]
            Just l
                | Text.null l -> pure ()
                | otherwise ->
                    modify $ Map.insertWith (++) (prior, next) [t2 - t1]
        pure (t2, next)

data Stats a = Stats
    { count :: Int
    , average :: a
    , stddev :: a
    , total :: a
    , maxVal :: a
    , minVal :: a
    }
    deriving stock (Eq, Show)

-- helper structure to compute statistics in one pass
data Stats' a = Stats'
    { count :: Int
    , total :: a
    , squares :: a
    , maxVal :: a
    , minVal :: a
    }

addStats' :: (Ord a, Num a) => Stats' a -> a -> Stats' a
addStats' Stats'{..} x =
    Stats'
        { count = count + 1
        , total = total + x
        , squares = squares + x * x
        , maxVal = max maxVal x
        , minVal = min minVal x
        }

singleStats' :: Num a => a -> Stats' a
singleStats' x =
    Stats'{count = 1, total = x, squares = x * x, maxVal = x, minVal = x}

finaliseStats :: (Floating a) => Stats' a -> Stats a
finaliseStats Stats'{..} = Stats{..}
  where
    average = total / fromIntegral count
    stddev = sqrt $ squares / fromIntegral count - average * average

collectStats ::
    forall tag.
    TimingStateMachine tag =>
    [(Timestamp, tag)] ->
    Map (tag, tag) (Stats Double)
collectStats =
    Map.map finaliseStats
        . snd
        . flip runState Map.empty
        . fold1M collect
        . map (first ((/ 1000) . fromIntegral)) -- microseconds
  where
    collect ::
        (Double, tag) ->
        (Double, tag) ->
        State (Map (tag, tag) (Stats' Double)) (Double, tag)
    collect (t1, prior) (t2, next) = do
        case label prior next of
            Nothing -> do
                traceM $
                    "WARNING: Undefined transition " <> show prior <> " --> " <> show next
                modify $ Map.alter (add $ t2 - t1) (prior, next)
            Just l
                | Text.null l -> pure ()
                | otherwise ->
                    modify $ Map.alter (add $ t2 - t1) (prior, next)
        pure (t2, next)

    add :: Double -> Maybe (Stats' Double) -> Maybe (Stats' Double)
    add x Nothing = Just $ singleStats' x
    add x (Just s) = Just $ addStats' s x

mkStats :: forall a. (Ord a, Floating a) => [a] -> Stats a
mkStats [] = error "mkStats: empty"
mkStats (x : xs) =
    Stats{count, average, stddev, total = valSum, maxVal, minVal}
  where
    go :: (Int, a, a, a, a) -> a -> (Int, a, a, a, a) -- basically Stats'
    go (cnt, acc, squareAcc, accMax, accMin) xx =
        (cnt + 1, acc + xx, squareAcc + xx * xx, max accMax xx, min accMin xx)

    (count, valSum, squareSum, maxVal, minVal) = foldl go (1, x, x * x, x, x) xs
    average = valSum / fromIntegral count
    stddev = sqrt $ squareSum / fromIntegral count - average * average

mapStatistics ::
    Map (tag, tag) [Double] ->
    Map (tag, tag) (Stats Double)
mapStatistics = Map.map mkStats

printForDot ::
    forall tag. TimingStateMachine tag => (tag, tag) -> Stats Double -> String
printForDot (t1, t2) Stats{count, average, stddev, total} =
    printf
        "%s -> %s\n\
        \  [ penwidth=%.1f,\n\
        \    label=\"%s. %.2fμs (+-%.2f), total #%d (%s)\",\n\
        \    fontsize=10 ]"
        (show t1)
        (show t2)
        (max 0.1 $ log @Double $ fromIntegral count / 50)
        (fromMaybe "UNEXPECTED" $ label t1 t2)
        average
        stddev
        count
        (humanReadable total)
  where
    humanReadable :: Double -> String
    humanReadable x
        | x > 10 ** 5 = printf "%.2fs" $ x / 10 ** 6
        | x > 10 ** 2 = printf "%.3fms" $ x / 10 ** 3
        | otherwise = printf "%.1fμs" x
