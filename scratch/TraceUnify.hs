{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module TraceUnify where

import Control.Monad.State
import Data.Bifunctor (first)
import Data.List (sortBy)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.RTS.Events
import System.Environment
import System.IO
import Text.Printf

main :: IO ()
main = do
    args <- getArgs
    -- option processing here, future work
    when (null args) $ putStrLn "No eventlog files given, nothing to do."
    forM_ args $ \file -> do
        putStr $ file <> "..."
        hFlush stdout
        lines <- logStats file
        let contents = printf "digraph \"%s\" {\n%s\n}\n" file (unlines lines)
        writeFile (file <> ".dot") contents
        putStrLn "Done"

logStats :: FilePath -> IO [String]
logStats file = do
    timingMap <- collectTimings . getMarkers <$> readLog file
    let statMap = mapStatistics timingMap
    pure $ map (uncurry printForDot) $ Map.assocs statMap

logStats_ :: FilePath -> IO [String]
logStats_ file = do
    statMap <- collectStats . getMarkers <$> readLog file
    pure $ map (uncurry printForDot) $ Map.assocs statMap

readLog :: FilePath -> IO [Event]
readLog file =
    readEventLogFromFile file
        >>= either error (pure . sortBy (comparing evTime) . events . dat)

getMarkers :: [Event] -> [(Timestamp, UnifyTag)]
getMarkers = mapMaybe getMarker
  where
    getMarker Event{..}
        | UserMarker{markername} <- evSpec =
            fmap (evTime,) $ readTag markername
        | otherwise =
            Nothing
    readTag :: Text -> Maybe UnifyTag
    readTag t
        | ("unify" : tag : rest) <- Text.splitOn ":" t =
            decodeTag tag
        | otherwise =
            Nothing


{-

UnifyRules markers as a state machine:


Rules --> Rule     EndRules
         /  |          A
        /   |          |
       /    |          |
      /     V          |
     /     Init        |
    /       |         /|
   /        |        / |
   |        |       /  |
   |        V      /   |
   +----- Start---/    |
   |        |         /|
   |        |        / |
   |        |       /  |
   |        V      /   |
   +----- Actual--/    |
   |        |          |
   |        |         /|
   |        |        / |
   |        V       /  |
   +----- Side ----/   |
   |        |          /
   |        |         /
    \       |        /
     \      V       /
      \--- End ----/
-}

data UnifyTag
    = -- | starting to unify term with a set of rules
      Rules
    | -- | starting work on one rule (Logic.scatter)
      Rule
    | -- | starting work on one rule (worker function)
      Init
    | -- | starting fast check for one rule
      Start
    | -- | starting unification for one rule
      Actual
    | -- | checking side conditions for one rule
      Side
    | -- | successful unification using one rule
      End
    | -- | ending term unification
      EndRules
    deriving (Eq, Ord, Enum, Bounded, Show)

decodeTag :: Text -> Maybe UnifyTag
decodeTag = flip Map.lookup tags

-- keep this top-level to cache it
tags :: Map Text UnifyTag
tags = Map.fromList [(Text.pack $ show tag, tag) | tag <- [minBound .. maxBound]]

label :: UnifyTag -> UnifyTag -> Maybe Text
label prior next = Map.lookup (prior, next) transitionLabels

transitionLabels :: Map (UnifyTag, UnifyTag) Text
transitionLabels = Map.fromList
    [ Rules --> Rule $ "Starting"
    , Rule --> Init $ "InRule"
--    , Rule --> EndRules "Ended" -- ???
    , Init --> Start $ "Init"
    , Start --> Actual $ "FastCheckPassed"
    , Start --> Rule $ "FailedFast"
    , Start --> EndRules $ "FailedFast"
    , Actual --> Side $ "Unified"
    , Actual --> Rule $ "UnifyFailed"
    , Actual --> EndRules $ "UnifyFailed"
    , Side --> End $ "SideChecked"
    , Side --> Rule $ "SideFailed"
    , Side --> EndRules $ "SideFailed"
    , End --> Rule $ "Success"
    , End --> EndRules $ "Success"
    , EndRules --> Rules $ Text.empty -- technical edge, should be filtered out
    ]
  where
    (-->) :: UnifyTag -> UnifyTag -> Text -> ((UnifyTag, UnifyTag), Text)
    t1 --> t2 = ((t1, t2),)

{- Collect timings for all state transitions in the machine above from
 the trace event sequence. 'UnifyTag's are unique transition signals
 so timings are stored in a 'Map (UnifyState, UnifyState) [Int]'.
 Time precision is _nanoseconds_ (same as in the GHC events).
-}
collectTimings ::
    [(Timestamp, UnifyTag)] ->
    Map (UnifyTag, UnifyTag) [Double]
collectTimings =
    snd
        . flip runState Map.empty
        . fold1M collect
        . map (first ((/ 1000) . fromIntegral)) -- microsecond timestamps
  where
    collect ::
        (Double, UnifyTag) ->
        (Double, UnifyTag) ->
        State (Map (UnifyTag, UnifyTag) [Double]) (Double, UnifyTag)
    collect (t1, prior) (t2, next) = do
        case label prior next of
            Nothing ->
                error $ "Undefined transition " <> show prior <> " --> " <> show next
            Just l
                | Text.null l -> pure (t2, next) -- omit
                | otherwise -> do
                      modify $ Map.insertWith (++) (prior, next) [t2 - t1]
                      pure (t2, next)

fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M f [] = error "foldM1: empty"
fold1M f (x : xs) = foldM f x xs

data Stats a = Stats
    { count :: Int
    , average :: a
    , stddev :: a
    , total :: a
    , maxVal :: a
    , minVal :: a
    }
    deriving (Eq, Show)

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

finaliseStats :: (Num a, Floating a) => Stats' a -> Stats a
finaliseStats Stats'{..} = Stats{..}
  where
    average = total / fromIntegral count
    stddev = sqrt $ squares / fromIntegral count - average * average

collectStats ::
    [(Timestamp, UnifyTag)] ->
    Map (UnifyTag, UnifyTag) (Stats Double)
collectStats =
    Map.map finaliseStats
        . snd
        . flip runState Map.empty
        . fold1M collect
        . map (first ( (/ 1000) . fromIntegral)) -- microseconds
  where
    collect ::
        (Double, UnifyTag) ->
        (Double, UnifyTag) ->
        State (Map (UnifyTag, UnifyTag) (Stats' Double)) (Double, UnifyTag)
    collect (t1, prior) (t2, next) =
        case label prior next of
            Nothing ->
                error $ "Undefined transition " <> show prior <> " --> " <> show next
            Just l
                | Text.null l -> pure (t2, next) -- omit
                | otherwise -> do
                      modify $ Map.alter (add $ t2 - t1) (prior, next)
                      pure (t2, next)

    add :: Double -> Maybe (Stats' Double) -> Maybe (Stats' Double)
    add x Nothing = Just $ singleStats' x
    add x (Just s) = Just $ addStats' s x

{-
* include totals (as a table and in the graph)
* for each transition, analyse/plot all timings to find outliers and humps
* compare with a version without fast path

* Link existing trace event system (O/C <component>) to this analysis
  - combine speed-scope diagram and state machine

-}

mkStats :: forall a. (Ord a, Num a, Floating a) => [a] -> Stats a
mkStats [] = error "mkStats: empty"
mkStats (x : xs) =
    Stats{count, average, stddev, total = valSum, maxVal, minVal}
  where
    go :: (Int, a, a, a, a) -> a -> (Int, a, a, a, a) -- basically Stats'
    go (count, acc, squareAcc, accMax, accMin) xx =
        (count + 1, acc + xx, squareAcc + xx * xx, max accMax xx, min accMin xx)

    (count, valSum, squareSum, maxVal, minVal) = foldl go (1, x, x * x, x, x) xs
    average = valSum / fromIntegral count
    stddev = sqrt $ squareSum / fromIntegral count - average * average

mapStatistics ::
    Map (UnifyTag, UnifyTag) [Double] ->
    Map (UnifyTag, UnifyTag) (Stats Double)
mapStatistics = Map.map mkStats

printForDot :: (UnifyTag, UnifyTag) -> Stats Double -> String
printForDot (t1, t2) Stats{count, average, stddev, total, maxVal, minVal} =
    printf
        "%s -> %s [penwidth=%.1f, label=\"%s. %.2fμs (+-%.2f), total #%d (%s)\" ]"
        (show t1)
        (show t2)
        (max 0.1 $ log @Double $ fromIntegral count / 50)
        (fromJust $ label t1 t2) -- safe, transitions have been checked before
        average
        stddev
        count
        (humanReadable total)
  where
    humanReadable :: Double -> String
    humanReadable x
        | x > 10 ^ 5 = printf "%.2fs" $ x / 10 ^ 6
        | x > 10 ^ 2 = printf "%.3fms" $ x / 10 ^ 3
        | otherwise = printf "%.1fμs" x
