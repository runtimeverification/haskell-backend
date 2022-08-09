{-# LANGUAGE DefaultSignatures #-}
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
import Data.Proxy
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
        lines <- logStats (Proxy :: Proxy UnifyTag) file
        let contents = printf "digraph \"%s\" {\n%s\n}\n" file (unlines lines)
        writeFile (file <> ".dot") contents
        putStrLn "Done"

logStats ::
    forall tag. TimingStateMachine tag => Proxy tag -> FilePath -> IO [String]
logStats _ file = do
    timingMap <- collectTimings @UnifyTag . getMarkers <$> readLog file
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
        >>= either error (pure . sortBy (comparing evTime) . events . dat)

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

------------------------------------------------------------
{-
UnifyRules markers as a state machine:

Rules --> Rule
        /  |
       /   |
      /    V
     /    Init
    /      |
   /       |
   |       |
   |\      V
   | ---FastCheck---
   |       |        \
   |       |        |
   |       |        |
   |\      V        |
   | ----Unify----- |
   |       |       \|
   |       |        |
   |       |        |
   |\      V        |
   | --CheckSide--- |
   |       |       \|
   |       |        |
   |       |        |
   \       V        V
    ---Success--> EndRules
-}

data UnifyTag
    = -- | starting to unify term with a set of rules
      Rules
    | -- | starting work on one rule (Logic.scatter)
      Rule
    | -- | starting work on one rule (worker function)
      Init
    | -- | starting fast check for one rule
      FastCheck
    | -- | starting unification for one rule
      Unify
    | -- | checking side conditions for one rule
      CheckSide
    | -- | successful unification using one rule
      Success
    | -- | ending term unification
      EndRules
    deriving (Eq, Ord, Enum, Bounded, Show)

{- ORMOLU_DISABLE -}
-- since it destroys the alignment of transitionLabels
instance TimingStateMachine UnifyTag where
    readTag t
        | "unify" : tag : rest <- Text.splitOn ":" t =
            Map.lookup tag tagMap
        | otherwise =
            Nothing

    transitionLabels =
        Map.fromList
            [ Rules     --> Rule      $ "Starting"
            , Rule      --> Init      $ "InRule"
            , Init      --> FastCheck $ "Init"
            , FastCheck --> Unify     $ "FastCheckPassed"
            , FastCheck --> Rule      $ "FailedFast"
            , FastCheck --> EndRules  $ "FailedFast"
            , Unify     --> CheckSide $ "Unified"
            , Unify     --> Rule      $ "UnifyFailed"
            , Unify     --> EndRules  $ "UnifyFailed"
            , CheckSide --> Success   $ "SideChecked"
            , CheckSide --> Rule      $ "SideFailed"
            , CheckSide --> EndRules  $ "SideFailed"
            , Success   --> Rule      $ "Success"
            , Success   --> EndRules  $ "Success"
            , EndRules  --> Rules     $ Text.empty -- technical edge, filtered out
            ]
      where
        (-->) :: tag -> tag -> Text -> ((tag, tag), Text)
        t1 --> t2 = ((t1, t2),)
{- ORMOLU_ENABLE -}

------------------------------------------------------------

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
    Map (tag, tag) [Double] ->
    Map (tag, tag) (Stats Double)
mapStatistics = Map.map mkStats

printForDot ::
    forall tag. TimingStateMachine tag => (tag, tag) -> Stats Double -> String
printForDot (t1, t2) Stats{count, average, stddev, total, maxVal, minVal} =
    printf
        "%s -> %s\n\
        \  [ penwidth=%.1f,\n\
        \    label=\"%s. %.2fμs (+-%.2f), total #%d (%s)\",\n\
        \    fontsize=10 ]"
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
