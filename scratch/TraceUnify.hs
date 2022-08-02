{-# Language DuplicateRecordFields #-}
{-# Language ImportQualifiedPost #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language RecordWildCards #-}
{-# Language TupleSections #-}
{-# Language TypeApplications #-}

module TraceUnify where

import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.RTS.Events
import System.IO
import System.Environment
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
logStats  file = do
    timingMap <- collectTimings . getMarkers <$> readLog file
    let statMap = mapStatistics timingMap
    pure $ map (uncurry printForDot) $ Map.assocs statMap


logStats_ :: FilePath -> IO [String]
logStats_  file = do
    statMap <- collectStats . getMarkers <$> readLog file
    pure $ map (uncurry printForDot) $ Map.assocs statMap

readLog :: FilePath -> IO [Event]
readLog file =
    readEventLogFromFile file >>=
    either error (pure . events . dat)

getMarkers :: [Event] -> [(Timestamp, UnifyTag)]
getMarkers = mapMaybe getMarker
    where
      getMarker Event{..}
          | UserMarker{markername} <- evSpec = fmap (evTime,) $ readTag markername
          | otherwise = Nothing

readTag :: Text -> Maybe UnifyTag
readTag t
    | ("unify" : tag : rest) <- parts =
          Just $ read (Text.unpack tag) -- FIXME catch exceptions?
    | otherwise =
          error $ "cannot read " <> show t -- Nothing
  where
    parts = Text.splitOn ":" t

{-

UnifyRules markers as a state machine:

None
  --Rules-->
   Started --Rule--> InRule --EndRules --> Ended
                    /  |                    A
                 e / Init                   |
                l /    |                 End|Rules
               u /     V                    |
              R /   RuleInit                |
               /       |                   /|
              /      Start                / |
              |        |                 /  |
              |        V                /   |
              +--- FastCheck ----------/    |
              |        |                   /|
              |       Actual              / |
              |        |                 /  |
              |        V                /   |
              +----- Unify-------------/    |
              |        |                    |
              |       Side                 /|
              |        |                  / |
              |        V                 /  |
              +--- CheckSide -----------/   |
              |        |                   /
              |       End                 /
               \       |                 /
                \      V                /
                  RuleSuccess----------/
-}

data UnifyTag
    = Rules
      -- ^ starting to unify term with a set of rules
    | Rule
      -- ^ starting work on one rule (Logic.scatter)
    | Init
      -- ^ starting work on one rule (worker function)
    | Start
      -- ^ starting fast check for one rule
    | Actual
      -- ^ starting unification for one rule
    | Side
      -- ^ checking side conditions for one rule
    | End
      -- ^ successful unification using one rule
    | EndRules
      -- ^ ending term unification
    deriving (Eq, Enum, Show, Read)

data UnifyState
    = None
    | Started
    | InRule
    | RuleInit
    | FastCheck
    | Unify
    | CheckSide
    | RuleSuccess
    | Ended
    | Error
    deriving (Eq, Ord, Enum, Show, Read)

transition :: UnifyState -> UnifyTag -> UnifyState
transition None Rules = Started
transition Ended Rules = Started -- technical¸ filtered out later
--------------------
transition Started Rule = InRule
--------------------
transition InRule Init = RuleInit
transition InRule EndRules = Ended
--------------------
transition RuleInit Start = FastCheck
--------------------
transition FastCheck Actual = Unify
transition FastCheck Rule = InRule
transition FastCheck EndRules = Ended
--------------------
transition Unify Side = CheckSide
transition Unify Rule = InRule
transition Unify EndRules = Ended
--------------------
transition CheckSide End = RuleSuccess
transition CheckSide Rule = InRule
transition CheckSide EndRules = Ended
--------------------
transition RuleSuccess Rule = InRule
transition RuleSuccess EndRules = Ended
--------------------
transition otherState otherTag =
    error $ "Transition from " <> show otherState <>
            " with " <> show otherTag <> " not defined"
-- transition _ _ = Error
-- transition Error _ = Error

{- Collect timings for all state transitions in the machine above from
 the trace event sequence. 'UnifyTag's are unique transition signals
 so timings are stored in a 'Map (UnifyState, UnifyState) [Int]'.
 Time precision is _nanoseconds_ (same as in the GHC events).
-}
collectTimings ::
    [(Timestamp, UnifyTag)] ->
    Map (UnifyState, UnifyState) [Double]
collectTimings =
    snd
        . flip runState Map.empty
        . fold1M collect
        . mkStates None
  where
    collect ::
        (Double, UnifyState) ->
        (Double, UnifyState) ->
        State (Map (UnifyState, UnifyState) [Double]) (Double, UnifyState)
    collect (t1, prior) (t2, next) = do
        when (not (prior == Ended && next == Started)) $
            modify  $ Map.insertWith (++) (prior, next) [t2 - t1]
        pure (t2, next)

fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M f [] = error "foldM1: empty"
fold1M f (x:xs) = foldM f x xs

-- compute a sequence of states with _microsec_ timestamps from the
-- sequence of _nanosec_ timestamps and transition tags
mkStates ::
    UnifyState -> [(Timestamp, UnifyTag)] -> [(Double, UnifyState)]
mkStates start [] = []
mkStates start ((t1, next):rest) =
    scanl mkState (fromIntegral t1 / 1000, transition start next) rest
  where
    mkState ::
        (Double, UnifyState) -> (Timestamp, UnifyTag) -> (Double, UnifyState)
    mkState (_, prior) (time, tag) = (fromIntegral time / 1000, transition prior tag)

data Stats a =
    Stats
    { count :: Int
    , average :: a
    , stddev :: a
    , total :: a
    , maxVal :: a
    , minVal :: a
    }
    deriving (Eq, Show)

-- helper structure to compute statistics in one pass
data Stats' a =
    Stats'
    { count :: !Int
    , total :: !a
    , squares :: !a
    , maxVal :: !a
    , minVal :: !a
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
    Stats' { count = 1, total = x, squares = x * x, maxVal = x, minVal = x }

finaliseStats :: (Num a, Floating a) => Stats' a -> Stats a
finaliseStats Stats'{..} = Stats{..}
  where
    average = total / fromIntegral count
    stddev = sqrt $ squares / fromIntegral count - average * average

collectStats ::
    [(Timestamp, UnifyTag)] ->
    Map (UnifyState, UnifyState) (Stats Double)
collectStats =
    Map.map finaliseStats
    . snd
    . flip runState Map.empty
    . fold1M collect
    . mkStates None
  where
    collect ::
        (Double, UnifyState) ->
        (Double, UnifyState) ->
        State (Map (UnifyState, UnifyState) (Stats' Double)) (Double, UnifyState)
    collect (t1, prior) (t2, next) = do
        when (not (prior == Ended && next == Started)) $
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

mkStats :: forall a . (Ord a, Num a, Floating a) => [a] -> Stats a
mkStats [] = error "mkStats: empty"
mkStats (x:xs) =
    Stats{ count, average, stddev, total = valSum, maxVal, minVal}
  where
    go :: (Int, a, a, a, a) -> a -> (Int, a, a, a, a) -- basically Stats'
    go (count, acc, squareAcc, accMax, accMin) xx =
        (count + 1, acc + xx, squareAcc + xx * xx, max accMax xx, min accMin xx)

    (count, valSum, squareSum, maxVal, minVal) = foldl go (1, x, x * x, x, x) xs
    average = valSum / fromIntegral count
    stddev = sqrt $ squareSum / fromIntegral count - average * average

mapStatistics ::
    Map (UnifyState, UnifyState) [Double] ->
    Map (UnifyState, UnifyState) (Stats Double)
mapStatistics = Map.map mkStats

printForDot :: (UnifyState, UnifyState) -> Stats Double -> String
printForDot (s1, s2) Stats{count, average, stddev, total, maxVal, minVal} =
    printf
        "%s -> %s [penwidth=%.1f, label=\"%.2fμs (+-%.2f), total #%d (%s), range %.2f to %.2f\" ]"
        (show s1) (show s2)
        (max 0.1 $ log @Double $ fromIntegral count / 100)
        average stddev count (humanReadable total) minVal maxVal

  where
    humanReadable :: Double -> String
    humanReadable x
        | x > 10^5 = printf "%.2fs" $ x / 10^6
        | x > 10^2 = printf "%.3fms" $ x / 10^3
        | otherwise = printf "%.1fμs" x
