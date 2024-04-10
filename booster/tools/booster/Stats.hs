module Stats (
    newStats,
    addStats,
    finaliseStats,
    showStats,
    timed,
    microsWithUnit,
    RequestStats (..),
    StatsVar,
) where

import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar, readMVar)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Map (Map)
import Data.Map qualified as Map
import Prettyprinter
import System.Clock
import Text.Printf

import Booster.Prettyprinter
import Kore.JsonRpc.Types (APIMethod)

-- server statistics
data RequestStats a = RequestStats
    { count :: Int
    , average :: a
    , stddev :: a
    , total :: a
    , maxVal :: a
    , minVal :: a
    , koreTotal :: a
    , koreAverage :: a
    , koreMax :: a
    }
    deriving stock (Eq, Show)

instance (Floating a, PrintfArg a, Ord a) => Pretty (RequestStats a) where
    pretty stats =
        vsep
            [ "Requests: " <> pretty stats.count
            , "Total time: " <> withUnit stats.total
            , "Average time per request:"
                <+> withUnit stats.average
                <+> parens ("+-" <+> withUnit stats.stddev)
                    <> ", range"
                <+> brackets (withUnit stats.minVal <> ", " <> withUnit stats.maxVal)
            , "Total time in kore-rpc code:"
                <+> withUnit stats.koreTotal
            , "Average time per request in kore-rpc code:"
                <+> withUnit stats.koreAverage
                    <> ", max"
                <+> withUnit stats.koreMax
            ]
      where
        withUnit = pretty . microsWithUnit

microsWithUnit :: (Floating a, Ord a, PrintfArg a) => a -> String
microsWithUnit x
    | x > 10 ** 5 = printf "%.2fs" $ x / 10 ** 6
    | x > 10 ** 2 = printf "%.3fms" $ x / 10 ** 3
    | otherwise = printf "%.1fμs" x

-- internal helper type
-- all values are in microseconds
data Stats' a = Stats'
    { count :: Int
    , total :: a
    , squares :: a
    , maxVal :: a
    , minVal :: a
    , koreTotal :: a
    , koreMax :: a
    }

instance (Ord a, Num a) => Semigroup (Stats' a) where
    (<>) = addStats'

-- FIXME specialise to Double (pragma)
addStats' :: (Ord a, Num a) => Stats' a -> Stats' a -> Stats' a
addStats' stats1 stats2 =
    Stats'
        { count = stats1.count + stats2.count
        , total = stats1.total + stats2.total
        , squares = stats1.squares + stats2.squares
        , maxVal = max stats1.maxVal stats2.maxVal
        , minVal = min stats1.minVal stats2.minVal
        , koreTotal = stats1.koreTotal + stats2.koreTotal
        , koreMax = max stats1.koreMax stats2.koreMax
        }

singleStats' :: Num a => a -> a -> Stats' a
singleStats' x korePart =
    Stats'
        { count = 1
        , total = x
        , squares = x * x
        , maxVal = x
        , minVal = x
        , koreTotal = korePart
        , koreMax = korePart
        }

type StatsVar = MVar (Map APIMethod (Stats' Double))

addStats ::
    MonadIO m =>
    MVar (Map APIMethod (Stats' Double)) ->
    APIMethod ->
    Double ->
    Double ->
    m ()
addStats statVar method time koreTime =
    liftIO . modifyMVar_ statVar $
        pure . Map.insertWith (<>) method (singleStats' time koreTime)

newStats :: MonadIO m => m (MVar (Map APIMethod (Stats' Double)))
newStats = liftIO $ newMVar Map.empty

timed :: MonadIO m => m a -> m (a, Double)
timed action = do
    start <- liftIO $ getTime Monotonic
    result <- action
    stop <- liftIO $ getTime Monotonic
    let time = fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1000.0
    pure (result, time)

finaliseStats :: Floating a => Stats' a -> RequestStats a
finaliseStats Stats'{count, total, squares, maxVal, minVal, koreTotal, koreMax} =
    RequestStats
        { count
        , total
        , average
        , stddev
        , maxVal
        , minVal
        , koreTotal
        , koreAverage
        , koreMax
        }
  where
    average = total / fromIntegral count
    stddev = sqrt $ squares / fromIntegral count - average * average
    koreAverage = koreTotal / fromIntegral count

showStats :: MVar (Map APIMethod (Stats' Double)) -> IO ()
showStats var = do
    statMap <- readMVar var
    let finalStats =
            Map.elems . Map.mapWithKey prettyAssoc . Map.map finaliseStats $ statMap
    putStrLn . renderDefault . vsep $
        [ "---------------------------"
        , "RPC request time statistics"
        , "---------------------------"
        ]
            <> finalStats
  where
    prettyAssoc key value = hang 4 $ vsep [pretty $ show key <> ": ", pretty value]
