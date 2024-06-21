module Stats (
    newStats,
    addStats,
    finaliseStats,
    timed,
    microsWithUnit,
    RequestStats (..),
    StatsVar,
    MethodTiming (..),
) where

import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar, readMVar)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Aeson
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (pack)
import Deriving.Aeson
import GHC.Generics ()
import Prettyprinter
import System.Clock
import Text.Printf

import Booster.Log
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
    deriving stock (Eq, Show, Generic)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[FieldLabelModifier '[CamelToKebab]] (RequestStats a)

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

{-# SPECIALIZE addStats' :: Stats' Double -> Stats' Double -> Stats' Double #-}
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

-- helper type mainly for json logging
data MethodTiming a = MethodTiming {method :: APIMethod, time :: a, koreTime :: a}
    deriving stock (Eq, Show, Generic)
    deriving
        (ToJSON, FromJSON)
        via CustomJSON '[FieldLabelModifier '[CamelToKebab]] (MethodTiming a)

instance ToLogFormat (MethodTiming Double) where
    toTextualLog mt =
        pack $
            printf
                "Performed %s in %s (%s kore time)"
                (show mt.method)
                (microsWithUnit mt.time)
                (microsWithUnit mt.koreTime)
    toJSONLog = toJSON

addStats ::
    MonadIO m =>
    MVar (Map APIMethod (Stats' Double)) ->
    MethodTiming Double ->
    m ()
addStats statVar MethodTiming{method, time, koreTime} =
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

newtype FinalStats = FinalStats (Map APIMethod (RequestStats Double))
    deriving stock (Eq, Show)
    deriving newtype (FromJSON, ToJSON)

instance Pretty FinalStats where
    pretty (FinalStats stats) =
        vsep $
            [ "---------------------------"
            , "RPC request time statistics"
            , "---------------------------"
            ]
                <> map (\(k, v) -> hang 4 $ vsep [pretty $ show k <> ": ", pretty v]) (Map.assocs stats)

instance ToLogFormat FinalStats where
    toTextualLog = renderText . pretty
    toJSONLog = toJSON

finaliseStats :: MVar (Map APIMethod (Stats' Double)) -> IO FinalStats
finaliseStats var = FinalStats . Map.map finalise <$> readMVar var
  where
    finalise :: Floating a => Stats' a -> RequestStats a
    finalise Stats'{count, total, squares, maxVal, minVal, koreTotal, koreMax} =
        let average = total / fromIntegral count
            stddev = sqrt $ squares / fromIntegral count - average * average
            koreAverage = koreTotal / fromIntegral count
         in RequestStats
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
