module Plot
    ( layoutStats
    , Time (..)
    , Space (..)
    , Log10 (..), log10
    , BuildNumber (..)
    ) where

import Control.Lens
    ( (.~)
    )
import Control.Lens
    ( (.=)
    )
import Data.Aeson
    ( FromJSON
    )
import qualified Data.Aeson as Aeson
import Data.Bifunctor
import Data.Default
    ( def
    )
import Data.Function
import Data.Map
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromMaybe
    )
import Data.Semigroup
    ( Max (..)
    )
import Data.Semigroup
    ( Min (..)
    )
import GHC.Generics
    ( Generic
    )
import qualified Graphics.Rendering.Chart as Chart
import qualified Graphics.Rendering.Chart.Easy as Chart
import Prelude hiding
    ( filter
    )
import qualified System.FilePath as FilePath

import Stats
    ( Stats
    )
import qualified Stats

newtype Time = Time { getTime :: Double }
    deriving (Eq, Ord, Read, Show)
    deriving (Floating, Fractional, Num, Real, RealFloat, RealFrac)

instance Chart.PlotValue Time where
    toValue = getTime
    fromValue = Time
    autoAxis = Chart.autoScaledAxis def

newtype Space = Space { getSpace :: Double }
    deriving (Eq, Ord, Read, Show)
    deriving (Floating, Fractional, Num, Real, RealFloat, RealFrac)

instance Chart.PlotValue Space where
    toValue = getSpace
    fromValue = Space
    autoAxis = Chart.autoScaledAxis def

newtype Log10 a = Log10 { getLog10 :: a }
    deriving (Eq, Ord, Read, Show)
    deriving (Floating, Fractional, Num, Real, RealFloat, RealFrac)

log10 :: RealFloat a => a -> Log10 a
log10 = Log10 . logBase 10

instance
    (Chart.PlotValue a, RealFloat a, Show a)
    => Chart.PlotValue (Log10 a)
  where
    toValue = Chart.toValue . getLog10
    fromValue = Log10 . Chart.fromValue
    autoAxis points = Chart.scaledAxis def (inf, sup) points
      where
        inf =
            fromInteger . floor   . getMin . fromMaybe 0
            $ foldMap (Just . Min) points
        sup =
            fromInteger . ceiling . getMax . fromMaybe 0
            $ foldMap (Just . Max) points

layoutStats
    :: FilePath
    -> Map BuildNumber Stats
    -> Chart.LayoutLR Double (Log10 Time) (Log10 Space)
layoutStats artifactName (Map.toList -> stats) = Chart.execEC $ do
    Chart.layoutlr_title .= title
    Chart.layoutlr_title_style .= titleStyle
    Chart.layoutlr_x_axis     . Chart.laxis_title .= "Build number"
    Chart.layoutlr_left_axis  . Chart.laxis_title .= "log_10(time / s)"
    Chart.layoutlr_right_axis . Chart.laxis_title .= "log_10(space / Mbyte)"
    Chart.plotLeft $ Chart.line "MUT CPU"
        [ bimap fromBuildNumber (log10 . mutator_cpu_sec) <$> stats ]
    Chart.plotLeft $ Chart.line "GC CPU"
        [ bimap fromBuildNumber (log10 . gc_cpu_sec) <$> stats ]
    Chart.plotRight $ Chart.line "max. live"
        [ bimap fromBuildNumber (log10 . max_live_mbytes) <$> stats ]
    Chart.plotRight $ Chart.line "allocated"
        [ bimap fromBuildNumber (log10 . allocated_mbytes) <$> stats ]
  where
    title = FilePath.dropExtension . FilePath.takeFileName $ artifactName
    titleStyle =
        def
        & Chart.font_size .~ 14
        & Chart.font_weight .~ Chart.FontWeightBold

fromBuildNumber :: BuildNumber -> Double
fromBuildNumber = fromInteger . unBuildNumber

newtype BuildNumber = BuildNumber { unBuildNumber :: Integer }
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance FromJSON BuildNumber where
    parseJSON value = BuildNumber <$> Aeson.parseJSON value

gc_cpu_sec, mutator_cpu_sec :: Stats -> Time
gc_cpu_sec = (/ 1_000_000_000) . fromIntegral . Stats.gc_cpu_ns
mutator_cpu_sec = (/ 1_000_000_000) . fromIntegral . Stats.mutator_cpu_ns

allocated_mbytes, max_live_mbytes :: Stats -> Space
allocated_mbytes = (/ 1_000_000) . fromIntegral . Stats.allocated_bytes
max_live_mbytes = (/ 1_000_000) . fromIntegral . Stats.max_live_bytes
