module Main (main) where

import Prelude hiding (filter)

import Data.Bifunctor
import Data.Foldable
import Data.Function
import Data.Traversable
import Data.Witherable

import Data.Aeson (FromJSON)
import Data.Map (Map)
import Data.Semigroup (Max (..))
import Data.Semigroup (Min (..))
import GHC.Generics (Generic)
import Stats (Stats)

import Control.Lens ((.~))
import Control.Lens ((.=))
import Data.Default (def)
import Data.Maybe (fromMaybe)
import Data.Monoid (First (getFirst))

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Control.Lens as Lens
import qualified Graphics.Rendering.Chart as Chart
import qualified Graphics.Rendering.Chart.Backend.Cairo as Chart.Backend
import qualified Graphics.Rendering.Chart.Easy as Chart
import qualified Graphics.Rendering.Chart.Grid as Chart
import qualified Network.Wreq as Wreq
import qualified Stats
import qualified System.Environment as Environment
import qualified System.FilePath as FilePath

jenkins :: String
jenkins = "https://office.runtimeverification.com/jenkins"

main :: IO ()
main = do
    artifactNames <- Environment.getArgs
    for_ artifactNames main1

main1 :: FilePath -> IO ()
main1 artifactName = do
    job <- getJob "haskell-backend" "master"
    builds <- getBuilds job
    let profiled = mapMaybe (matchProfiled artifactName) builds
    buildStats <- Map.traverseWithKey (getBuildStats builds) profiled
    let title = FilePath.dropExtension . FilePath.takeFileName $ artifactName
        titleStyle =
            def
            & Chart.font_size .~ 14
            & Chart.font_weight .~ Chart.FontWeightBold
        layout =
            plotStats buildStats
            & Chart.layoutlr_title .~ title
            & Chart.layoutlr_title_style .~ titleStyle
        fileOptions = def & Chart.Backend.fo_size .~ (400, 400)
        pngFileName = FilePath.replaceExtension artifactName "png"
    _ <-
        Chart.gridToRenderable (Chart.layoutLRToGrid layout)
        & Chart.fillBackground def
        & Chart.Backend.renderableToFile fileOptions pngFileName
    return ()

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

plotStats
    :: Map BuildNumber Stats
    -> Chart.LayoutLR Double (Log10 Time) (Log10 Space)
plotStats (Map.toList -> buildStats) = Chart.execEC $ do
    Chart.layoutlr_x_axis     . Chart.laxis_title .= "Build number"
    Chart.layoutlr_left_axis  . Chart.laxis_title .= "log_10(time / s)"
    Chart.layoutlr_right_axis . Chart.laxis_title .= "log_10(space / Mbyte)"
    Chart.plotLeft $ Chart.line "MUT CPU"
        [ bimap fromBuildNumber (log10 . mutator_cpu_sec) <$> buildStats ]
    Chart.plotLeft $ Chart.line "GC CPU"
        [ bimap fromBuildNumber (log10 . gc_cpu_sec) <$> buildStats ]
    Chart.plotRight $ Chart.line "max. live"
        [ bimap fromBuildNumber (log10 . max_live_mbytes) <$> buildStats ]
    Chart.plotRight $ Chart.line "allocated"
        [ bimap fromBuildNumber (log10 . allocated_mbytes) <$> buildStats ]

fromBuildNumber :: BuildNumber -> Double
fromBuildNumber = fromInteger . unBuildNumber

getJob :: String -> String -> IO Job
getJob project name = do
    let url = jenkins <> "/job/" <> project <> "/job/" <> name <> "/api/json"
    Lens.view Wreq.responseBody <$> (Wreq.asJSON =<< Wreq.get url)

data Job =
    Job
    { builds :: [BuildRef]
    }
    deriving (Generic, Show)

instance FromJSON Job

data BuildRef =
    BuildRef
    { number :: BuildNumber
    , url    :: String
    }
    deriving (Generic, Show)

instance FromJSON BuildRef

getBuild :: BuildRef -> IO Build
getBuild BuildRef { url } = do
    let url' = url <> "/api/json"
    response <- Wreq.get url'
    Lens.view Wreq.responseBody <$> Wreq.asJSON response

getBuilds :: Job -> IO Builds
getBuilds Job { builds } = do
    builds' <- for builds getBuild
    return $ Map.fromList (withNumber <$> builds')
  where
    withNumber build@Build { number } = (number, build)

type Builds = Map BuildNumber Build

newtype BuildNumber = BuildNumber { unBuildNumber :: Integer }
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance FromJSON BuildNumber where
    parseJSON value = BuildNumber <$> Aeson.parseJSON value

data Build =
    Build
    { number :: BuildNumber
    , result :: Result
    , url :: String
    , artifacts :: [Artifact]
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Build

matchProfiled :: FilePath -> Build -> Maybe Artifact
matchProfiled artifactName Build { artifacts } =
    getFirst (foldMap matchFileName artifacts)
  where
    matchFileName artifact@Artifact { fileName }
      | fileName == artifactName   = pure artifact
      | otherwise                  = mempty

data Result = Success | Aborted | Incomplete | Other String
    deriving (Show)

instance FromJSON Result where
    parseJSON (Aeson.String "SUCCESS") = return Success
    parseJSON (Aeson.String "ABORTED") = return Aborted
    parseJSON (Aeson.String other    ) = return (Other (Text.unpack other))
    parseJSON Aeson.Null               = return Incomplete
    parseJSON v =
        Aeson.prependFailure "Result"
        $ Aeson.typeMismatch "Null or String" v

data Artifact =
    Artifact
    { fileName     :: String
    , relativePath :: FilePath
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Artifact

getBuildStats :: Builds -> BuildNumber -> Artifact -> IO Stats
getBuildStats builds buildNumber Artifact { relativePath } = do
    let Just Build { url } = Map.lookup buildNumber builds
        url' = url <> "artifact/" <> relativePath
    response <- Wreq.get url'
    Lens.view Wreq.responseBody <$> Wreq.asJSON response

gc_cpu_sec, mutator_cpu_sec :: Stats -> Time
gc_cpu_sec = (/ 1_000_000_000) . fromIntegral . Stats.gc_cpu_ns
mutator_cpu_sec = (/ 1_000_000_000) . fromIntegral . Stats.mutator_cpu_ns

allocated_mbytes, max_live_mbytes :: Stats -> Space
allocated_mbytes = (/ 1_000_000) . fromIntegral . Stats.allocated_bytes
max_live_mbytes = (/ 1_000_000) . fromIntegral . Stats.max_live_bytes
