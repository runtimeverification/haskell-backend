module Main (main) where

import Prelude hiding (filter)

import Data.Bifunctor
import Data.Function
import Data.Traversable
import Data.Witherable

import Data.Aeson (FromJSON)
import Data.Map (Map)
import Data.Semigroup (Max (..))
import Data.Semigroup (Min (..))
import Data.Scientific (Scientific)
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
import qualified Data.Scientific as Scientific
import qualified Data.Set as Set
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
    [artifactName] <- Environment.getArgs
    job <- getJob "haskell-backend" "master"
    builds <- getBuilds job
    let profiled = mapMaybe (matchProfiled artifactName) builds
    buildStats <- Map.traverseWithKey (getBuildStats builds) profiled
    let buildNumbers = Map.keysSet builds
        firstBuild = Set.findMin buildNumbers
        lastBuild = Set.findMax buildNumbers
        buildRange = (firstBuild, lastBuild)
        xAxis =
            Chart.scaledAxis def
            $ bimap fromBuildNumber fromBuildNumber buildRange
        yAxisFrom project =
            Chart.scaledAxis def
            $ bimap fromInteger fromInteger yRange
          where
            yRange = (yMin, yMax)
            yMin =
                floor . fromScientific . getMin . fromMaybe 0
                $ foldMap (Just . Min . project) buildStats
            yMax =
                ceiling . fromScientific . getMax . fromMaybe 0
                $ foldMap (Just . Max . project) buildStats
        series =
            [ ("MUT CPU time / s", mutator_cpu_sec)
            , ("max. live memory / Mbyte", max_live_mbytes)
            ]
        grid =
            let
                testName =
                    FilePath.dropExtension . FilePath.takeFileName
                    $ artifactName
                title =
                    testName
                    & Chart.label style Chart.HTA_Left Chart.VTA_Centre
                    & Chart.setPickFn Chart.nullPickFn
                style =
                    def
                    & Chart.font_size .~ 14
                    & Chart.font_weight .~ Chart.FontWeightBold
                layout' yAxis = layoutTest (xAxis, yAxis) buildStats
            in
                Chart.wideAbove title . Chart.besideN
                $ map Chart.layoutToGrid
                $ do
                    (seriesTitle, project) <- series
                    let yAxis = yAxisFrom project
                    [layout' yAxis seriesTitle project]
    let fileOptions = def & Chart.Backend.fo_size .~ (800, 400)
        pngFileName = FilePath.replaceExtension artifactName "png"
    _ <-
        Chart.gridToRenderable grid
        & Chart.fillBackground def
        & Chart.Backend.renderableToFile fileOptions pngFileName
    return ()

fromBuildNumber :: BuildNumber -> Double
fromBuildNumber = fromInteger . unBuildNumber

fromScientific :: Scientific -> Double
fromScientific = logBase 10 . Scientific.toRealFloat

layoutTest
    :: (Chart.AxisFn Double, Chart.AxisFn Double)
    -> Map BuildNumber Stats
    -> String
    -> (Stats -> Scientific)
    -> Chart.Layout Double Double
layoutTest (xAxis, yAxis) profiles title select = Chart.execEC $ do
    let points =
            profiles
            & Map.map fromScientific . Map.map select
            & Map.mapKeys fromBuildNumber
            & Map.toAscList
    Chart.layout_x_axis . Chart.laxis_generate .= xAxis
    Chart.layout_x_axis . Chart.laxis_title .= "Build number"
    Chart.layout_y_axis . Chart.laxis_generate .= yAxis
    Chart.layout_y_axis . Chart.laxis_title .= "log_10(" <> title <> ")"
    Chart.plot $ Chart.line "" [ points ]
  where

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

mutator_cpu_sec :: Stats -> Scientific
mutator_cpu_sec = (/ 1_000_000_000) . fromIntegral . Stats.mutator_cpu_ns

max_live_mbytes :: Stats -> Scientific
max_live_mbytes = (/ 1_000_000) . fromIntegral . Stats.max_live_bytes
