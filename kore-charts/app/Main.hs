module Main (main) where

import Prelude hiding (filter)

import Data.Foldable
import Data.Function
import Data.Witherable

import Data.Map (Map)
import Stats (Stats)

import Control.Lens ((.~))
import Data.Default (def)

import qualified Data.Map.Strict as Map
import qualified Graphics.Rendering.Chart as Chart
import qualified Graphics.Rendering.Chart.Backend.Cairo as Chart.Backend
import qualified Graphics.Rendering.Chart.Grid as Chart
import qualified Stats
import qualified System.Directory as Directory
import qualified System.Environment as Environment
import qualified System.FilePath as FilePath

import Jenkins
import Plot

main :: IO ()
main = do
    artifactNames <- Environment.getArgs
    builds <- getBuilds =<< getJob "haskell-backend" "master"
    for_ artifactNames (main1 builds)

main1 :: Builds -> FilePath -> IO ()
main1 builds artifactName = do
    latestStats <- getLatestStats artifactName
    olderStats <-
        mapMaybe (matchProfiled artifactName) builds
        & Map.traverseWithKey (getBuildStats builds)
    let stats = insertLatestStats latestStats olderStats
        layout = layoutStats artifactName stats
        fileOptions = def & Chart.Backend.fo_size .~ (400, 400)
        pngFileName = FilePath.replaceExtension artifactName "png"
    _ <-
        Chart.gridToRenderable (Chart.layoutLRToGrid layout)
        & Chart.Backend.renderableToFile fileOptions pngFileName
    return ()

getLatestStats :: FilePath -> IO (Maybe Stats)
getLatestStats artifactName = do
    exists <- Directory.doesFileExist artifactName
    if not exists
        then return Nothing
        else Just <$> Stats.readStats artifactName

insertLatestStats
    :: Maybe Stats
    -> Map BuildNumber Stats
    -> Map BuildNumber Stats
insertLatestStats Nothing buildStats = buildStats
insertLatestStats (Just stats) buildStats =
    Map.insert thisBuildNumber stats buildStats
  where
    thisBuildNumber = maybe (BuildNumber 1) fst (Map.lookupMax buildStats)
