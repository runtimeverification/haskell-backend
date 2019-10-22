module Main (main) where

import Data.Traversable

import Data.Aeson (FromJSON)
import Data.Map (Map)
import GHC.Generics (Generic)

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Control.Lens as Lens
import qualified Network.Wreq as Wreq

jenkins :: String
jenkins = "https://office.runtimeverification.com/jenkins"

main :: IO ()
main = do
    job <- getJob "haskell-backend" "master"
    builds <- getBuilds job
    print builds

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

newtype BuildNumber = BuildNumber Integer
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance FromJSON BuildNumber

data Build =
    Build
    { number :: BuildNumber
    , result :: Result
    , artifacts :: [Artifact]
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Build

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
