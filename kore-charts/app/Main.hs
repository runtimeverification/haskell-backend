module Main (main) where

import Prelude hiding (filter)

import Control.Applicative
import Data.Traversable
import Data.Witherable

import Data.Aeson (FromJSON)
import Data.Map (Map)
import Data.Monoid (First (getFirst))
import Data.Scientific (Scientific)
import GHC.Generics (Generic)

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.Attoparsec.ByteString as Attoparsec
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
    let profiled = mapMaybe matchProfiled builds
    buildProfiles <- Map.traverseWithKey (getBuildProfile builds) profiled
    print buildProfiles

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
    , url :: String
    , artifacts :: [Artifact]
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Build

matchProfiled :: Build -> Maybe Artifact
matchProfiled Build { artifacts } =
    getFirst (foldMap matchFileName artifacts)
  where
    matchFileName artifact@Artifact { fileName }
      | fileName == "profile.json" = pure artifact
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

getBuildProfile :: Builds -> BuildNumber -> Artifact -> IO BuildProfile
getBuildProfile builds buildNumber Artifact { relativePath } = do
    let Just Build { url } = Map.lookup buildNumber builds
        url' = url <> "artifact/" <> relativePath
    response <- Wreq.get url'
    Lens.view Wreq.responseBody <$> Wreq.asJSON response

type BuildProfile = Map String Profile

jsons :: Attoparsec.Parser [Aeson.Value]
jsons = some Aeson.json <* Attoparsec.endOfInput

asJSONs
    :: FromJSON json
    => Wreq.Response ByteString
    -> IO (Wreq.Response [json])

data Profile =
    Profile
    { user_sec :: Scientific
    , resident_kbytes :: Integer
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Profile
