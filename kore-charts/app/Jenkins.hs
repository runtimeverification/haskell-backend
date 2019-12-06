module Jenkins
    ( Job (..), getJob
    , matchProfiled
    , getBuildStats
    , Build (..), getBuild
    , Builds, getBuilds
    ) where

import qualified Control.Lens as Lens
import Data.Aeson
    ( FromJSON
    )
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import Data.Map
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Monoid
    ( First (getFirst)
    )
import qualified Data.Text as Text
import Data.Traversable
import GHC.Generics
    ( Generic
    )
import qualified Network.Wreq as Wreq
import Prelude hiding
    ( filter
    )
import Stats
    ( Stats
    )

import Plot
    ( BuildNumber
    )

jenkins :: String
jenkins = "http://office.runtimeverification.com/jenkins"

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
