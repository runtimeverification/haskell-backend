module Main (main) where

import Prelude hiding (filter)

import Control.Applicative
import Control.Monad
import Control.Monad.Catch
import Data.Foldable
import Data.Function
import Data.Traversable
import Data.Witherable

import Control.Lens (Traversal')
import Data.Aeson (FromJSON)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as Lazy (ByteString)
import Data.Map (Map)
import Data.Monoid (First (getFirst))
import Data.Scientific (Scientific)
import GHC.Generics (Generic)

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.Attoparsec.ByteString.Lazy as Attoparsec
import qualified Data.ByteString as ByteString
import qualified Data.List as List
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
    profiles <- Lens.view Wreq.responseBody <$> asJSONs response
    return (fold profiles)

type BuildProfile = Map String Profile

-- | The only valid whitespace in a JSON document is space, newline,
-- carriage return, and tab.
skipSpace :: Attoparsec.Parser ()
skipSpace = Attoparsec.skipWhile $ \w -> any (== w) [ 0x20, 0x0a, 0x0d, 0x09 ]

{- | Parse a sequence of JSON values.

This is not a valid JSON document, but it's easy to work with and I don't care.

 -}
jsons :: Attoparsec.Parser [Aeson.Value]
jsons = some Aeson.json <* skipSpace <* Attoparsec.endOfInput

responseContentType :: Traversal' (Wreq.Response body) ByteString
responseContentType = Wreq.responseHeader "Content-Type"

asJSONs
    :: FromJSON json
    => Wreq.Response Lazy.ByteString
    -> IO (Wreq.Response [json])
asJSONs response = withContext $ do
    assertContentTypeJSON response
    let responseBody = Lens.view Wreq.responseBody response
    values <- fromJSONs responseBody
    responseBody' <- traverse fromValue values
    return (responseBody' <$ response)
  where
    isContentTypeJSON contentType
      | ByteString.isPrefixOf "application/json" contentType = True
      | ByteString.isPrefixOf "application/" contentType
      , ByteString.isSuffixOf "+json" contentType = True
      | otherwise = False

    unknownContentType =
        throwM $ Wreq.JSONError "unknown content type of response"

    wrongContentType contentType =
        throwM . Wreq.JSONError
        $ "content type of response is " ++ show contentType

    assertContentTypeJSON resp = do
        contentType <- getContentType resp
        unless (isContentTypeJSON contentType) (wrongContentType contentType)

    getContentType resp =
        Lens.preview responseContentType resp
        & maybe unknownContentType return

    fromJSONs :: Lazy.ByteString -> IO [Aeson.Value]
    fromJSONs body =
        parseOnly jsons body
        & either (throwM . Wreq.JSONError) return

    fromValue value =
        Aeson.parseEither Aeson.parseJSON value
        & either (throwM . Wreq.JSONError) return

    withContext =
        flip onException $ do
            putStrLn "While parsing:"
            print (Lens.view Wreq.responseBody response)

parseOnly :: Attoparsec.Parser a -> Lazy.ByteString -> Either String a
parseOnly parser byteString =
    case Attoparsec.parse parser byteString of
        Attoparsec.Fail _ [] err   -> Left err
        Attoparsec.Fail _ ctxs err ->
            Left (List.intercalate " > " ctxs ++ ": " ++ err)
        Attoparsec.Done _ a        -> Right a

data Profile =
    Profile
    { user_sec :: Scientific
    , resident_kbytes :: Integer
    }
    deriving (Show)
    deriving (Generic)

instance FromJSON Profile
