module FrameDict (
    FrameName (..),
    FrameId (..),
    FrameDict (frameNames, frameFilter),
    FrameFilter (..),
    empty,
    insert,
    lookup,
    toList,
) where

import Prelude hiding (lookup)

import Data.Aeson (ToJSON)
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import Data.Text (Text)
import GHC.Generics (Generic)

import Data.Aeson qualified as Aeson
import Data.HashMap.Strict qualified as HashMap
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as Text

newtype FrameName = FrameName {unFrameName :: Text}
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance Hashable FrameName

instance ToJSON FrameName where
    toJSON FrameName{unFrameName} =
        Aeson.object ["name" Aeson..= unFrameName]

newtype FrameId = FrameId {unFrameId :: Int}
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance ToJSON FrameId where
    toJSON = Aeson.toJSON . unFrameId

data FrameFilter = FrameFilter
    { matchingIds :: !(Set FrameId)
    , notMatchingIds :: !(Set FrameId)
    , notMatchingChildrenIds :: !(Set FrameId)
    }

updateFrameFilter ::
    FrameFilter -> [Text] -> [Text] -> [Text] -> FrameId -> FrameName -> FrameFilter
updateFrameFilter
    FrameFilter
        { matchingIds
        , notMatchingIds
        , notMatchingChildrenIds
        }
    matching
    notMatching
    notMatchingChildren
    frameId
    FrameName{unFrameName} =
        FrameFilter
            { matchingIds = matchingIds <> match matching
            , notMatchingIds = notMatchingIds <> match notMatching
            , notMatchingChildrenIds = notMatchingChildrenIds <> match notMatchingChildren
            }
      where
        match toMatch =
            if any (`Text.isInfixOf` unFrameName) toMatch
                then Set.singleton frameId
                else mempty

data FrameDict = FrameDict
    { frameNames :: !(Map FrameId FrameName)
    , frameIds :: !(HashMap FrameName FrameId)
    , size :: !Int
    , frameFilter :: !FrameFilter
    }

empty :: FrameDict
empty =
    FrameDict
        { frameNames = Map.empty
        , frameIds = HashMap.empty
        , size = 0
        , frameFilter = FrameFilter mempty mempty mempty
        }

insert :: FrameName -> [Text] -> [Text] -> [Text] -> FrameDict -> (FrameId, Maybe FrameDict)
insert frameName matching notMatching notMatchingChildren frameDict =
    case HashMap.lookup frameName (frameIds frameDict) of
        Just frameId -> (frameId, Nothing)
        Nothing ->
            let frameId = FrameId (size frameDict)
                frameDict' =
                    FrameDict
                        { frameNames = Map.insert frameId frameName (frameNames frameDict)
                        , frameIds = HashMap.insert frameName frameId (frameIds frameDict)
                        , size = unFrameId frameId + 1
                        , frameFilter =
                            updateFrameFilter (frameFilter frameDict) matching notMatching notMatchingChildren frameId frameName
                        }
             in (frameId, Just frameDict')

lookup :: FrameId -> FrameDict -> Maybe FrameName
lookup frameId frameDict = Map.lookup frameId (frameNames frameDict)

toList :: FrameDict -> [FrameName]
toList = Map.elems . frameNames
