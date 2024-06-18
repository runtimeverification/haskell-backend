{-# OPTIONS_GHC -Wno-partial-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Kore.JsonRpc.Types.ContextLog (
    module Kore.JsonRpc.Types.ContextLog,
) where

import Data.Aeson.Types (FromJSON (..), ToJSON (..))
import Data.Aeson.Types qualified as JSON
import Data.Data
import Data.List (stripPrefix)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, unpack)
import Data.Text qualified as Text
import Data.Tuple (swap)
import Deriving.Aeson
import Numeric

data CLContext
    = CLNullary SimpleContext
    | CLWithId IdContext
    deriving stock (Generic, Eq)

instance Show CLContext where
    show (CLNullary c) = fromMaybe (error $ show c) $ Map.lookup c simpleShow
    show (CLWithId withId) = show withId

instance ToJSON CLContext where
    toJSON (CLNullary c) = JSON.String $ maybe (error $ show c) pack $ Map.lookup c simpleShow
    toJSON (CLWithId withId) = JSON.genericToJSON options withId

instance FromJSON CLContext where
    parseJSON = \case
        JSON.String simple
            | Just c <- Map.lookup (unpack simple) simpleRead ->
                pure $ CLNullary c
        obj@JSON.Object{} ->
            CLWithId <$> JSON.genericParseJSON options obj
        other ->
            JSON.typeMismatch "Object or string" other

options :: JSON.Options
options =
    JSON.defaultOptions
    { JSON.sumEncoding = JSON.ObjectWithSingleField
    , JSON.constructorTagModifier = toJsonName
    , JSON.allNullaryToStringTag = True
    }

toJsonName :: String -> String
toJsonName name = JSON.camelTo2 '-' $ fromMaybe name $ stripPrefix "Ctx" name

----------------------------------------
data SimpleContext
    = -- component
      CtxBooster
    | CtxKore
    | CtxProxy
    -- method
    | CtxExecute
    | CtxSimplify
    | CtxImplies
    | CtxGetModel
    -- mode/phase
    | CtxMatch
    | CtxDefinedness
    | CtxConstraint
    -- results
    | CtxFailure
    | CtxAbort
    | CtxSuccess
    -- information
    | CtxKoreTerm
    | CtxDetail
    -- standard log levels
    | CtxError
    | CtxWarn
    | CtxInfo
    deriving stock (Generic, Data, Enum, Show, Eq, Ord)

-- translation table for nullary constructors
translateSimple :: [(SimpleContext, String)]
translateSimple =
    [ (con, toJsonName $ show con)
    | con <- [CtxBooster .. CtxInfo]
    ]

simpleShow :: Map SimpleContext String
simpleShow = Map.fromList translateSimple

simpleRead :: Map String SimpleContext
simpleRead = Map.fromList $ map swap translateSimple

----------------------------------------
data IdContext
    = -- entities with hex identifier
      CtxRewrite UniqueId
    | CtxSimplification UniqueId
    | CtxFunction UniqueId
    | CtxTerm UniqueId
    -- entities with name
    | CtxHook Text
    deriving stock (Generic, Eq)

-- To/FromJSON by way of Generic

instance Show IdContext where
    show (CtxRewrite uid) = "rewrite " <> show uid
    show (CtxSimplification uid) = "simplification " <> show uid
    show (CtxFunction uid) = "function " <> show uid
    show (CtxTerm uid) = "term " <> show uid
    show (CtxHook name) = "simplification " <> unpack name

----------------------------------------
data UniqueId
    = Hex7 Int -- short hashes (7 char)
    | Hex64 Integer -- long hashes (64 char)
    | UNKNOWN
    deriving stock (Generic, Eq, Ord)

instance Show UniqueId where
    show (Hex7 i) = showHex i ""
    show (Hex64 i) = showHex i ""
    show UNKNOWN = "UNKNOWN"

parseUId :: Text -> Maybe UniqueId
parseUId "UNKNOWN" = pure UNKNOWN
parseUId hex =
    case readHex $ unpack hex of
        [(h, "")]
            | Text.length hex < 8 -> Just $ Hex7 (fromIntegral h)
            | Text.length hex <= 64 -> Just $ Hex64 h
        _otherwise -> Nothing

instance FromJSON UniqueId where
    parseJSON = JSON.withText "Hexadecimal Hash" parseHex
      where
        parseHex :: Text -> JSON.Parser UniqueId
        parseHex hex =
            maybe (JSON.parseFail $ "Bad hash value: " <> show hex) pure $ parseUId hex

instance ToJSON UniqueId where
    toJSON = \case
        Hex7 x ->
            JSON.String . pad0 7 . pack $ showHex x ""
        Hex64 x ->
            JSON.String . pad0 64 . pack $ showHex x ""
        UNKNOWN ->
            JSON.String "UNKNOWN"
      where
          pad0 l = Text.takeEnd l . (Text.replicate l "0" <>)


----------------------------------------
data LogLine
    = LogLine
      { context :: [CLContext]
      , message :: CLMessage
      }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[] LogLine

data CLMessage
    = CLText Text  -- generic log message
    | CLValue JSON.Value -- other stuff
    deriving stock (Generic, Eq)

instance Show CLMessage where
    show (CLText t) = unpack t
    show (CLValue value) = show value

-- a message is a term if it is an object with format: KORE
instance FromJSON CLMessage where
    parseJSON (JSON.String msg) = pure $ CLText msg
    parseJSON obj@JSON.Object{} = pure $ CLValue obj
    parseJSON arr@JSON.Array{} = pure $ CLValue arr
    parseJSON other =
        JSON.typeMismatch "Object, array, or string" other

instance ToJSON CLMessage where
    toJSON (CLText text) = toJSON text
    toJSON (CLValue value) = value
