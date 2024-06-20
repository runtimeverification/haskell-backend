{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Kore.JsonRpc.Types.ContextLog (
    module Kore.JsonRpc.Types.ContextLog,
) where

import Data.Aeson.TH (deriveJSON)
import Data.Aeson.Types (FromJSON (..), ToJSON (..), defaultOptions)
import Data.Aeson.Types qualified as JSON
import Data.Char (toLower)
import Data.Data (Data, toConstr)
import Data.Sequence (Seq)
import Data.Text (Text, unpack)
import Data.Text qualified as Text

data SimpleContext
    = -- component
      CtxBooster
    | CtxKore
    | CtxProxy
    | -- method
      CtxExecute
    | CtxSimplify
    | CtxImplies
    | CtxGetModel
    | CtxAddModule
    | -- mode/phase
      CtxInternalise
    | CtxMatch
    | CtxDefinedness
    | CtxConstraint
    | CtxSMT
    | CtxLlvm
    | CtxCached
    | -- results
      CtxFailure
    | CtxIndeterminate
    | CtxAbort
    | CtxSuccess
    | CtxBreak
    | CtxContinue
    | -- information
      CtxKoreTerm
    | CtxDetail
    | CtxSubstitution
    | CtxDepth
    | -- standard log levels
      CtxError
    | CtxWarn
    | CtxInfo
    deriving stock (Eq, Ord, Enum, Data)

instance Show SimpleContext where
    show = JSON.camelTo2 '-' . drop 3 . show . toConstr

$( deriveJSON
    defaultOptions
        { JSON.constructorTagModifier = JSON.camelTo2 '-' . drop 3
        , JSON.sumEncoding = JSON.ObjectWithSingleField
        }
 ''SimpleContext)

----------------------------------------
data IdContext
    = -- entities with hex identifier
      CtxRewrite UniqueId
    | CtxSimplification UniqueId
    | CtxFunction UniqueId
    | CtxCeil UniqueId
    | CtxTerm UniqueId
    | -- entities with name
      CtxHook Text
    deriving stock (Eq)

instance Show IdContext where
    show (CtxRewrite uid) = "rewrite " <> show uid
    show (CtxSimplification uid) = "simplification " <> show uid
    show (CtxFunction uid) = "function " <> show uid
    show (CtxCeil uid) = "ceil " <> show uid
    show (CtxTerm uid) = "term " <> show uid
    show (CtxHook name) = "hook " <> unpack name

----------------------------------------
data UniqueId
    = ShortId Text -- short hashes (7 char)
    | LongId Text -- long hashes (64 char)
    | UNKNOWN
    deriving stock (Eq, Ord)

instance Show UniqueId where
    show (ShortId x) = unpack x
    show (LongId x) = unpack $ Text.take 7 x -- for parity with legacy log
    show UNKNOWN = "UNKNOWN"

parseUId :: Text -> Maybe UniqueId
parseUId "UNKNOWN" = pure UNKNOWN
parseUId hex
    | Text.length hex == 7 = Just $ ShortId hex
    | Text.length hex == 64 = Just $ LongId hex
    | otherwise = Nothing

instance FromJSON UniqueId where
    parseJSON = JSON.withText "Hash ID" parseHex
      where
        parseHex :: Text -> JSON.Parser UniqueId
        parseHex hex =
            maybe (JSON.parseFail $ "Bad hash ID: " <> show hex) pure $ parseUId hex

instance ToJSON UniqueId where
    toJSON = \case
        ShortId x -> JSON.String x
        LongId x -> JSON.String x
        UNKNOWN -> JSON.String "UNKNOWN"

$( deriveJSON
    defaultOptions
        { JSON.constructorTagModifier = JSON.camelTo2 '-' . drop 3
        , JSON.sumEncoding = JSON.ObjectWithSingleField
        }
    ''IdContext
 )

----------------------------------------
data CLContext
    = CLNullary SimpleContext
    | CLWithId IdContext
    deriving stock (Eq)

instance Show CLContext where
    show (CLNullary c) = show c
    show (CLWithId withId) = show withId

instance ToJSON CLContext where
    toJSON (CLNullary c) = toJSON c
    toJSON (CLWithId withId) = toJSON withId

instance FromJSON CLContext where
    parseJSON = \case
        simple@JSON.String{} ->
            CLNullary <$> parseJSON simple
        obj@JSON.Object{} ->
            CLWithId <$> parseJSON obj
        other ->
            JSON.typeMismatch "Object or string" other

----------------------------------------
data CLMessage
    = CLText Text -- generic log message
    | CLValue JSON.Value -- other stuff
    deriving stock (Eq)

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

data LogLine = LogLine
    { context :: Seq CLContext
    , message :: CLMessage
    }
    deriving stock (Show, Eq)

$(deriveJSON defaultOptions ''LogLine)
