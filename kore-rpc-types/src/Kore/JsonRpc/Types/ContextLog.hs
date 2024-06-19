{-# LANGUAGE PatternSynonyms #-}
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
    deriving stock (Generic, Data, Enum, Show, Eq, Ord)

pattern CBooster, CKore, CProxy :: CLContext
pattern CBooster = CLNullary CtxBooster
pattern CKore = CLNullary CtxKore
pattern CProxy = CLNullary CtxProxy

-- method
pattern CExecute, CSimplify, CImplies, CGetModel, CAddModule :: CLContext
pattern CExecute = CLNullary CtxExecute
pattern CSimplify = CLNullary CtxSimplify
pattern CImplies = CLNullary CtxImplies
pattern CGetModel = CLNullary CtxGetModel
pattern CAddModule = CLNullary CtxAddModule

-- mode/phase
pattern CInternalise, CMatch, CDefinedness, CConstraint, CSMT, CLlvm, CCached :: CLContext
pattern CInternalise = CLNullary CtxInternalise
pattern CMatch = CLNullary CtxMatch
pattern CDefinedness = CLNullary CtxDefinedness
pattern CConstraint = CLNullary CtxConstraint
pattern CSMT = CLNullary CtxSMT
pattern CLlvm = CLNullary CtxLlvm
pattern CCached = CLNullary CtxCached

-- results
pattern CFailure, CIndeterminate, CAbort, CSuccess, CBreak, CContinue :: CLContext
pattern CFailure = CLNullary CtxFailure
pattern CIndeterminate = CLNullary CtxIndeterminate
pattern CAbort = CLNullary CtxAbort
pattern CSuccess = CLNullary CtxSuccess
pattern CBreak = CLNullary CtxBreak
pattern CContinue = CLNullary CtxContinue

-- information
pattern CKoreTerm, CDetail, CSubstitution, CDepth :: CLContext
pattern CKoreTerm = CLNullary CtxKoreTerm
pattern CDetail = CLNullary CtxDetail
pattern CSubstitution = CLNullary CtxSubstitution
pattern CDepth = CLNullary CtxDepth

-- standard log levels
pattern CError, CWarn, CInfo :: CLContext
pattern CError = CLNullary CtxError
pattern CWarn = CLNullary CtxWarn
pattern CInfo = CLNullary CtxInfo

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
    | CtxCeil UniqueId
    | CtxTerm UniqueId
    | -- entities with name
      CtxHook Text
    deriving stock (Generic, Eq)

-- To/FromJSON by way of Generic

instance Show IdContext where
    show (CtxRewrite uid) = "rewrite " <> show uid
    show (CtxSimplification uid) = "simplification " <> show uid
    show (CtxFunction uid) = "function " <> show uid
    show (CtxCeil uid) = "ceil " <> show uid
    show (CtxTerm uid) = "term " <> show uid
    show (CtxHook name) = "simplification " <> unpack name

pattern CRewrite, CSimplification, CFunction, CCeil, CTerm :: UniqueId -> CLContext
pattern CRewrite u = CLWithId (CtxRewrite u)
pattern CSimplification u = CLWithId (CtxSimplification u)
pattern CFunction u = CLWithId (CtxFunction u)
pattern CCeil u = CLWithId (CtxCeil u)
pattern CTerm u = CLWithId (CtxTerm u)

pattern CHook :: Text -> CLContext
pattern CHook t = CLWithId (CtxHook t)

----------------------------------------
data UniqueId
    = ShortId Text -- short hashes (7 char)
    | LongId Text -- long hashes (64 char)
    | UNKNOWN
    deriving stock (Generic, Eq, Ord)

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

----------------------------------------
data LogLine = LogLine
    { context :: [CLContext]
    , message :: CLMessage
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[] LogLine

data CLMessage
    = CLText Text -- generic log message
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
