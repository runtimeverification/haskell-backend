{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.JsonRpc.Types.Log (module Kore.JsonRpc.Types.Log) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import GHC.Generics (Generic)
import Kore.Syntax.Json.Types (KoreJson)

import Deriving.Aeson (
    CamelToKebab,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
 )

data LogSimplificationResult
    = Success
        { rewrittenTerm :: Maybe KoreJson
        , ruleId :: Text
        }
    | Failure
        { reason :: Text
        , ruleId :: Text
        }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] LogSimplificationResult

data LogEntry
    = RewriteSuccess
        { rewrittenTerm :: Maybe KoreJson
        , ruleId :: Text
        , origin :: Text
        }
    | RewriteFailure
        { reason :: Text
        , ruleId :: Text
        , origin :: Text
        }
    | LlvmSimplification
        { originalTerm :: Maybe KoreJson
        , result :: LogSimplificationResult
        , origin :: Text
        }
    | Simplification
        { originalTerm :: Maybe KoreJson
        , result :: LogSimplificationResult
        , origin :: Text
        }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] LogEntry
