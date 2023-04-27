{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.JsonRpc.Types.Log (module Kore.JsonRpc.Types.Log) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import GHC.Generics (Generic)
import Kore.Syntax.Json.Types (KoreJson)

import Deriving.Aeson (
    CamelToKebab,
    ConstructorTagModifier,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
 )

data LogOrigin = KoreRpc | Booster | Llvm
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]] LogOrigin

data LogRewriteResult
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
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]] LogRewriteResult

data LogEntry
    = Rewrite
        { result :: LogRewriteResult
        , origin :: LogOrigin
        }
    | Simplification
        { originalTerm :: Maybe KoreJson
        , result :: LogRewriteResult
        , origin :: LogOrigin
        }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]] LogEntry
