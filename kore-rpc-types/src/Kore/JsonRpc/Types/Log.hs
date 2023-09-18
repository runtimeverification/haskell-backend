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
    StripPrefix,
 )

data LogOrigin = KoreRpc | Booster | Llvm | Proxy
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON
                '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]]
                LogOrigin

data LogRewriteResult
    = Success
        { rewrittenTerm :: Maybe KoreJson
        , substitution :: Maybe KoreJson
        , ruleId :: Text
        }
    | Failure
        { reason :: Text
        , _ruleId :: Maybe Text
        }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON
                '[ OmitNothingFields
                 , FieldLabelModifier '[CamelToKebab, StripPrefix "_"]
                 , ConstructorTagModifier '[CamelToKebab]
                 ]
                LogRewriteResult

data LogEntry
    = Rewrite
        { result :: LogRewriteResult
        , origin :: LogOrigin
        }
    | Simplification
        { originalTerm :: Maybe KoreJson
        , originalTermIndex :: Maybe [Int]
        , result :: LogRewriteResult
        , origin :: LogOrigin
        }
    | -- | summatory timing, by origin or overall
      ProcessingTime
        { component :: Maybe LogOrigin
        , time :: Double
        }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON
                '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]]
                LogEntry
