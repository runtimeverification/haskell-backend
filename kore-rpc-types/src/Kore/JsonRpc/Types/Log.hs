{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.JsonRpc.Types.Log (module Kore.JsonRpc.Types.Log) where
import Kore.Syntax.Json.Types (KoreJson)
import Data.Text (Text)
import GHC.Generics (Generic)
import Data.Aeson (FromJSON, ToJSON)

import Deriving.Aeson (
    CamelToKebab,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
 )

data LogSimplificationResult = Success {
    rewrittenTerm :: Maybe KoreJson,
    ruleId :: Text
  } |
  Failure {
    reason :: Text,
    ruleId :: Text
  }
  deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] LogSimplificationResult

data LogEntry = 
    RewriteSuccess {
      rewrittenTerm :: Maybe KoreJson,
      ruleId :: Text
    } |
    RewriteFailure {
      reason :: Text,
      ruleId :: Text
    } |
    LlvmSimplification {
      originalTerm :: Maybe KoreJson,
      result :: LogSimplificationResult
    } |
    Simplification {
      originalTerm :: Maybe KoreJson,
      result :: LogSimplificationResult
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] LogEntry