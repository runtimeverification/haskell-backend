{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.JsonRpc.Types.Log (module Kore.JsonRpc.Types.Log) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Aeson.Text (encodeToLazyText)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import Data.Text.Lazy qualified as Text (toStrict)
import GHC.Generics (Generic)
import Kore.JsonRpc.Types.Depth (Depth (..))
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
        { rewrittenTerm :: !(Maybe KoreJson)
        , substitution :: !(Maybe KoreJson)
        , ruleId :: !Text
        }
    | Failure
        { reason :: !Text
        , _ruleId :: !(Maybe Text)
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
        { result :: !(LogRewriteResult)
        , origin :: !LogOrigin
        }
    | Simplification
        { originalTerm :: !(Maybe KoreJson)
        , originalTermIndex :: !(Maybe [Int])
        , result :: !LogRewriteResult
        , origin :: !LogOrigin
        }
    | -- | Indicates a fallback of an RPC-server to a more powerful, but slower backup server, i.e. Booster to Kore
      Fallback
        { originalTerm :: !(Maybe KoreJson)
        -- ^ state before fallback
        , rewrittenTerm :: !(Maybe KoreJson)
        -- ^ state after fallback
        , reason :: !Text
        -- ^ fallback reason
        , fallbackRuleId :: !Text
        -- ^ the rule that caused the fallback
        , recoveryRuleIds :: !(Maybe (NonEmpty Text))
        -- ^ rules applied during fallback, the first rule is the one that caused the fallback
        , recoveryDepth :: !Depth
        -- ^ depth reached in fallback, must be the same as (length ruleIds)
        , origin :: !LogOrigin
        -- ^ proxy server the log was emitted from
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

-- | If the log entry contains the any of the term fields, make them Nothing
logEntryEraseTerms :: LogEntry -> LogEntry
logEntryEraseTerms = \case
    entry@Rewrite{result} -> entry{result = removeTermsFromResult result}
    entry@Simplification{result} -> entry{result = removeTermsFromResult result, originalTerm = Nothing}
    entry@Fallback{} -> entry{originalTerm = Nothing, rewrittenTerm = Nothing}
    entry@ProcessingTime{} -> entry
  where
    removeTermsFromResult :: LogRewriteResult -> LogRewriteResult
    removeTermsFromResult = \case
        Success{ruleId} -> Success{ruleId, rewrittenTerm = Nothing, substitution = Nothing}
        res -> res

-- | Encode a Kore RPC as Text-embedded JSON for stderr/file logging
encodeLogEntryText :: LogEntry -> Text
encodeLogEntryText = Text.toStrict . encodeToLazyText
