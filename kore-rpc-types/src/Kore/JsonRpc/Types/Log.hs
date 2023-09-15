{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.JsonRpc.Types.Log (module Kore.JsonRpc.Types.Log) where

import Data.Aeson (FromJSON, ToJSON)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
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
        { originalTerm :: !(Maybe KoreJson)
        , result :: !(LogRewriteResult)
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
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON
                '[OmitNothingFields, FieldLabelModifier '[CamelToKebab], ConstructorTagModifier '[CamelToKebab]]
                LogEntry
