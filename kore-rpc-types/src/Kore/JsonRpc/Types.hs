{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Kore.JsonRpc.Types (
    module Kore.JsonRpc.Types,
    module Kore.JsonRpc.Types.Depth,
) where

import Control.Exception (Exception)
import Data.Aeson.Encode.Pretty qualified as PrettyJson
import Data.Aeson.Types (FromJSON (..), ToJSON (..))
import Data.Text (Text)
import Deriving.Aeson (
    CamelToKebab,
    ConstructorTagModifier,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
    StripPrefix,
 )
import GHC.Generics (Generic)
import Kore.JsonRpc.Types.Depth (Depth (..))
import Kore.JsonRpc.Types.Log (LogEntry)
import Kore.Syntax.Json.Types (KoreJson)
import Network.JSONRPC (
    FromRequest (..),
 )
import Prettyprinter qualified as Pretty

data ExecuteRequest = ExecuteRequest
    { state :: !KoreJson
    , maxDepth :: !(Maybe Depth)
    , _module :: !(Maybe Text)
    , cutPointRules :: !(Maybe [Text])
    , terminalRules :: !(Maybe [Text])
    , movingAverageStepTimeout :: !(Maybe Bool)
    , stepTimeout :: !(Maybe Int)
    , assumeStateDefined :: !(Maybe Bool)
    , logSuccessfulRewrites :: !(Maybe Bool)
    , logFailedRewrites :: !(Maybe Bool)
    , logSuccessfulSimplifications :: !(Maybe Bool)
    , logFailedSimplifications :: !(Maybe Bool)
    , logFallbacks :: !(Maybe Bool)
    , logTiming :: !(Maybe Bool)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab, StripPrefix "_"]] ExecuteRequest

data ImpliesRequest = ImpliesRequest
    { antecedent :: !KoreJson
    , consequent :: !KoreJson
    , _module :: !(Maybe Text)
    , logSuccessfulSimplifications :: !(Maybe Bool)
    , logFailedSimplifications :: !(Maybe Bool)
    , logTiming :: !(Maybe Bool)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab, StripPrefix "_"]] ImpliesRequest

data SimplifyRequest = SimplifyRequest
    { state :: KoreJson
    , _module :: !(Maybe Text)
    , logSuccessfulSimplifications :: !(Maybe Bool)
    , logFailedSimplifications :: !(Maybe Bool)
    , logTiming :: !(Maybe Bool)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab, StripPrefix "_"]] SimplifyRequest

data AddModuleRequest = AddModuleRequest
    { _module :: Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[FieldLabelModifier '[StripPrefix "_"]] AddModuleRequest

data GetModelRequest = GetModelRequest
    { state :: KoreJson
    , _module :: !(Maybe Text)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab, StripPrefix "_"]] GetModelRequest

data ReqException = CancelRequest deriving stock (Show)

instance Exception ReqException

instance FromRequest (API 'Req) where
    parseParams "execute" = Just $ fmap (Execute <$>) parseJSON
    parseParams "implies" = Just $ fmap (Implies <$>) parseJSON
    parseParams "simplify" = Just $ fmap (Simplify <$>) parseJSON
    parseParams "add-module" = Just $ fmap (AddModule <$>) parseJSON
    parseParams "get-model" = Just $ fmap (GetModel <$>) parseJSON
    parseParams "cancel" = Just $ const $ return Cancel
    parseParams _ = Nothing

data ExecuteState = ExecuteState
    { term :: KoreJson
    , substitution :: Maybe KoreJson
    , predicate :: Maybe KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteState

data HaltReason
    = Branching
    | Stuck
    | Vacuous
    | DepthBound
    | CutPointRule
    | TerminalRule
    | Aborted
    | Timeout
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, ConstructorTagModifier '[CamelToKebab]] HaltReason

data ExecuteResult = ExecuteResult
    { reason :: HaltReason
    , depth :: Depth
    , state :: ExecuteState
    , nextStates :: Maybe [ExecuteState]
    , rule :: Maybe Text
    , logs :: Maybe [LogEntry]
    , unknownPredicate :: Maybe KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteResult

data Condition = Condition
    { substitution :: KoreJson
    , predicate :: KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] Condition

data ImpliesResult = ImpliesResult
    { implication :: KoreJson
    , satisfiable :: Bool
    , condition :: Maybe Condition
    , logs :: Maybe [LogEntry]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ImpliesResult

data SimplifyResult = SimplifyResult
    { state :: KoreJson
    , logs :: Maybe [LogEntry]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] SimplifyResult

data AddModuleResult = AddModuleResult {_module :: !Text}
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[FieldLabelModifier '[StripPrefix "_"]] AddModuleResult

data GetModelResult = GetModelResult
    { satisfiable :: SatResult
    , substitution :: Maybe KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] GetModelResult

data SatResult
    = Sat
    | Unsat
    | Unknown
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON, ToJSON)
        via CustomJSON '[] SatResult

data ReqOrRes = Req | Res

data APIMethod
    = ExecuteM
    | ImpliesM
    | SimplifyM
    | AddModuleM
    | GetModelM
    deriving stock (Eq, Ord, Show, Enum)

type family APIPayload (api :: APIMethod) (r :: ReqOrRes) where
    APIPayload 'ExecuteM 'Req = ExecuteRequest
    APIPayload 'ExecuteM 'Res = ExecuteResult
    APIPayload 'ImpliesM 'Req = ImpliesRequest
    APIPayload 'ImpliesM 'Res = ImpliesResult
    APIPayload 'SimplifyM 'Req = SimplifyRequest
    APIPayload 'SimplifyM 'Res = SimplifyResult
    APIPayload 'AddModuleM 'Req = AddModuleRequest
    APIPayload 'AddModuleM 'Res = AddModuleResult
    APIPayload 'GetModelM 'Req = GetModelRequest
    APIPayload 'GetModelM 'Res = GetModelResult

data API (r :: ReqOrRes) where
    Execute :: APIPayload 'ExecuteM r -> API r
    Implies :: APIPayload 'ImpliesM r -> API r
    Simplify :: APIPayload 'SimplifyM r -> API r
    AddModule :: APIPayload 'AddModuleM r -> API r
    GetModel :: APIPayload 'GetModelM r -> API r
    Cancel :: API 'Req

deriving stock instance Show (API 'Req)
deriving stock instance Show (API 'Res)
deriving stock instance Eq (API 'Req)
deriving stock instance Eq (API 'Res)

instance ToJSON (API 'Res) where
    toJSON = \case
        Execute payload -> toJSON payload
        Implies payload -> toJSON payload
        Simplify payload -> toJSON payload
        AddModule payload -> toJSON payload
        GetModel payload -> toJSON payload

instance Pretty.Pretty (API 'Req) where
    pretty = \case
        Execute _ -> "execute"
        Implies _ -> "implies"
        Simplify _ -> "simplify"
        AddModule _ -> "add-module"
        GetModel _ -> "get-model"
        Cancel -> "cancel"

rpcJsonConfig :: PrettyJson.Config
rpcJsonConfig =
    PrettyJson.defConfig
        { PrettyJson.confCompare =
            PrettyJson.keyOrder
                [ "format"
                , "version"
                , "term"
                , "tag"
                , "assoc"
                , "name"
                , "symbol"
                , "argSort"
                , "sort"
                , "sorts"
                , "var"
                , "varSort"
                , "arg"
                , "args"
                , "argss"
                , "source"
                , "dest"
                , "value"
                , "jsonrpc"
                , "id"
                , "reason"
                , "depth"
                , "rule"
                , "state"
                , "next-states"
                , "substitution"
                , "predicate"
                , "satisfiable"
                , "implication"
                , "condition"
                , "module"
                , "step-timeout"
                , "moving-average-step-timeout"
                ]
        }

class FromRequest q => FromRequestCancellable q where
    isCancel :: q -> Bool

instance FromRequestCancellable (API 'Req) where
    isCancel Cancel = True
    isCancel _ = False
