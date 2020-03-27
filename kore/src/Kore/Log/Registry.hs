{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Log.Registry
    ( parseEntryType
    , toSomeEntryType
    , lookupTextFromTypeWithError
    , registry
    , typeToText
    , textToType
    , getEntryTypesAsText
    , typeOfSomeEntry
    -- entry types
    , debugAppliedRuleType
    , debugAxiomEvaluationType
    , debugSolverSendType
    , debugSolverRecvType
    , warnBottomHookType
    , warnFunctionWithoutEvaluatorsType
    , debugSkipSimplificationType
    , infoAttemptUnificationType
    , errorRewritesInstantiationType
    ) where

import Prelude.Kore

import Data.Functor.Classes
    ( eq2
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Tuple
    ( swap
    )
import Data.Typeable
    ( Proxy (..)
    )
import qualified Text.Megaparsec as Parser
import Type.Reflection
    ( SomeTypeRep (..)
    , someTypeRep
    , typeOf
    )

import Kore.Log.DebugAppliedRewriteRules
    ( DebugAppliedRewriteRules
    )
import Kore.Log.DebugAppliedRule
    ( DebugAppliedRule
    )
import Kore.Log.DebugAxiomEvaluation
    ( DebugAxiomEvaluation
    )
import Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition
    )
import Kore.Log.DebugProofState
    ( DebugProofState
    )
import Kore.Log.DebugSkipSimplification
    ( DebugSkipSimplification
    )
import Kore.Log.DebugSolver
    ( DebugSolverRecv
    , DebugSolverSend
    )
import Kore.Log.ErrorException
    ( ErrorException
    )
import Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation
    )
import Kore.Log.InfoAttemptUnification
    ( InfoAttemptUnification
    )
import Kore.Log.InfoReachability
    ( InfoReachability
    )
import Kore.Log.WarnBottomHook
    ( WarnBottomHook
    )
import Kore.Log.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators
    )
import Log
    ( Entry
    , LogMessage
    , SomeEntry (..)
    )

data Registry =
    Registry
    { textToType :: !(Map Text SomeTypeRep)
    , typeToText :: !(Map SomeTypeRep Text)
    }

-- | A registry of log entry types and their textual representations.
-- It is used for user input validation in kore-exec and kore-repl and
-- for pretty printing information about log entries.
-- When adding a new entry type you should register it here.
registry :: Registry
registry =
    let textToType =
            Map.fromList
                [ register debugAppliedRuleType
                , register debugAxiomEvaluationType
                , register debugSolverSendType
                , register debugSolverRecvType
                , register debugProofStateType
                , register debugAppliedRewriteRulesType
                , register warnBottomHookType
                , register warnFunctionWithoutEvaluatorsType
                , register debugSkipSimplificationType
                , register logDebugEvaluateConditionType
                , register criticalExecutionErrorType
                , register logMessageType
                , register infoAttemptUnificationType
                , register infoReachabilityType
                , register errorRewritesInstantiationType
                ]
        typeToText = makeInverse textToType
    in if textToType `eq2` makeInverse typeToText
          then Registry { textToType, typeToText }
          else
            error
                "Failure to create Kore.Log.Registry.registry.\
                \ The maps 'textToType' and 'typeToText'\
                \ should be inverses of eachother."
  where
    register :: SomeTypeRep -> (Text, SomeTypeRep)
    register type' =
        (asText type', type')

asText :: SomeTypeRep -> Text
asText = Text.pack . show

makeInverse
    :: Ord k2
    => Map k1 k2 -> Map k2 k1
makeInverse map' =
    Map.fromList
    $ swap
    <$> Map.toList map'

debugAppliedRuleType
  , debugAxiomEvaluationType
  , debugSolverSendType
  , debugSolverRecvType
  , debugProofStateType
  , debugAppliedRewriteRulesType
  , warnBottomHookType
  , warnFunctionWithoutEvaluatorsType
  , debugSkipSimplificationType
  , logDebugEvaluateConditionType
  , criticalExecutionErrorType
  , logMessageType
  , infoAttemptUnificationType
  , infoReachabilityType
  , errorRewritesInstantiationType
  :: SomeTypeRep

debugAppliedRuleType =
    someTypeRep (Proxy :: Proxy DebugAppliedRule)
debugAxiomEvaluationType =
    someTypeRep (Proxy :: Proxy DebugAxiomEvaluation)
debugSolverSendType =
    someTypeRep (Proxy :: Proxy DebugSolverSend)
debugSolverRecvType =
    someTypeRep (Proxy :: Proxy DebugSolverRecv)
debugProofStateType =
    someTypeRep (Proxy :: Proxy DebugProofState)
debugAppliedRewriteRulesType =
    someTypeRep (Proxy :: Proxy DebugAppliedRewriteRules)
warnBottomHookType =
    someTypeRep (Proxy :: Proxy WarnBottomHook)
warnFunctionWithoutEvaluatorsType =
    someTypeRep (Proxy :: Proxy WarnFunctionWithoutEvaluators)
debugSkipSimplificationType =
    someTypeRep (Proxy :: Proxy DebugSkipSimplification)
logDebugEvaluateConditionType =
    someTypeRep (Proxy :: Proxy DebugEvaluateCondition)
criticalExecutionErrorType =
    someTypeRep (Proxy :: Proxy ErrorException)
logMessageType =
    someTypeRep (Proxy :: Proxy LogMessage)
infoAttemptUnificationType =
    someTypeRep (Proxy :: Proxy InfoAttemptUnification)
infoReachabilityType =
    someTypeRep (Proxy :: Proxy InfoReachability)
errorRewritesInstantiationType =
    someTypeRep (Proxy :: Proxy ErrorRewritesInstantiation)

lookupTextFromTypeWithError :: SomeTypeRep -> Text
lookupTextFromTypeWithError type' =
    fromMaybe notFoundError
    $ Map.lookup type' (typeToText registry)
  where
    notFoundError =
        error
            $ "Tried to log nonexistent entry type: "
            <> show type'
            <> " It should be added to Kore.Log.Registry.registry."

parseEntryType :: Text -> Parser.Parsec String String SomeTypeRep
parseEntryType entryText =
    maybe empty return
    $ Map.lookup entryText (textToType registry)

toSomeEntryType :: Entry entry => entry -> SomeTypeRep
toSomeEntryType =
    SomeTypeRep . typeOf

{- | The entry type underlying the 'SomeEntry' wrapper.
 -}
typeOfSomeEntry :: SomeEntry -> SomeTypeRep
typeOfSomeEntry (SomeEntry entry) = SomeTypeRep (typeOf entry)

getEntryTypesAsText :: [Text]
getEntryTypesAsText = Map.keys . textToType $ registry
