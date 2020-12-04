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
    , entryTypeReps
    ) where

import Prelude.Kore

import Data.Functor.Classes
    ( eq2
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Text.Megaparsec as Parser
import Type.Reflection
    ( SomeTypeRep (..)
    , someTypeRep
    , typeOf
    )

import Kore.Equation.Application
    ( DebugApplyEquation
    , DebugAttemptEquation
    )
import Kore.Log.DebugAppliedRewriteRules
    ( DebugAppliedRewriteRules
    )
import Kore.Log.DebugClaimState
    ( DebugClaimState
    )
import Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition
    )
import Kore.Log.DebugProven
    ( DebugProven
    )
import Kore.Log.DebugSolver
    ( DebugSolverRecv
    , DebugSolverSend
    )
import Kore.Log.DebugSubstitutionSimplifier
    ( DebugSubstitutionSimplifier
    )
import Kore.Log.DebugUnification
    ( DebugUnification
    )
import Kore.Log.ErrorBottomTotalFunction
    ( ErrorBottomTotalFunction
    )
import Kore.Log.ErrorDecidePredicateUnknown
    ( ErrorDecidePredicateUnknown
    )
import Kore.Log.ErrorException
    ( ErrorException
    )
import Kore.Log.ErrorParse
    ( ErrorParse
    )
import Kore.Log.ErrorRewriteLoop
    ( ErrorRewriteLoop
    )
import Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation
    )
import Kore.Log.ErrorRuleMergeDuplicate
    ( ErrorRuleMergeDuplicateIds
    , ErrorRuleMergeDuplicateLabels
    )
import Kore.Log.ErrorVerify
    ( ErrorVerify
    )
import Kore.Log.InfoAttemptUnification
    ( InfoAttemptUnification
    )
import Kore.Log.InfoExecBreadth
    ( InfoExecBreadth
    )
import Kore.Log.InfoExecDepth
    ( InfoExecDepth
    )
import Kore.Log.InfoProofDepth
    ( InfoProofDepth
    )
import Kore.Log.InfoReachability
    ( InfoReachability
    )
import Kore.Log.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators
    )
import Kore.Log.WarnIfLowProductivity
    ( WarnIfLowProductivity
    )
import Kore.Log.WarnRetrySolverQuery
    ( WarnRetrySolverQuery
    )
import Kore.Log.WarnStuckClaimState
    ( WarnStuckClaimState
    )
import Kore.Log.WarnSymbolSMTRepresentation
    ( WarnSymbolSMTRepresentation
    )
import Kore.Log.WarnTrivialClaim
    ( WarnTrivialClaim
    )
import Log
    ( Entry (..)
    , LogMessage
    , SomeEntry (..)
    )
import qualified Pretty

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
    let textToType = (Map.fromList . map register) entryTypeReps
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

entryTypeReps :: [SomeTypeRep]
entryHelpDocs :: [Pretty.Doc ()]
(entryTypeReps, entryHelpDocs) =
    unzip
    [ mk $ Proxy @DebugSolverSend
    , mk $ Proxy @DebugSolverRecv
    , mk $ Proxy @DebugClaimState
    , mk $ Proxy @DebugAppliedRewriteRules
    , mk $ Proxy @DebugSubstitutionSimplifier
    , mk $ Proxy @ErrorBottomTotalFunction
    , mk $ Proxy @ErrorDecidePredicateUnknown
    , mk $ Proxy @ErrorParse
    , mk $ Proxy @ErrorVerify
    , mk $ Proxy @ErrorRuleMergeDuplicateIds
    , mk $ Proxy @ErrorRuleMergeDuplicateLabels
    , mk $ Proxy @WarnFunctionWithoutEvaluators
    , mk $ Proxy @WarnSymbolSMTRepresentation
    , mk $ Proxy @WarnStuckClaimState
    , mk $ Proxy @WarnIfLowProductivity
    , mk $ Proxy @WarnTrivialClaim
    , mk $ Proxy @WarnRetrySolverQuery
    , mk $ Proxy @DebugEvaluateCondition
    , mk $ Proxy @ErrorException
    , mk $ Proxy @ErrorRewriteLoop
    , mk $ Proxy @LogMessage
    , mk $ Proxy @InfoAttemptUnification
    , mk $ Proxy @InfoReachability
    , mk $ Proxy @InfoExecBreadth
    , mk $ Proxy @ErrorRewritesInstantiation
    , mk $ Proxy @DebugAttemptEquation
    , mk $ Proxy @DebugApplyEquation
    , mk $ Proxy @DebugUnification
    , mk $ Proxy @InfoProofDepth
    , mk $ Proxy @InfoExecDepth
    , mk $ Proxy @DebugProven
    ]
  where
    mk proxy =
        let tRep = someTypeRep proxy
        in  ( tRep
            , Pretty.hsep [Pretty.pretty (asText tRep <> ":"), helpDoc proxy]
            )

asText :: SomeTypeRep -> Text
asText = Text.pack . show

makeInverse
    :: Ord k2
    => Map k1 k2 -> Map k2 k1
makeInverse map' =
    Map.fromList
    $ swap
    <$> Map.toList map'

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

parseEntryType :: Ord e => Text -> Parser.Parsec e Text SomeTypeRep
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

getEntryTypesAsText :: [String]
getEntryTypesAsText = show <$> entryHelpDocs
