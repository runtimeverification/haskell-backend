{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Log.Registry (
    parseEntryType,
    toSomeEntryType,
    lookupTextFromTypeWithError,
    registry,
    typeToText,
    textToType,
    getEntryTypesAsText,
    getErrEntryTypesAsText,
    getNoErrEntryTypesAsText,
    typeOfSomeEntry,
    entryTypeRepsErr,
    entryTypeRepsNoErr,
    entryTypeReps,
) where

import Control.Lens (
    (%~),
 )
import Control.Lens qualified as Lens
import Data.Functor.Classes (
    eq2,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Proxy
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Kore.Equation.DebugEquation (
    DebugApplyEquation,
    DebugAttemptEquation,
 )
import Kore.Log.DebugAppliedRewriteRules (
    DebugAppliedRewriteRules,
 )
import Kore.Log.DebugBeginClaim (
    DebugBeginClaim,
 )
import Kore.Log.DebugEvaluateCondition (
    DebugEvaluateCondition,
 )
import Kore.Log.DebugProven (
    DebugProven,
 )
import Kore.Log.DebugRetrySolverQuery (
    DebugRetrySolverQuery,
 )
import Kore.Log.DebugSolver (
    DebugSolverRecv,
    DebugSolverSend,
 )
import Kore.Log.DebugSubstitutionSimplifier (
    DebugSubstitutionSimplifier,
 )
import Kore.Log.DebugTransition (
    DebugTransition,
 )
import Kore.Log.DebugUnification (
    DebugUnification,
 )
import Kore.Log.DebugUnifyBottom (
    DebugUnifyBottom,
 )
import Kore.Log.ErrorBottomTotalFunction (
    ErrorBottomTotalFunction,
 )
import Kore.Log.ErrorDecidePredicateUnknown (
    ErrorDecidePredicateUnknown,
 )
import Kore.Log.ErrorEquationRightFunction (
    ErrorEquationRightFunction,
 )
import Kore.Log.ErrorEquationsSameMatch (
    ErrorEquationsSameMatch,
 )
import Kore.Log.ErrorException (
    ErrorException,
 )
import Kore.Log.ErrorParse (
    ErrorParse,
 )
import Kore.Log.ErrorRewriteLoop (
    ErrorRewriteLoop,
 )
import Kore.Log.ErrorRewritesInstantiation (
    ErrorRewritesInstantiation,
 )
import Kore.Log.ErrorVerify (
    ErrorVerify,
 )
import Kore.Log.InfoAttemptUnification (
    InfoAttemptUnification,
 )
import Kore.Log.InfoExecBreadth (
    InfoExecBreadth,
 )
import Kore.Log.InfoExecDepth (
    InfoExecDepth,
 )
import Kore.Log.InfoProofDepth (
    InfoProofDepth,
 )
import Kore.Log.InfoReachability (
    InfoReachability,
 )
import Kore.Log.WarnBoundedModelChecker (
    WarnBoundedModelChecker,
 )
import Kore.Log.WarnClaimRHSIsBottom (
    WarnClaimRHSIsBottom,
 )
import Kore.Log.WarnDepthLimitExceeded (
    WarnDepthLimitExceeded,
 )
import Kore.Log.WarnFunctionWithoutEvaluators (
    WarnFunctionWithoutEvaluators,
 )
import Kore.Log.WarnIfLowProductivity (
    WarnIfLowProductivity,
 )
import Kore.Log.WarnRestartSolver (
    WarnRestartSolver,
 )
import Kore.Log.WarnStuckClaimState (
    WarnStuckClaimState,
 )
import Kore.Log.WarnSymbolSMTRepresentation (
    WarnSymbolSMTRepresentation,
 )
import Kore.Log.WarnTrivialClaim (
    WarnTrivialClaim,
 )
import Kore.Log.WarnUnsimplified (
    WarnUnsimplifiedCondition,
    WarnUnsimplifiedPredicate,
 )
import Log (
    Entry (..),
    LogMessage,
    SomeEntry (..),
 )
import Prelude.Kore
import Pretty qualified
import Text.Megaparsec qualified as Parser
import Type.Reflection (
    SomeTypeRep (..),
    someTypeRep,
    typeOf,
 )

data Registry = Registry
    { textToType :: !(Map Text SomeTypeRep)
    , typeToText :: !(Map SomeTypeRep Text)
    }

{- | A registry of log entry types and their textual representations.
 It is used for user input validation in kore-exec and kore-repl and
 for pretty printing information about log entries.
 When adding a new entry type you should register it here.
-}
registry :: Registry
registry =
    let textToType =
            (Map.fromList . map register) entryTypeReps
        typeToText = makeInverse textToType
     in if textToType `eq2` makeInverse typeToText
            then Registry{textToType, typeToText}
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
entryTypeReps = entryTypeRepsErr <> entryTypeRepsNoErr

entryTypeRepsErr, entryTypeRepsNoErr :: [SomeTypeRep]
entryHelpDocsErr, entryHelpDocsNoErr :: [Pretty.Doc ()]
( (entryTypeRepsNoErr, entryHelpDocsNoErr)
    , (entryTypeRepsErr, entryHelpDocsErr)
    ) =
        (
            [ mk $ Proxy @DebugSolverSend
            , mk $ Proxy @DebugSolverRecv
            , mk $ Proxy @DebugTransition
            , mk $ Proxy @DebugAppliedRewriteRules
            , mk $ Proxy @DebugSubstitutionSimplifier
            , mk $ Proxy @WarnFunctionWithoutEvaluators
            , mk $ Proxy @WarnSymbolSMTRepresentation
            , mk $ Proxy @WarnStuckClaimState
            , mk $ Proxy @WarnDepthLimitExceeded
            , mk $ Proxy @WarnBoundedModelChecker
            , mk $ Proxy @WarnClaimRHSIsBottom
            , mk $ Proxy @WarnIfLowProductivity
            , mk $ Proxy @WarnTrivialClaim
            , mk $ Proxy @DebugRetrySolverQuery
            , mk $ Proxy @DebugUnifyBottom
            , mk $ Proxy @DebugEvaluateCondition
            , mk $ Proxy @LogMessage
            , mk $ Proxy @InfoAttemptUnification
            , mk $ Proxy @InfoReachability
            , mk $ Proxy @InfoExecBreadth
            , mk $ Proxy @DebugAttemptEquation
            , mk $ Proxy @DebugApplyEquation
            , mk $ Proxy @DebugUnification
            , mk $ Proxy @InfoProofDepth
            , mk $ Proxy @InfoExecDepth
            , mk $ Proxy @DebugBeginClaim
            , mk $ Proxy @DebugProven
            , mk $ Proxy @WarnUnsimplifiedPredicate
            , mk $ Proxy @WarnUnsimplifiedCondition
            , mk $ Proxy @WarnRestartSolver
            ]
        ,
            [ mk $ Proxy @ErrorBottomTotalFunction
            , mk $ Proxy @ErrorDecidePredicateUnknown
            , mk $ Proxy @ErrorEquationRightFunction
            , mk $ Proxy @ErrorEquationsSameMatch
            , mk $ Proxy @ErrorParse
            , mk $ Proxy @ErrorVerify
            , mk $ Proxy @ErrorException
            , mk $ Proxy @ErrorRewriteLoop
            , mk $ Proxy @ErrorRewritesInstantiation
            ]
        )
            & Lens.each %~ unzip
      where
        mk proxy =
            let tRep = someTypeRep proxy
             in ( tRep
                , Pretty.hsep [Pretty.pretty (asText tRep <> ":"), helpDoc proxy]
                )

asText :: SomeTypeRep -> Text
asText = Text.pack . show

makeInverse ::
    Ord k2 =>
    Map k1 k2 ->
    Map k2 k1
makeInverse map' =
    Map.fromList $
        swap
            <$> Map.toList map'

lookupTextFromTypeWithError :: SomeTypeRep -> Text
lookupTextFromTypeWithError type' =
    fromMaybe notFoundError $
        Map.lookup type' (typeToText registry)
  where
    ~notFoundError =
        error $
            "Tried to log nonexistent entry type: "
                <> show type'
                <> " It should be added to Kore.Log.Registry.registry."

parseEntryType :: Ord e => Text -> Parser.Parsec e Text SomeTypeRep
parseEntryType entryText =
    maybe empty return $
        Map.lookup entryText (textToType registry)

toSomeEntryType :: Entry entry => entry -> SomeTypeRep
toSomeEntryType =
    SomeTypeRep . typeOf

-- | The entry type underlying the 'SomeEntry' wrapper.
typeOfSomeEntry :: SomeEntry -> SomeTypeRep
typeOfSomeEntry (SomeEntry entry) = SomeTypeRep (typeOf entry)

getEntryTypesAsText :: [String]
getEntryTypesAsText = getNoErrEntryTypesAsText <> getErrEntryTypesAsText

getErrEntryTypesAsText :: [String]
getErrEntryTypesAsText = show <$> entryHelpDocsErr

getNoErrEntryTypesAsText :: [String]
getNoErrEntryTypesAsText = show <$> entryHelpDocsNoErr
