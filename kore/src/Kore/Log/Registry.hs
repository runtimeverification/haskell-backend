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
import Data.Tuple
    ( swap
    )
import qualified Text.Megaparsec as Parser
import Type.Reflection
    ( SomeTypeRep (..)
    , someTypeRep
    , typeOf
    )

import Kore.Equation.Application
    ( DebugAttemptEquation
    , DebugEquationApplied
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
import Kore.Log.WarnDecidePredicateUnknown
    ( WarnDecidePredicateUnknown
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
entryTypeReps =
    [ someTypeRep $ Proxy @DebugAppliedRule
    , someTypeRep $ Proxy @DebugAxiomEvaluation
    , someTypeRep $ Proxy @DebugSolverSend
    , someTypeRep $ Proxy @DebugSolverRecv
    , someTypeRep $ Proxy @DebugProofState
    , someTypeRep $ Proxy @DebugAppliedRewriteRules
    , someTypeRep $ Proxy @WarnBottomHook
    , someTypeRep $ Proxy @WarnDecidePredicateUnknown
    , someTypeRep $ Proxy @WarnFunctionWithoutEvaluators
    , someTypeRep $ Proxy @DebugSkipSimplification
    , someTypeRep $ Proxy @DebugEvaluateCondition
    , someTypeRep $ Proxy @ErrorException
    , someTypeRep $ Proxy @LogMessage
    , someTypeRep $ Proxy @InfoAttemptUnification
    , someTypeRep $ Proxy @InfoReachability
    , someTypeRep $ Proxy @ErrorRewritesInstantiation
    , someTypeRep $ Proxy @DebugAttemptEquation
    , someTypeRep $ Proxy @DebugEquationApplied
    ]

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
