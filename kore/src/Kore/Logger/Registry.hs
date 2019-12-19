{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.Registry
    ( parseEntryType
    , toSomeEntryType
    , lookupTextFromTypeWithError
    , registry
    , typeToText
    , textToType
    -- entry types
    , debugAppliedRuleType
    , debugAxiomEvaluationType
    , debugSolverSendType
    , debugSolverRecvType
    , warnBottomHookType
    , warnFunctionWithoutEvaluatorsType
    , warnSimplificationWithRemainderType
    ) where

import Control.Applicative
    ( empty
    )
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

import Kore.Logger
    ( Entry
    )
import Kore.Logger.DebugAppliedRule
    ( DebugAppliedRule
    )
import Kore.Logger.DebugAxiomEvaluation
    ( DebugAxiomEvaluation
    )
import Kore.Logger.DebugSolver
    ( DebugSolverRecv
    , DebugSolverSend
    )
import Kore.Logger.WarnBottomHook
    ( WarnBottomHook
    )
import Kore.Logger.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators
    )
import Kore.Logger.WarnSimplificationWithRemainder
    ( WarnSimplificationWithRemainder
    )

data Registry =
    Registry
    { textToType :: Map Text SomeTypeRep
    , typeToText :: Map SomeTypeRep Text
    }

registry :: Registry
registry =
    let textToType =
            Map.fromList
                [ register debugAppliedRuleType
                , register debugAxiomEvaluationType
                , register debugSolverSendType
                , register debugSolverRecvType
                , register warnBottomHookType
                , register warnFunctionWithoutEvaluatorsType
                , register warnSimplificationWithRemainderType
                ]
        typeToText = makeInverse textToType
    in if textToType `eq2` makeInverse typeToText
          then Registry { textToType, typeToText }
          else error "TODO error message"
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
  , warnBottomHookType
  , warnFunctionWithoutEvaluatorsType
  , warnSimplificationWithRemainderType
  :: SomeTypeRep

debugAppliedRuleType =
    someTypeRep (Proxy :: Proxy DebugAppliedRule)
debugAxiomEvaluationType =
    someTypeRep (Proxy :: Proxy DebugAxiomEvaluation)
debugSolverSendType =
    someTypeRep (Proxy :: Proxy DebugSolverSend)
debugSolverRecvType =
    someTypeRep (Proxy :: Proxy DebugSolverRecv)
warnBottomHookType =
    someTypeRep (Proxy :: Proxy WarnBottomHook)
warnFunctionWithoutEvaluatorsType =
    someTypeRep (Proxy :: Proxy WarnFunctionWithoutEvaluators)
warnSimplificationWithRemainderType =
    someTypeRep (Proxy :: Proxy WarnSimplificationWithRemainder)

lookupTextFromTypeWithError :: SomeTypeRep -> Text
lookupTextFromTypeWithError type' =
    maybe notFoundError id
    $ Map.lookup type' (typeToText registry)
  where
    notFoundError =
        error "Tried to log nonexistent entry type."

parseEntryType :: Text -> Parser.Parsec String String SomeTypeRep
parseEntryType entryText =
    maybe empty return
    $ Map.lookup entryText (textToType registry)

toSomeEntryType :: Entry entry => entry -> SomeTypeRep
toSomeEntryType =
    SomeTypeRep . typeOf
