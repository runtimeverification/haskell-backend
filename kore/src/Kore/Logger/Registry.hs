{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.Registry
    ( lookupEntryWithError
    , parseEntryType
    , toSomeEntryType
    , isElemOfRegistry
    , registry
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
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
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

-- TODO: crash program if it logs a type which isn't here
registry :: Map Text SomeTypeRep
registry =
    Map.fromList
        [ register debugAppliedRuleType
        , register debugAxiomEvaluationType
        , register debugSolverSendType
        , register debugSolverRecvType
        , register warnBottomHookType
        , register warnFunctionWithoutEvaluatorsType
        , register warnSimplificationWithRemainderType
        ]
  where
    register :: SomeTypeRep -> (Text, SomeTypeRep)
    register type' =
        (asText type', type')
    asText :: SomeTypeRep -> Text
    asText = Text.pack . show

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

lookupEntryWithError :: Text -> SomeTypeRep
lookupEntryWithError entryText =
    maybe notFoundError id
    $ Map.lookup entryText registry
  where
    notFoundError =
        error "Tried to log nonexistent entry type."

parseEntryType :: Text -> Parser.Parsec String String SomeTypeRep
parseEntryType entryText =
    maybe empty return
    $ Map.lookup entryText registry

isElemOfRegistry :: Entry entry => entry -> Bool
isElemOfRegistry entry =
    toSomeEntryType entry `elem` Map.elems registry

toSomeEntryType :: Entry entry => entry -> SomeTypeRep
toSomeEntryType =
    SomeTypeRep . typeOf
