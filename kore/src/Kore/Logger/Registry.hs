{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.Registry
    ( registry
    ) where

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
import Type.Reflection
    ( SomeTypeRep
    , someTypeRep
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

    register :: SomeTypeRep -> (Text, SomeTypeRep)
    register type' =
        (asText type', type')
    asText :: SomeTypeRep -> Text
    asText = Text.pack . show
