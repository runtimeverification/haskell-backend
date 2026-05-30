{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Booster-side per-request log capture for the @haskell-logging: true@
JSON-RPC flag.

Provides a tee combinator and a capture 'Logger' so a request handler
can fan its logs into a per-request 'Collector' on top of the regular
stderr/file logger.  Capture is purely additive; the existing logger
keeps writing exactly what it would have anyway.
-}
module Booster.Log.LogCapture (
    boosterCaptureLogger,
    teeLogger,
    withBoosterCapture,
    haskellLoggingBundleBoosterContexts,
) where

import Control.Monad (when)
import Data.Aeson (Value, object, toJSON, (.=))
import Data.Set (Set)
import Data.Set qualified as Set

import Booster.Log (LogMessage (..), Logger (..), LoggerMIO (..), toJSONLog)
import Kore.JsonRpc.Types.ContextLog (CLContext (..), SimpleContext (..))
import Kore.JsonRpc.Types.LogCapture (Collector, appendCollector)

{- | The four booster-side context tags the @haskell-logging@ bundle
captures.  An entry matches if any of its contexts is one of these
(pyk's parser keys off the presence of the context string, not on
exact context-stack equality).
-}
haskellLoggingBundleBoosterContexts :: Set CLContext
haskellLoggingBundleBoosterContexts =
    Set.fromList
        [ CLNullary CtxProxy
        , CLNullary CtxDetail
        , CLNullary CtxAbort
        , CLNullary CtxSimplify
        ]

{- | A 'Logger' that writes matching 'LogMessage's as JSON 'Value's
into the given 'Collector'.  Compose with the existing logger via
'teeLogger' to enable capture without losing stderr/file output.
-}
boosterCaptureLogger :: Collector -> Logger LogMessage
boosterCaptureLogger collector =
    Logger $ \msg@(LogMessage _ ctxts _) ->
        when (any (`Set.member` haskellLoggingBundleBoosterContexts) ctxts) $
            appendCollector collector (renderLogMessage msg)

renderLogMessage :: LogMessage -> Value
renderLogMessage (LogMessage _ ctxts msg) =
    object
        [ "context" .= toJSON (map toJSONLog ctxts)
        , "message" .= toJSONLog msg
        ]

{- | Run two loggers on every message.  Order is left-then-right; both
run unconditionally.
-}
teeLogger :: Logger LogMessage -> Logger LogMessage -> Logger LogMessage
teeLogger (Logger l1) (Logger l2) =
    Logger $ \m -> l1 m >> l2 m

{- | Run a 'LoggerMIO' action with the booster-side capture installed
as a tee onto the existing logger.  When the collector is 'Nothing'
this is the identity.  The original logger continues to receive
every message; capture is purely additive.
-}
withBoosterCapture :: LoggerMIO m => Maybe Collector -> m a -> m a
withBoosterCapture Nothing = id
withBoosterCapture (Just collector) =
    withLogger (`teeLogger` boosterCaptureLogger collector)
