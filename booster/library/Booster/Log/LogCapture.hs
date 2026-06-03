{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Booster-side per-request log capture for the @haskell-logging@
JSON-RPC flag.

Provides a tee combinator and a capture 'Logger' so a request handler
can fan its logs into a per-request 'Collector' on top of the regular
stderr/file logger.  Capture is purely additive; the existing logger
keeps writing exactly what it would have anyway.

Which messages are captured is decided per request by the set of
context names carried on the request (see 'Booster.JsonRpc' /
@Proxy.withHaskellLoggingCapture@); a message matches if any context in
its stack has a requested name (via 'clContextName', so id-carrying
contexts like @CtxRewrite@ match by tag).  Names this engine does not
recognise (e.g. kore entry-type names) simply never match here.
-}
module Booster.Log.LogCapture (
    boosterCaptureLogger,
    teeLogger,
    withBoosterCapture,
) where

import Control.Monad (when)
import Data.Aeson (Value, object, toJSON, (.=))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import Booster.Log (LogMessage (..), Logger (..), LoggerMIO (..), toJSONLog)
import Kore.JsonRpc.Types.ContextLog (clContextName)
import Kore.JsonRpc.Types.LogCapture (Collector, appendCollector)

{- | A 'Logger' that writes matching 'LogMessage's as JSON 'Value's
into the given 'Collector'.  A message matches when any context in its
stack has one of the requested names.  Compose with the existing logger
via 'teeLogger' to enable capture without losing stderr/file output.
-}
boosterCaptureLogger :: Set Text -> Collector -> Logger LogMessage
boosterCaptureLogger names collector =
    Logger $ \msg@(LogMessage _ ctxts _) ->
        when (any ((`Set.member` names) . clContextName) ctxts) $
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
as a tee onto the existing logger.  When 'Nothing' this is the
identity.  Otherwise the carried context-name set selects which
messages are captured.  The original logger continues to receive every
message; capture is purely additive.
-}
withBoosterCapture :: LoggerMIO m => Maybe (Collector, Set Text) -> m a -> m a
withBoosterCapture Nothing = id
withBoosterCapture (Just (collector, names)) =
    withLogger (`teeLogger` boosterCaptureLogger names collector)
