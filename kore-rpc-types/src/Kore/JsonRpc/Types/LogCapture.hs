{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Per-request log capture for the `haskell-logging` JSON-RPC flag.

A 'Collector' is a thread-safe buffer of 'LogLine's, one per matching
log entry.  The booster-side and kore-side log paths each carry their
own predicate and build a 'LogLine' (defined in 'ContextLog', the same
structured type the context log uses); both write into the same
'Collector', so the proxy can drain a single buffer at response time
and attach the entries to the response's @haskell-log-entries@ field.

The buffer is unbounded: the design requires lossless capture for any
request that opts in.  Memory growth is proportional to the volume of
matched entries during a single request and is released when the
'Collector' is dropped at response time.
-}
module Kore.JsonRpc.Types.LogCapture (
    Collector,
    newCollector,
    appendCollector,
    drainCollector,
) where

import Control.Concurrent.STM (TVar, atomically, modifyTVar', newTVarIO, readTVar, writeTVar)
import Data.Foldable (toList)
import Data.Sequence (Seq, (|>))
import Data.Sequence qualified as Seq

import Kore.JsonRpc.Types.ContextLog (LogLine)

{- | A per-request buffer for captured log entries, each built as a
structured 'LogLine' by the engine-specific capture path.
-}
newtype Collector = Collector (TVar (Seq LogLine))

newCollector :: IO Collector
newCollector = Collector <$> newTVarIO Seq.empty

{- | Append a single captured entry to the buffer.  Non-blocking; safe to
call concurrently from any thread.
-}
appendCollector :: Collector -> LogLine -> IO ()
appendCollector (Collector tv) l = atomically $ modifyTVar' tv (|> l)

{- | Drain the buffer and reset it to empty.  Returns entries in
insertion order.
-}
drainCollector :: Collector -> IO [LogLine]
drainCollector (Collector tv) = atomically $ do
    s <- readTVar tv
    writeTVar tv Seq.empty
    pure (toList s)
