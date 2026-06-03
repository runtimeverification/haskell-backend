{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Kore-side per-request log capture for the @haskell-logging@ JSON-RPC
flag.

A request carries the list of entry-type names to capture.  The proxy
turns the names this engine recognises into a 'Set' 'SomeTypeRep' (via
'koreTypesFromNames') and registers it, together with a 'Collector',
against the request's thread for the duration of the request.
'registryLogAction' — installed once at server startup, outside the
@-l@/@--log-entries@ filter — then fans every matching entry into that
collector.  Because it sits outside the CLI filter, capture is
independent of server-startup verbosity: the requested entries are
captured whether or not the server was started with @-l@ for them.
-}
module Kore.Log.LogCapture (
    KoreCaptureRegistry,
    newKoreCaptureRegistry,
    koreTypesFromNames,
    registryLogAction,
    withKoreCapture,
) where

import Control.Concurrent (ThreadId, myThreadId)
import Control.Concurrent.STM (TVar, atomically, modifyTVar', newTVarIO, readTVarIO)
import Control.Exception (bracket_)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Prelude.Kore
import Type.Reflection (SomeTypeRep)

import Kore.JsonRpc.Types.LogCapture (Collector, appendCollector)
import Kore.Log.BoosterAdaptor (entryToJsonValue)
import Kore.Log.Registry (registry, textToType, typeOfSomeEntry)
import Log (LogAction (..), SomeEntry)

{- | Resolve requested entry-type names to the kore 'SomeTypeRep's the
capture should match.  Names not in the log registry — booster context
tags, or entries this backend version does not know — are skipped, so a
client can request a superset spanning both engines (and across backend
versions) without failing the request.
-}
koreTypesFromNames :: [Text] -> Set SomeTypeRep
koreTypesFromNames names =
    Set.fromList $ mapMaybe (`Map.lookup` textToType registry) names

----------------------------------------------------------------------
-- Per-request capture registry, keyed by the OS thread that owns the
-- request.  The proxy's main log action is augmented once at server
-- startup with 'registryLogAction'; each request that opts in
-- registers its own 'Collector' (and the set of entry types it wants)
-- against its 'ThreadId' so concurrent requests do not see each
-- other's logs.
----------------------------------------------------------------------

newtype KoreCaptureRegistry = KoreCaptureRegistry (TVar (Map ThreadId (Collector, Set SomeTypeRep)))

newKoreCaptureRegistry :: IO KoreCaptureRegistry
newKoreCaptureRegistry = KoreCaptureRegistry <$> newTVarIO Map.empty

{- | A 'LogAction' that dispatches matching kore entries to whichever
'Collector' is registered for the calling thread, if any, filtered by
that request's requested entry-type set.  Combined with the static kore
log action via 'mconcat' so capture is purely additive.
-}
registryLogAction :: MonadIO m => KoreCaptureRegistry -> LogAction m SomeEntry
registryLogAction (KoreCaptureRegistry tv) =
    LogAction $ \entry -> liftIO $ do
        -- Runs for every kore entry (it is composed outside the -l filter).
        -- Most requests register nothing, so the thread lookup short-circuits.
        tid <- myThreadId
        m <- readTVarIO tv
        case Map.lookup tid m of
            Nothing -> pure ()
            Just (c, types)
                | typeOfSomeEntry entry `Set.member` types ->
                    appendCollector c (entryToJsonValue Nothing entry)
                | otherwise -> pure ()

{- | Register a collector and its requested entry-type set against the
current thread for the duration of the inner action.  Existing
registrations on the same thread (rare but possible if a request is
re-entered) are restored on exit.  When the argument is 'Nothing' the
inner action runs unchanged.
-}
withKoreCapture :: KoreCaptureRegistry -> Maybe (Collector, Set SomeTypeRep) -> IO a -> IO a
withKoreCapture _ Nothing action = action
withKoreCapture (KoreCaptureRegistry tv) (Just entry) action = do
    tid <- myThreadId
    bracket_
        (atomically $ modifyTVar' tv (Map.insert tid entry))
        (atomically $ modifyTVar' tv (Map.delete tid))
        action
