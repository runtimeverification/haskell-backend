{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Kore-side per-request log capture for the @haskell-logging: true@
JSON-RPC flag.

The 'koreCaptureLogAction' returns a 'LogAction' that fans entries
matching the bundled set (@DebugAttemptEquation@, @DebugApplyEquation@,
@DebugTerm@) into a 'Collector'.  The collector is owned by the proxy
for the lifetime of a single request and is drained when constructing
the response.  Filtering here is independent of any CLI @-l@ filter so
the capture is non-lossy regardless of server-startup verbosity.
-}
module Kore.Log.LogCapture (
    KoreCaptureRegistry,
    newKoreCaptureRegistry,
    koreCaptureLogAction,
    registryLogAction,
    withKoreCapture,
    haskellLoggingBundleKoreTypes,
) where

import Control.Concurrent (ThreadId, myThreadId)
import Control.Concurrent.STM (TVar, atomically, modifyTVar', newTVarIO, readTVar)
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

{- | The three kore-side entry types pyk's 'HASKELL_LOGGING_ENTRIES'
@SimplifyKore@ bundle resolves to.  Looked up against the registry
so a typo or removal would surface as a missing-entry diagnostic at
module load.
-}
haskellLoggingBundleKoreTypes :: Set SomeTypeRep
haskellLoggingBundleKoreTypes =
    Set.fromList $ map lookupOrFail bundleNames
  where
    bundleNames :: [Text]
    bundleNames = ["DebugAttemptEquation", "DebugApplyEquation", "DebugTerm"]
    lookupOrFail name =
        case Map.lookup name (textToType registry) of
            Just t -> t
            Nothing ->
                error $
                    "Kore.Log.LogCapture: bundle entry " <> show name <> " not in registry."

{- | A 'LogAction' that writes matching entries (filtered by
'haskellLoggingBundleKoreTypes') as JSON 'Value's into the given
'Collector'.  Combine with the engine's existing log action via
the 'Semigroup' instance of 'LogAction' (fan-out).
-}
koreCaptureLogAction :: MonadIO m => Collector -> LogAction m SomeEntry
koreCaptureLogAction collector =
    LogAction $ \entry ->
        liftIO $
            when (typeOfSomeEntry entry `Set.member` haskellLoggingBundleKoreTypes) $
                appendCollector collector (entryToJsonValue Nothing entry)

----------------------------------------------------------------------
-- Per-request capture registry, keyed by the OS thread that owns the
-- request.  The proxy's main log action is augmented once at server
-- startup with 'registryLogAction'; each request that opts in
-- registers its own 'Collector' against its 'ThreadId' so concurrent
-- requests do not see each other's logs.
----------------------------------------------------------------------

newtype KoreCaptureRegistry = KoreCaptureRegistry (TVar (Map ThreadId Collector))

newKoreCaptureRegistry :: IO KoreCaptureRegistry
newKoreCaptureRegistry = KoreCaptureRegistry <$> newTVarIO Map.empty

{- | A 'LogAction' that dispatches matching kore entries to whichever
'Collector' is registered for the calling thread, if any.  Combined
with the static kore log action via 'mconcat' so capture is purely
additive.
-}
registryLogAction :: MonadIO m => KoreCaptureRegistry -> LogAction m SomeEntry
registryLogAction (KoreCaptureRegistry tv) =
    LogAction $ \entry -> liftIO $ do
        tid <- myThreadId
        m <- atomically (readTVar tv)
        case Map.lookup tid m of
            Nothing -> pure ()
            Just c ->
                when (typeOfSomeEntry entry `Set.member` haskellLoggingBundleKoreTypes) $
                    appendCollector c (entryToJsonValue Nothing entry)

{- | Register a collector against the current thread for the duration
of the inner action.  Existing registrations on the same thread
(rare but possible if a request is re-entered) are restored on
exit.  When the collector argument is 'Nothing' the inner action
runs unchanged.
-}
withKoreCapture :: KoreCaptureRegistry -> Maybe Collector -> IO a -> IO a
withKoreCapture _ Nothing action = action
withKoreCapture (KoreCaptureRegistry tv) (Just collector) action = do
    tid <- myThreadId
    bracket_
        (atomically $ modifyTVar' tv (Map.insert tid collector))
        (atomically $ modifyTVar' tv (Map.delete tid))
        action
