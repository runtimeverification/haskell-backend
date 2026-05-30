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
    koreCaptureLogAction,
    haskellLoggingBundleKoreTypes,
) where

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

-- | The three kore-side entry types pyk's 'HASKELL_LOGGING_ENTRIES'
-- @SimplifyKore@ bundle resolves to.  Looked up against the registry
-- so a typo or removal would surface as a missing-entry diagnostic at
-- module load.
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

-- | A 'LogAction' that writes matching entries (filtered by
-- 'haskellLoggingBundleKoreTypes') as JSON 'Value's into the given
-- 'Collector'.  Combine with the engine's existing log action via
-- the 'Semigroup' instance of 'LogAction' (fan-out).
koreCaptureLogAction :: MonadIO m => Collector -> LogAction m SomeEntry
koreCaptureLogAction collector =
    LogAction $ \entry -> liftIO $
        when (typeOfSomeEntry entry `Set.member` haskellLoggingBundleKoreTypes) $
            appendCollector collector (entryToJsonValue Nothing entry)
