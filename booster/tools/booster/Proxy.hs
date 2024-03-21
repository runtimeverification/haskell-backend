{-# LANGUAGE RankNTypes #-}

{- |
Module      : Proxy
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Proxy (
    KoreServer (..),
    ProxyConfig (..),
    serverError,
    respondEither,
) where

import Control.Concurrent.MVar qualified as MVar
import Control.Monad (when)
import Control.Monad.Catch (MonadCatch (..), catch)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger qualified as Log
import Control.Monad.Trans.Except (runExcept)
import Data.Aeson (ToJSON (..))
import Data.Aeson.KeyMap qualified as Aeson
import Data.Aeson.Text (encodeToLazyText)
import Data.Aeson.Types (Value (..))
import Data.Bifunctor (second)
import Data.Either (partitionEithers)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy (toStrict)
import Network.JSONRPC
import System.Clock (Clock (Monotonic), TimeSpec, diffTimeSpec, getTime, toNanoSecs)

import Booster.Definition.Base (KoreDefinition)
import Booster.JsonRpc as Booster (ServerState (..), execStateToKoreJson, toExecState)
import Booster.JsonRpc.Utils (diffBy)
import Booster.Syntax.Json.Internalise
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.Internal.TermLike (TermLike, VariableName)
import Kore.JsonRpc qualified as Kore (ServerState)
import Kore.JsonRpc.Types
import Kore.JsonRpc.Types qualified as ExecuteRequest (ExecuteRequest (..))
import Kore.JsonRpc.Types qualified as ImpliesRequest (ImpliesRequest (..))
import Kore.JsonRpc.Types qualified as SimplifyRequest (SimplifyRequest (..))
import Kore.JsonRpc.Types.Log qualified as RPCLog
import Kore.Log qualified
import Kore.Log.DecidePredicateUnknown (DecidePredicateUnknown, externaliseDecidePredicateUnknown)
import Kore.Syntax.Definition (SentenceAxiom)
import Kore.Syntax.Json.Types qualified as KoreJson
import SMT qualified
import Stats (StatsVar, addStats, microsWithUnit, timed)

data KoreServer = KoreServer
    { serverState :: MVar.MVar Kore.ServerState
    , mainModule :: Text
    , runSMT ::
        forall a.
        SmtMetadataTools StepperAttributes ->
        [SentenceAxiom (TermLike VariableName)] ->
        SMT.SMT a ->
        IO a
    , loggerEnv :: Kore.Log.LoggerEnv IO
    }

data ProxyConfig = ProxyConfig
    { statsVar :: Maybe StatsVar
    , forceFallback :: Maybe Depth
    , boosterState :: MVar.MVar Booster.ServerState
    , fallbackReasons :: [HaltReason]
    , simplifyAtEnd :: Bool
    , customLogLevels :: ![Log.LogLevel]
    }

serverError :: String -> Value -> ErrorObj
serverError detail = ErrorObj ("Server error: " <> detail) (-32032)

respondEither ::
    forall m.
    Log.MonadLogger m =>
    (MonadIO m, MonadCatch m) =>
    ProxyConfig ->
    Respond (API 'Req) m (API 'Res) ->
    Respond (API 'Req) m (API 'Res) ->
    Respond (API 'Req) m (API 'Res)
respondEither cfg@ProxyConfig{statsVar, boosterState} booster kore req = case req of
    Execute execReq
        | isJust execReq.stepTimeout || isJust execReq.movingAverageStepTimeout ->
            loggedKore ExecuteM req
        | otherwise ->
            let logSettings =
                    LogSettings
                        { logSuccessfulSimplifications = execReq.logSuccessfulSimplifications
                        , logFailedSimplifications = execReq.logFailedSimplifications
                        , logSuccessfulRewrites = execReq.logSuccessfulRewrites
                        , logFailedRewrites = execReq.logFailedRewrites
                        , logFallbacks = execReq.logFallbacks
                        , logTiming = execReq.logTiming
                        }
             in liftIO (getTime Monotonic) >>= \start -> do
                    bState <- liftIO $ MVar.readMVar boosterState
                    let m = fromMaybe bState.defaultMain execReq._module
                        def =
                            fromMaybe (error $ "Module " <> show m <> " not found") $
                                Map.lookup m bState.definitions
                    handleExecute logSettings def execReq
                        >>= traverse (postExecSimplify logSettings start execReq._module def)
    Implies impliesReq -> do
        koreResult <-
            loggedKore
                ImpliesM
                ( Implies
                    impliesReq
                        { ImpliesRequest.logSuccessfulSimplifications =
                            Just $ Log.LevelOther "SimplifyJson" `elem` cfg.customLogLevels
                        }
                )
        case koreResult of
            Right (Implies koreRes) -> do
                -- Kore may have produced simplification logs during rewriting. If so,
                -- output them Kore at "SimplifyJson" level. Erase terms from the traces.
                when (isJust koreRes.logs) $ do
                    outputLogsAtLevel (Log.LevelOther "SimplifyJson")
                        . map RPCLog.logEntryEraseTerms
                        . fromJust
                        $ koreRes.logs
            _ -> pure ()
        pure koreResult
    Simplify simplifyReq ->
        liftIO (getTime Monotonic) >>= handleSimplify simplifyReq . Just
    AddModule _ -> do
        -- execute in booster first, assuming that kore won't throw an
        -- error if booster did not. The response is empty anyway.
        (boosterResult, boosterTime) <- Stats.timed $ booster req
        case boosterResult of
            Left _err -> pure boosterResult
            Right _ -> do
                (koreRes, koreTime) <- Stats.timed $ kore req
                logStats AddModuleM (boosterTime + koreTime, koreTime)
                pure koreRes
    GetModel _ -> do
        -- try the booster end-point first
        (bResult, bTime) <- Stats.timed $ booster req
        (result, kTime) <-
            case bResult of
                Left err -> do
                    Log.logErrorNS "proxy" . Text.pack $
                        "get-model error in booster: " <> fromError err
                    Stats.timed $ kore req
                Right (GetModel res@GetModelResult{})
                    -- re-check with legacy-kore if result is unknown
                    | Unknown <- res.satisfiable -> do
                        Log.logOtherNS "proxy" (Log.LevelOther "Aborts") "Re-checking a get-model result Unknown"
                        r@(kResult, _) <- Stats.timed $ kore req
                        Log.logOtherNS "proxy" (Log.LevelOther "Aborts") $
                            "Double-check returned " <> toStrict (encodeToLazyText kResult)
                        pure r
                    -- keep other results
                    | otherwise ->
                        pure (bResult, 0)
                other ->
                    error $ "Unexpected get-model result " <> show other
        logStats GetModelM (bTime + kTime, kTime)
        pure result
    Cancel ->
        pure $ Left $ ErrorObj "Cancel not supported" (-32601) Null
  where
    handleSimplify :: SimplifyRequest -> Maybe TimeSpec -> m (Either ErrorObj (API 'Res))
    handleSimplify simplifyReq mbStart = do
        -- execute in booster first, then in kore. Log the difference
        (boosterResult, boosterTime) <-
            Stats.timed $ booster (Simplify simplifyReq)
        case boosterResult of
            Right (Simplify boosterRes) -> do
                let koreReq =
                        Simplify
                            simplifyReq
                                { SimplifyRequest.state = boosterRes.state
                                , SimplifyRequest.logSuccessfulSimplifications =
                                    Just $ Log.LevelOther "SimplifyJson" `elem` cfg.customLogLevels
                                }
                (koreResult, koreTime) <- Stats.timed $ kore koreReq
                case koreResult of
                    Right (Simplify koreRes) -> do
                        logStats SimplifyM (boosterTime + koreTime, koreTime)
                        when (koreRes.state /= boosterRes.state) $ do
                            bState <- liftIO (MVar.readMVar boosterState)
                            Log.logOtherNS "proxy" (Log.LevelOther "Aborts") $
                                let m = fromMaybe bState.defaultMain simplifyReq._module
                                    def =
                                        fromMaybe (error $ "Module " <> show m <> " not found") $
                                            Map.lookup m bState.definitions
                                    diff =
                                        fromMaybe "<syntactic difference only>" $
                                            diffBy def boosterRes.state.term koreRes.state.term
                                 in Text.pack ("Kore simplification: Diff (< before - > after)\n" <> diff)
                        stop <- liftIO $ getTime Monotonic
                        -- output simplification traces returned by Kore at "SimplifyJson" level, effectively
                        -- appending them to Booster's traces. Erase terms from the traces.
                        when (isJust koreRes.logs) $ do
                            outputLogsAtLevel (Log.LevelOther "SimplifyJson")
                                . map RPCLog.logEntryEraseTerms
                                . fromJust
                                $ koreRes.logs
                        let timing
                                | Just start <- mbStart
                                , fromMaybe False simplifyReq.logTiming =
                                    Just
                                        [ RPCLog.ProcessingTime
                                            Nothing
                                            (fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9)
                                        ]
                                | otherwise = Nothing
                        pure . Right . Simplify $
                            SimplifyResult
                                { state = koreRes.state
                                , logs =
                                    combineLogs
                                        [ timing
                                        , boosterRes.logs
                                        , map RPCLog.logEntryEraseTerms <$> koreRes.logs
                                        ]
                                }
                    koreError ->
                        -- can only be an error
                        pure koreError
            Left ErrorObj{getErrMsg, getErrData} -> do
                -- in case of problems, log the problem and try with kore
                let boosterError
                        | Object errObj <- getErrData
                        , Just err <- Aeson.lookup "error" errObj =
                            fromString err
                        | otherwise = fromString getErrData
                    fromString (String s) = s
                    fromString other = Text.pack (show other)
                Log.logWarnNS "proxy" . Text.unwords $
                    ["Problem with simplify request: ", Text.pack getErrMsg, "-", boosterError]
                -- NB the timing information for booster execution is lost here.
                loggedKore SimplifyM req
            _wrong ->
                pure . Left $ ErrorObj "Wrong result type" (-32002) $ toJSON _wrong

    loggedKore method r = do
        Log.logInfoNS "proxy" . Text.pack $ show method <> " (using kore)"
        (result, time) <- Stats.timed $ kore r
        logStats method (time, time)
        pure result

    logStats method (time, koreTime)
        | Just v <- statsVar = do
            addStats v method time koreTime
            Log.logInfoNS "proxy" . Text.pack . unwords $
                [ "Performed"
                , show method
                , "in"
                , microsWithUnit time
                , "(" <> microsWithUnit koreTime <> " kore time)"
                ]
        | otherwise =
            pure ()

    handleExecute :: LogSettings -> KoreDefinition -> ExecuteRequest -> m (Either ErrorObj (API 'Res))
    handleExecute logSettings def =
        executionLoop logSettings def (0, 0.0, 0.0, Nothing)

    executionLoop ::
        LogSettings ->
        KoreDefinition ->
        (Depth, Double, Double, Maybe [RPCLog.LogEntry]) ->
        ExecuteRequest ->
        m (Either ErrorObj (API 'Res))
    executionLoop logSettings def (currentDepth@(Depth cDepth), !time, !koreTime, !rpcLogs) r = do
        Log.logInfoNS "proxy" . Text.pack $
            if currentDepth == 0
                then "Starting execute request"
                else "Iterating execute request at " <> show currentDepth
        -- calculate depth limit, considering possible forced Kore simplification
        let mbDepthLimit = case (cfg.forceFallback, r.maxDepth) of
                (Just (Depth forceDepth), Just (Depth maxDepth)) ->
                    if cDepth + forceDepth < maxDepth
                        then Just $ Depth forceDepth
                        else Just $ Depth $ maxDepth - cDepth
                (Just forceDepth, _) -> Just forceDepth
                (_, Just maxDepth) -> Just $ maxDepth - currentDepth
                _ -> Nothing
        (bResult, bTime) <- Stats.timed $ booster (Execute r{maxDepth = mbDepthLimit})
        case bResult of
            Right (Execute boosterResult)
                -- the execution reached the depth bound due to a forced Kore simplification
                | boosterResult.reason == DepthBound && isJust cfg.forceFallback -> do
                    Log.logInfoNS "proxy" . Text.pack $
                        "Forced simplification at " <> show (currentDepth + boosterResult.depth)
                    simplifyResult <- simplifyExecuteState logSettings r._module def boosterResult.state
                    case simplifyResult of
                        Left logsOnly -> do
                            -- state was simplified to \bottom, return vacuous
                            Log.logInfoNS "proxy" "Vacuous state after simplification"
                            pure . Right . Execute $ makeVacuous logsOnly boosterResult
                        Right (simplifiedBoosterState, boosterStateSimplificationLogs) -> do
                            let accumulatedLogs =
                                    combineLogs
                                        [ rpcLogs
                                        , boosterResult.logs
                                        , boosterStateSimplificationLogs
                                        ]
                            executionLoop
                                logSettings
                                def
                                ( currentDepth + boosterResult.depth
                                , time + bTime
                                , koreTime
                                , accumulatedLogs
                                )
                                r{ExecuteRequest.state = execStateToKoreJson simplifiedBoosterState}
                -- if we stop for a reason in fallbackReasons (default [Aborted, Stuck, Branching],
                -- revert to the old backend to re-confirm and possibly proceed
                | boosterResult.reason `elem` cfg.fallbackReasons -> do
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    -- simplify Booster's state with Kore's simplifier
                    Log.logInfoNS "proxy" . Text.pack $ "Simplifying booster state and falling back to Kore "
                    simplifyResult <- simplifyExecuteState logSettings r._module def boosterResult.state
                    case simplifyResult of
                        Left logsOnly -> do
                            -- state was simplified to \bottom, return vacuous
                            Log.logInfoNS "proxy" "Vacuous state after simplification"
                            pure . Right . Execute $ makeVacuous logsOnly boosterResult
                        Right (simplifiedBoosterState, boosterStateSimplificationLogs) -> do
                            -- attempt to do one step in the old backend
                            (kResult, kTime) <-
                                Stats.timed $
                                    kore
                                        ( Execute
                                            r
                                                { state = execStateToKoreJson simplifiedBoosterState
                                                , maxDepth = Just $ Depth 1
                                                , assumeStateDefined = Just True
                                                , ExecuteRequest.logSuccessfulSimplifications =
                                                    Just $ Log.LevelOther "SimplifyJson" `elem` cfg.customLogLevels
                                                }
                                        )
                            when (isJust statsVar) $ do
                                Log.logInfoNS "proxy" . Text.pack $
                                    "Kore fall-back in " <> microsWithUnit kTime
                            case kResult of
                                Right (Execute koreResult) -> do
                                    let
                                        fallbackLog =
                                            if fromMaybe False logSettings.logFallbacks
                                                then Just [mkFallbackLogEntry boosterResult koreResult]
                                                else Nothing
                                    case (boosterResult.reason, koreResult.reason) of
                                        (Aborted, res) ->
                                            Log.logOtherNS "proxy" (Log.LevelOther "Aborts") $
                                                "Booster aborted, kore yields " <> Text.pack (show res)
                                        (bRes, kRes)
                                            | bRes /= kRes ->
                                                Log.logOtherNS "proxy" (Log.LevelOther "Aborts") $
                                                    "Booster and kore disagree: " <> Text.pack (show (bRes, kRes))
                                            | otherwise ->
                                                Log.logOtherNS "proxy" (Log.LevelOther "Aborts") $
                                                    "kore confirms result " <> Text.pack (show bRes)

                                    -- Kore may have produced simplification logs during rewriting. If so,
                                    -- output them Kore at "SimplifyJson" level, effectively
                                    -- appending them to Booster's traces. Erase terms from the traces.
                                    when (isJust koreResult.logs) $ do
                                        outputLogsAtLevel (Log.LevelOther "SimplifyJson")
                                            . map RPCLog.logEntryEraseTerms
                                            . filter isSimplificationLogEntry
                                            . fromJust
                                            $ koreResult.logs

                                    case koreResult.reason of
                                        DepthBound -> do
                                            -- if we made one step, add the number of
                                            -- steps we have taken to the counter and
                                            -- attempt with booster again
                                            when (koreResult.depth == 0) $ error "Expected kore-rpc to take at least one step"
                                            Log.logInfoNS "proxy" $
                                                Text.pack $
                                                    "kore depth-bound, continuing... (currently at "
                                                        <> show (currentDepth + boosterResult.depth + koreResult.depth)
                                                        <> ")"
                                            let accumulatedLogs =
                                                    combineLogs
                                                        [ rpcLogs
                                                        , boosterResult.logs
                                                        , boosterStateSimplificationLogs
                                                        , map RPCLog.logEntryEraseTerms <$> koreResult.logs
                                                        , fallbackLog
                                                        ]
                                            executionLoop
                                                logSettings
                                                def
                                                ( currentDepth + boosterResult.depth + koreResult.depth
                                                , time + bTime + kTime
                                                , koreTime + kTime
                                                , accumulatedLogs
                                                )
                                                r{ExecuteRequest.state = execStateToKoreJson koreResult.state}
                                        _ -> do
                                            -- otherwise we have hit a different
                                            -- HaltReason, at which point we should
                                            -- return, setting the correct depth
                                            Log.logInfoNS "proxy" . Text.pack $
                                                "Kore " <> show koreResult.reason <> " at " <> show koreResult.depth
                                            logStats ExecuteM (time + bTime + kTime, koreTime + kTime)
                                            pure $
                                                Right $
                                                    Execute
                                                        koreResult
                                                            { depth = currentDepth + boosterResult.depth + koreResult.depth
                                                            , logs =
                                                                combineLogs
                                                                    [ rpcLogs
                                                                    , boosterResult.logs
                                                                    , koreResult.logs
                                                                    , fallbackLog
                                                                    ]
                                                            }
                                -- can only be an error at this point
                                res -> pure res
                | otherwise -> do
                    -- we were successful with the booster, thus we
                    -- return the booster result with the updated
                    -- depth, in case we previously looped
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    logStats ExecuteM (time + bTime, koreTime)
                    pure $
                        Right $
                            Execute
                                boosterResult
                                    { depth = currentDepth + boosterResult.depth
                                    , logs = combineLogs [rpcLogs, boosterResult.logs]
                                    }
            -- can only be an error at this point
            res -> pure res

    -- Performs an internal simplify call for the given execute state.
    -- If the state simplifies to bottom, only the logs are returned,
    -- otherwise the logs and the simplified state (after splitting it
    -- into term and predicates by an internal trivial execute call).
    simplifyExecuteState ::
        LogSettings ->
        Maybe Text ->
        KoreDefinition ->
        ExecuteState ->
        m (Either (Maybe [RPCLog.LogEntry]) (ExecuteState, Maybe [RPCLog.LogEntry]))
    simplifyExecuteState
        LogSettings{logSuccessfulSimplifications, logFailedSimplifications, logTiming}
        mbModule
        def
        s = do
            Log.logInfoNS "proxy" "Simplifying execution state"
            simplResult <-
                handleSimplify (toSimplifyRequest s) Nothing
            case simplResult of
                -- This request should not fail, as the only possible
                -- failure mode would be malformed or invalid kore
                Right (Simplify simplified)
                    | KoreJson.KJBottom _ <- simplified.state.term ->
                        pure (Left simplified.logs)
                    | otherwise -> do
                        -- convert back to a term/constraints form by re-internalising
                        let internalPattern =
                                runExcept $
                                    internalisePattern
                                        DisallowAlias
                                        IgnoreSubsorts
                                        Nothing
                                        def
                                        simplified.state.term
                        case internalPattern of
                            Right (p, sub, unsup) ->
                                pure $ Right (Booster.toExecState p sub unsup, simplified.logs)
                            Left err -> do
                                Log.logWarnNS "proxy" $
                                    "Error processing execute state simplification result: "
                                        <> Text.pack (show err)
                                pure $ Right (s, Nothing)
                _other -> do
                    -- if we hit an error here, return the original
                    Log.logWarnNS "proxy" "Unexpected failure when calling Kore simplifier, returning original term"
                    pure $ Right (s, Nothing)
          where
            toSimplifyRequest :: ExecuteState -> SimplifyRequest
            toSimplifyRequest state =
                SimplifyRequest
                    { state = execStateToKoreJson state
                    , _module = mbModule
                    , logSuccessfulSimplifications
                    , logFailedSimplifications
                    , logTiming
                    }

    postExecSimplify ::
        LogSettings -> TimeSpec -> Maybe Text -> KoreDefinition -> API 'Res -> m (API 'Res)
    postExecSimplify logSettings start mbModule def
        | not cfg.simplifyAtEnd = pure
        | otherwise = \case
            Execute res ->
                Execute
                    <$> ( simplifyResult res
                            `catch` ( \(err :: DecidePredicateUnknown) ->
                                        pure res{reason = Aborted, unknownPredicate = Just . externaliseDecidePredicateUnknown $ err}
                                    )
                        )
            other -> pure other
      where
        -- timeLog :: TimeDiff -> Maybe [LogEntry]
        timeLog stop
            | fromMaybe False logSettings.logTiming =
                let duration =
                        fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9
                 in Just [RPCLog.ProcessingTime Nothing duration]
            | otherwise =
                Nothing

        simplifyResult :: ExecuteResult -> m ExecuteResult
        simplifyResult res@ExecuteResult{reason, state, nextStates} = do
            Log.logInfoNS "proxy" . Text.pack $ "Simplifying state in " <> show reason <> " result"
            simplified <- simplifyExecuteState logSettings mbModule def state
            case simplified of
                Left logsOnly -> do
                    -- state simplified to \bottom, return vacuous
                    Log.logInfoNS "proxy" "Vacuous after simplifying result state"
                    stop <- liftIO $ getTime Monotonic
                    pure $ makeVacuous (combineLogs [timeLog stop, logsOnly]) res
                Right (simplifiedState, simplifiedStateLogs) -> do
                    simplifiedNexts <-
                        maybe
                            (pure [])
                            (mapM $ simplifyExecuteState logSettings mbModule def)
                            nextStates
                    stop <- liftIO $ getTime Monotonic
                    let (logsOnly, (filteredNexts, filteredNextLogs)) =
                            second unzip $ partitionEithers simplifiedNexts
                        newLogs = simplifiedStateLogs : logsOnly <> filteredNextLogs

                    pure $ case reason of
                        Branching
                            | null filteredNexts ->
                                res
                                    { reason = Stuck
                                    , nextStates = Nothing
                                    , logs = combineLogs $ timeLog stop : res.logs : simplifiedStateLogs : logsOnly
                                    }
                            | length filteredNexts == 1 ->
                                res -- What now? would have to re-loop. Return as-is.
                                -- otherwise falling through to _otherReason
                        CutPointRule
                            | null filteredNexts ->
                                makeVacuous (combineLogs $ timeLog stop : newLogs) res
                        _otherReason ->
                            res
                                { state = simplifiedState
                                , nextStates =
                                    if null filteredNexts
                                        then Nothing
                                        else Just filteredNexts
                                , logs = combineLogs $ timeLog stop : res.logs : newLogs
                                }

data LogSettings = LogSettings
    { logSuccessfulSimplifications :: Maybe Bool
    , logFailedSimplifications :: Maybe Bool
    , logSuccessfulRewrites :: Maybe Bool
    , logFailedRewrites :: Maybe Bool
    , logFallbacks :: Maybe Bool
    , logTiming :: Maybe Bool
    }

-- | Combine multiple, possibly empty/non-existent (Nothing) lists of logs into one
combineLogs :: [Maybe [RPCLog.LogEntry]] -> Maybe [RPCLog.LogEntry]
combineLogs logSources
    | all isNothing logSources = Nothing
    | otherwise = Just $ concat $ catMaybes logSources

-- | Log a list of RPCLog items at a certain level
outputLogsAtLevel :: Log.MonadLogger m => Log.LogLevel -> [RPCLog.LogEntry] -> m ()
outputLogsAtLevel level = mapM_ (Log.logOtherNS "proxy" level . RPCLog.encodeLogEntryText)

isSimplificationLogEntry :: RPCLog.LogEntry -> Bool
isSimplificationLogEntry = \case
    RPCLog.Simplification{} -> True
    _ -> False

makeVacuous :: Maybe [RPCLog.LogEntry] -> ExecuteResult -> ExecuteResult
makeVacuous newLogs execState =
    execState
        { reason = Vacuous
        , nextStates = Nothing
        , rule = Nothing
        , logs = combineLogs [execState.logs, newLogs]
        }

mkFallbackLogEntry :: ExecuteResult -> ExecuteResult -> RPCLog.LogEntry
mkFallbackLogEntry boosterResult koreResult =
    let boosterRewriteFailureLog = filter isRewriteFailureLogEntry . fromMaybe [] $ boosterResult.logs
        lastBoosterRewriteLogEntry = case boosterRewriteFailureLog of
            [] -> Nothing
            xs -> Just $ last xs
        fallbackRuleId =
            case lastBoosterRewriteLogEntry of
                Nothing -> "UNKNOWN"
                Just logEntry -> fromMaybe "UNKNOWN" $ getRewriteFailureRuleId logEntry
        fallbackReason =
            case lastBoosterRewriteLogEntry of
                Nothing -> "UNKNOWN"
                Just logEntry -> fromMaybe "UNKNOWN" $ getRewriteFailureReason logEntry
        koreRewriteSuccessLog = filter isRewriteSuccessLogEntry . fromMaybe [] $ koreResult.logs
        koreRuleIds = mapMaybe getRewriteSuccessRuleId koreRewriteSuccessLog
     in RPCLog.Fallback
            { originalTerm = Just $ execStateToKoreJson boosterResult.state
            , rewrittenTerm = Just $ execStateToKoreJson koreResult.state
            , reason = fallbackReason
            , fallbackRuleId = fallbackRuleId
            , recoveryRuleIds = NonEmpty.nonEmpty koreRuleIds
            , recoveryDepth = koreResult.depth
            , origin = RPCLog.Proxy
            }
  where
    isRewriteFailureLogEntry :: RPCLog.LogEntry -> Bool
    isRewriteFailureLogEntry = \case
        RPCLog.Rewrite{result = RPCLog.Failure{}} -> True
        _ -> False

    isRewriteSuccessLogEntry :: RPCLog.LogEntry -> Bool
    isRewriteSuccessLogEntry = \case
        RPCLog.Rewrite{result = RPCLog.Success{}} -> True
        _ -> False

    getRewriteFailureReason :: RPCLog.LogEntry -> Maybe Text
    getRewriteFailureReason = \case
        RPCLog.Rewrite{result = RPCLog.Failure{reason}} -> Just reason
        _ -> Nothing

    getRewriteFailureRuleId :: RPCLog.LogEntry -> Maybe Text
    getRewriteFailureRuleId = \case
        RPCLog.Rewrite{result = RPCLog.Failure{_ruleId}} -> _ruleId
        _ -> Nothing

    getRewriteSuccessRuleId :: RPCLog.LogEntry -> Maybe Text
    getRewriteSuccessRuleId = \case
        RPCLog.Rewrite{result = RPCLog.Success{ruleId}} -> Just ruleId
        _ -> Nothing
