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
import Control.Monad.IO.Class (liftIO)
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
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy (toStrict)
import Network.JSONRPC
import System.Clock (Clock (Monotonic), TimeSpec, diffTimeSpec, getTime, toNanoSecs)

import Booster.Definition.Base (KoreDefinition)
import Booster.JsonRpc as Booster (ServerState (..), execStateToKoreJson, toExecState)
import Booster.JsonRpc.Utils
import Booster.Log
import Booster.Syntax.Json.Internalise
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.Internal.TermLike (TermLike, VariableName)
import Kore.JsonRpc qualified as Kore (ServerState)
import Kore.JsonRpc.Types
import Kore.JsonRpc.Types qualified as ExecuteRequest (ExecuteRequest (..))
import Kore.JsonRpc.Types qualified as SimplifyRequest (SimplifyRequest (..))
import Kore.JsonRpc.Types.Log qualified as RPCLog
import Kore.Log qualified
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
    , simplifyBeforeFallback :: Bool
    , customLogLevels :: ![Log.LogLevel]
    }

serverError :: String -> Value -> ErrorObj
serverError detail = ErrorObj ("Server error: " <> detail) (-32032)

respondEither ::
    forall m.
    Booster.Log.LoggerMIO m =>
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
                        { logSuccessfulRewrites = execReq.logSuccessfulRewrites
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
                    handleExecute logSettings def start execReq
    Implies ImpliesRequest{assumeDefined}
        | fromMaybe False assumeDefined -> do
            -- try the booster end-point first
            (boosterResult, boosterTime) <- Stats.timed $ booster req
            case boosterResult of
                res@Right{} -> do
                    logStats ImpliesM (boosterTime, 0)
                    pure res
                Left err -> do
                    Booster.Log.withContext CtxProxy $
                        Booster.Log.logMessage' $
                            Text.pack $
                                "implies error in booster: " <> fromError err
                    (koreRes, koreTime) <- Stats.timed $ kore req
                    logStats ImpliesM (boosterTime + koreTime, koreTime)
                    pure koreRes
        | otherwise -> do
            (koreRes, koreTime) <- Stats.timed $ kore req
            logStats ImpliesM (koreTime, koreTime)
            pure koreRes
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
                    Booster.Log.withContext CtxProxy $
                        Booster.Log.logMessage' $
                            Text.pack $
                                "get-model error in booster: " <> fromError err
                    Stats.timed $ kore req
                Right (GetModel res@GetModelResult{})
                    -- re-check with legacy-kore if result is unknown
                    | Unknown <- res.satisfiable -> do
                        Booster.Log.withContext CtxProxy $
                            Booster.Log.withContext CtxAbort $
                                Booster.Log.logMessage $
                                    Text.pack "Re-checking a get-model result Unknown"
                        r@(kResult, _) <- Stats.timed $ kore req
                        Booster.Log.withContext CtxProxy $
                            Booster.Log.withContext CtxAbort $
                                Booster.Log.logMessage $
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
                                }
                (koreResult, koreTime) <- Stats.timed $ kore koreReq
                case koreResult of
                    Right (Simplify koreRes) -> do
                        logStats SimplifyM (boosterTime + koreTime, koreTime)
                        when (koreRes.state /= boosterRes.state) $ do
                            bState <- liftIO (MVar.readMVar boosterState)

                            Booster.Log.withContext CtxProxy $
                                Booster.Log.withContext CtxAbort $
                                    Booster.Log.withContext CtxDetail $
                                        Booster.Log.logMessage $
                                            let m = fromMaybe bState.defaultMain simplifyReq._module
                                                def =
                                                    fromMaybe (error $ "Module " <> show m <> " not found") $
                                                        Map.lookup m bState.definitions
                                                diff =
                                                    fromMaybe "<syntactic difference only>" $
                                                        diffBy def boosterRes.state.term koreRes.state.term
                                             in Text.pack ("Kore simplification: Diff (< before - > after)\n" <> diff)
                        stop <- liftIO $ getTime Monotonic
                        let timing
                                | Just start <- mbStart
                                , fromMaybe False simplifyReq.logTiming =
                                    Just
                                        [ RPCLog.ProcessingTime
                                            Nothing
                                            (fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9)
                                        ]
                                | otherwise = Nothing
                        -- NOTE: we do not include simplification logs into the response
                        pure . Right . Simplify $
                            SimplifyResult
                                { state = koreRes.state
                                , logs =
                                    postProcessLogs
                                        <$> combineLogs
                                            [ timing
                                            , boosterRes.logs
                                            , koreRes.logs
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

                Booster.Log.withContext CtxProxy $
                    Booster.Log.logMessage' $
                        Text.unwords
                            ["Problem with simplify request: ", Text.pack getErrMsg, "-", boosterError]
                -- NB the timing information for booster execution is lost here.
                loggedKore SimplifyM req
            _wrong ->
                pure . Left $ ErrorObj "Wrong result type" (-32002) $ toJSON _wrong

    loggedKore method r = do
        Booster.Log.withContext CtxProxy $
            Booster.Log.logMessage' $
                Text.pack $
                    show method <> " (using kore)"
        (result, time) <- Stats.timed $ kore r
        logStats method (time, time)
        pure result

    logStats method (time, koreTime)
        | Just v <- statsVar = do
            addStats v method time koreTime
            Booster.Log.withContext CtxProxy $
                Booster.Log.logMessage' $
                    Text.pack $
                        unwords
                            [ "Performed"
                            , show method
                            , "in"
                            , microsWithUnit time
                            , "(" <> microsWithUnit koreTime <> " kore time)"
                            ]
        | otherwise =
            pure ()

    handleExecute ::
        LogSettings ->
        KoreDefinition ->
        TimeSpec ->
        ExecuteRequest ->
        m (Either ErrorObj (API 'Res))
    handleExecute logSettings def start execReq = do
        execRes <- executionLoop logSettings def (0, 0.0, 0.0, Nothing) execReq
        if (fromMaybe False logSettings.logTiming)
            then traverse (addTimeLog start) execRes
            else pure execRes

    addTimeLog :: TimeSpec -> API 'Res -> m (API 'Res)
    addTimeLog start res = do
        stop <- liftIO (getTime Monotonic)
        let duration = fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9
        pure $ case res of
            Execute result ->
                let result' :: ExecuteResult
                    result' =
                        result
                            { reason = result.reason
                            , logs = combineLogs [Just [RPCLog.ProcessingTime Nothing duration], result.logs]
                            }
                 in Execute result'
            other -> other

    postProcessLogs :: [RPCLog.LogEntry] -> [RPCLog.LogEntry]
    postProcessLogs !logs = map RPCLog.logEntryEraseTerms logs

    executionLoop ::
        LogSettings ->
        KoreDefinition ->
        (Depth, Double, Double, Maybe [RPCLog.LogEntry]) ->
        ExecuteRequest ->
        m (Either ErrorObj (API 'Res))
    executionLoop logSettings def (currentDepth@(Depth cDepth), !time, !koreTime, !rpcLogs) r = do
        Booster.Log.withContext CtxProxy $
            Booster.Log.logMessage $
                Text.pack $
                    if currentDepth == 0
                        then "Starting execute request"
                        else "Iterating execute request at " <> show currentDepth
        -- calculate depth limit, considering possible forced Kore simplification
        let mbDepthLimit = case (cfg.forceFallback, r.maxDepth) of
                (Just (Depth forceDepth), Just (Depth maxDepth))
                    | cDepth + forceDepth < maxDepth ->
                        cfg.forceFallback
                    | otherwise ->
                        Just $ Depth $ maxDepth - cDepth
                (Just forceDepth, _) -> Just forceDepth
                (_, Just maxDepth) -> Just $ maxDepth - currentDepth
                _ -> Nothing
        (bResult, bTime) <- Stats.timed $ booster (Execute r{maxDepth = mbDepthLimit})
        case bResult of
            Right (Execute boosterResult)
                -- the execution reached the depth bound due to a forced Kore simplification
                | DepthBound <- boosterResult.reason
                , Just forceDepth <- cfg.forceFallback
                , forceDepth == boosterResult.depth -> do
                    Booster.Log.withContext CtxProxy $
                        Booster.Log.logMessage $
                            Text.pack $
                                "Forced simplification at " <> show (currentDepth + boosterResult.depth)
                    simplifyResult <- simplifyExecuteState logSettings r._module def boosterResult.state
                    case simplifyResult of
                        Left logsOnly -> do
                            -- state was simplified to \bottom, return vacuous
                            Booster.Log.withContext CtxProxy $
                                Booster.Log.logMessage $
                                    Text.pack "Vacuous state after simplification"
                            pure . Right . Execute $
                                makeVacuous
                                    ( postProcessLogs
                                        <$> logsOnly
                                    )
                                    boosterResult
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
                                , postProcessLogs
                                    <$> accumulatedLogs
                                )
                                r{ExecuteRequest.state = execStateToKoreJson simplifiedBoosterState}
                -- if we stop for a reason in fallbackReasons (default [Aborted, Stuck, Branching],
                -- revert to the old backend to re-confirm and possibly proceed
                | boosterResult.reason `elem` cfg.fallbackReasons -> do
                    Booster.Log.withContext CtxProxy $
                        Booster.Log.logMessage $
                            Text.pack $
                                "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    -- simplify Booster's state with Kore's simplifier
                    Booster.Log.withContext CtxProxy $
                        Booster.Log.logMessage ("Simplifying booster state and falling back to Kore" :: Text)
                    simplifyResult <-
                        if cfg.simplifyBeforeFallback
                            then simplifyExecuteState logSettings r._module def boosterResult.state
                            else pure $ Right (boosterResult.state, Nothing)
                    case simplifyResult of
                        Left logsOnly -> do
                            -- state was simplified to \bottom, return vacuous
                            Booster.Log.withContext CtxProxy $
                                Booster.Log.logMessage $
                                    Text.pack "Vacuous state after simplification"
                            pure . Right . Execute $ makeVacuous (postProcessLogs <$> logsOnly) boosterResult
                        Right (simplifiedBoosterState, boosterStateSimplificationLogs) -> do
                            -- attempt to do one step in the old backend
                            Booster.Log.withContext CtxProxy $
                                Booster.Log.logMessage ("Executing fall-back request" :: Text)
                            (kResult, kTime) <-
                                Stats.timed $
                                    kore
                                        ( Execute
                                            r
                                                { state = execStateToKoreJson simplifiedBoosterState
                                                , maxDepth = Just $ Depth 1
                                                , assumeStateDefined = Just True
                                                }
                                        )
                            when (isJust statsVar) $ do
                                Booster.Log.withContext CtxProxy $
                                    Booster.Log.logMessage $
                                        Text.pack $
                                            "Kore fall-back in " <> microsWithUnit kTime
                            case kResult of
                                Right (Execute koreResult) -> do
                                    let
                                        fallbackLog =
                                            if fromMaybe False logSettings.logFallbacks
                                                then Just [mkFallbackLogEntry boosterResult koreResult]
                                                else Nothing
                                        accumulatedLogs =
                                            combineLogs
                                                [ rpcLogs
                                                , boosterResult.logs
                                                , boosterStateSimplificationLogs
                                                , koreResult.logs
                                                , fallbackLog
                                                ]
                                        loopState newLogs =
                                            ( currentDepth + boosterResult.depth + koreResult.depth
                                            , time + bTime + kTime
                                            , koreTime + kTime
                                            , postProcessLogs
                                                <$> combineLogs (accumulatedLogs : newLogs)
                                            )
                                        continueWith newLogs nextState =
                                            executionLoop
                                                logSettings
                                                def
                                                (loopState newLogs)
                                                r{ExecuteRequest.state = nextState}
                                    case (boosterResult.reason, koreResult.reason) of
                                        (Aborted, res) ->
                                            Booster.Log.withContext CtxProxy $
                                                Booster.Log.withContext CtxAbort $
                                                    Booster.Log.logMessage $
                                                        "Booster aborted, kore yields " <> Text.pack (show res)
                                        (bRes, kRes)
                                            | bRes /= kRes ->
                                                Booster.Log.withContext CtxProxy $
                                                    Booster.Log.withContext CtxAbort $
                                                        Booster.Log.logMessage $
                                                            "Booster and kore disagree: " <> Text.pack (show (bRes, kRes))
                                            | otherwise ->
                                                Booster.Log.withContext CtxProxy $
                                                    Booster.Log.withContext CtxAbort $
                                                        Booster.Log.logMessage $
                                                            "kore confirms result " <> Text.pack (show bRes)

                                    case koreResult.reason of
                                        DepthBound -> do
                                            -- if we made one step, add the number of
                                            -- steps we have taken to the counter and
                                            -- attempt with booster again
                                            when (koreResult.depth == 0) $ error "Expected kore-rpc to take at least one step"
                                            Booster.Log.withContext CtxProxy $
                                                Booster.Log.logMessage $
                                                    Text.pack $
                                                        "kore depth-bound, continuing... (currently at "
                                                            <> show (currentDepth + boosterResult.depth + koreResult.depth)
                                                            <> ")"
                                            continueWith [] (execStateToKoreJson koreResult.state)
                                        _ -> do
                                            -- otherwise we have hit a different
                                            -- HaltReason, at which point we should
                                            -- return, setting the correct depth
                                            Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                                                "Kore " <> show koreResult.reason <> " at " <> show koreResult.depth
                                            -- perform post-exec simplification.
                                            -- NB This has been found to make a difference,
                                            -- even for results produced by legacy-kore.
                                            postExecResult <-
                                                simplifyExecResult logSettings r._module def koreResult

                                            case postExecResult of
                                                Left (nextState, newLogs) -> do
                                                    -- simplification revealed that we should actually proceed
                                                    continueWith newLogs nextState
                                                Right result -> do
                                                    logStats ExecuteM (time + bTime + kTime, koreTime + kTime)
                                                    pure $
                                                        Right $
                                                            Execute
                                                                result
                                                                    { depth = currentDepth + boosterResult.depth + koreResult.depth
                                                                    , logs =
                                                                        postProcessLogs
                                                                            <$> combineLogs
                                                                                [ rpcLogs
                                                                                , boosterResult.logs
                                                                                , map RPCLog.logEntryEraseTerms <$> result.logs
                                                                                , fallbackLog
                                                                                ]
                                                                    }
                                -- can only be an error at this point
                                res -> pure res
                | otherwise -> do
                    -- we were successful with the booster, thus we
                    -- return the booster result with the updated
                    -- depth, in case we previously looped
                    Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    -- perform post-exec simplification
                    postExecResult <-
                        simplifyExecResult logSettings r._module def boosterResult
                    case postExecResult of
                        Left (nextState, newLogs) ->
                            executionLoop
                                logSettings
                                def
                                ( currentDepth + boosterResult.depth
                                , time + bTime
                                , koreTime
                                , postProcessLogs <$> combineLogs (rpcLogs : boosterResult.logs : newLogs)
                                )
                                r{ExecuteRequest.state = nextState}
                        Right result -> do
                            logStats ExecuteM (time + bTime, koreTime)
                            pure . Right $
                                Execute
                                    result
                                        { depth = currentDepth + boosterResult.depth
                                        , logs = postProcessLogs <$> combineLogs [rpcLogs, result.logs]
                                        }
            -- can only be an error at this point
            res -> pure res

    -- Performs an internal simplify call for the given execute state.
    -- If the state simplifies to bottom, only the logs are returned,
    -- otherwise the logs and the simplified state (after splitting it
    -- into term and predicates by an internal trivial execute call).
    --
    -- Only the timing logs will be returned (if requested by the top-level).
    simplifyExecuteState ::
        LogSettings ->
        Maybe Text ->
        KoreDefinition ->
        ExecuteState ->
        m (Either (Maybe [RPCLog.LogEntry]) (ExecuteState, Maybe [RPCLog.LogEntry]))
    simplifyExecuteState
        LogSettings{logTiming}
        mbModule
        def
        s = do
            Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                "Simplifying execution state"
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
                                -- put back the ruleId, ruleSubstitution and rulePredicate that was originally passed to simplifyExecuteState
                                -- this ensures the information from next states in a branch reponse doesn't get lost
                                pure $
                                    Right
                                        ( (Booster.toExecState p sub unsup Nothing)
                                            { ruleId = s.ruleId
                                            , ruleSubstitution = s.ruleSubstitution
                                            , rulePredicate = s.rulePredicate
                                            }
                                        , simplified.logs
                                        )
                            Left err -> do
                                Booster.Log.withContext CtxProxy . Booster.Log.logMessage $
                                    "Error processing execute state simplification result: "
                                        <> Text.pack (show err)
                                pure $ Right (s, Nothing)
                _other -> do
                    -- if we hit an error here, return the original
                    Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                        "Unexpected failure when calling Kore simplifier, returning original term"
                    pure $ Right (s, Nothing)
          where
            toSimplifyRequest :: ExecuteState -> SimplifyRequest
            toSimplifyRequest state =
                SimplifyRequest
                    { state = execStateToKoreJson state
                    , _module = mbModule
                    , logTiming
                    }

    -- used for post-exec simplification returns either a state to
    -- continue execution from, with associated simplification logs
    -- (only new logs), or a simplified result with combined logs
    simplifyExecResult ::
        LogSettings ->
        Maybe Text ->
        KoreDefinition ->
        ExecuteResult ->
        m (Either (KoreJson.KoreJson, [Maybe [RPCLog.LogEntry]]) ExecuteResult)
    simplifyExecResult logSettings mbModule def res@ExecuteResult{reason, state, nextStates}
        | not cfg.simplifyAtEnd = pure $ Right res
        | otherwise = do
            Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                "Simplifying state in " <> show reason <> " result"
            simplified <- simplifyExecuteState logSettings mbModule def state
            case simplified of
                Left logsOnly -> do
                    -- state simplified to \bottom, return vacuous
                    Booster.Log.withContext CtxProxy . Booster.Log.logMessage . Text.pack $
                        "Vacuous after simplifying result state"
                    pure . Right $ makeVacuous logsOnly res
                Right (simplifiedState, simplifiedStateLogs) -> do
                    simplifiedNexts <-
                        maybe
                            (pure [])
                            (mapM $ simplifyExecuteState logSettings mbModule def)
                            nextStates
                    let (logsOnly, (filteredNexts, filteredNextLogs)) =
                            second unzip $ partitionEithers simplifiedNexts
                        newLogs = simplifiedStateLogs : logsOnly <> filteredNextLogs

                    pure $ case reason of
                        Branching
                            | null filteredNexts ->
                                Right
                                    res
                                        { reason = Stuck
                                        , nextStates = Nothing
                                        , logs = combineLogs $ res.logs : simplifiedStateLogs : logsOnly
                                        }
                            | length filteredNexts == 1 ->
                                -- all but one next states are bottom, execution should proceed
                                Left (execStateToKoreJson $ head filteredNexts, logsOnly <> filteredNextLogs)
                        -- otherwise falling through to _otherReason
                        CutPointRule
                            | null filteredNexts ->
                                Right $ makeVacuous (combineLogs $ res.logs : newLogs) res
                        _otherReason ->
                            Right $
                                res
                                    { state = simplifiedState
                                    , nextStates =
                                        if null filteredNexts
                                            then Nothing
                                            else Just filteredNexts
                                    , logs = combineLogs $ res.logs : newLogs
                                    }

data LogSettings = LogSettings
    { logSuccessfulRewrites :: Maybe Bool
    , logFailedRewrites :: Maybe Bool
    , logFallbacks :: Maybe Bool
    , logTiming :: Maybe Bool
    }

-- | Combine multiple, possibly empty/non-existent (Nothing) lists of logs into one
combineLogs :: [Maybe [RPCLog.LogEntry]] -> Maybe [RPCLog.LogEntry]
combineLogs logSources
    | all isNothing logSources = Nothing
    | otherwise = Just $ concat $ catMaybes logSources

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
