{-# LANGUAGE RankNTypes #-}

{- |
Module      : Proxy
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Proxy (
    KoreServer (..),
    serverError,
    respondEither,
) where

import Control.Concurrent.MVar qualified as MVar
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger qualified as Log
import Data.Aeson (ToJSON (..), encode)
import Data.Aeson.KeyMap qualified as Aeson
import Data.Aeson.Types (Value (..))
import Data.Bifunctor (second)
import Data.Either (partitionEithers)
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as Text
import Network.JSONRPC
import SMT qualified

import Booster.JsonRpc (execStateToKoreJson)
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

serverError :: String -> Value -> ErrorObj
serverError detail = ErrorObj ("Server error: " <> detail) (-32032)

respondEither ::
    forall m.
    Log.MonadLogger m =>
    MonadIO m =>
    Maybe StatsVar ->
    Respond (API 'Req) m (API 'Res) ->
    Respond (API 'Req) m (API 'Res) ->
    Respond (API 'Req) m (API 'Res)
respondEither mbStatsVar booster kore req = case req of
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
                        }
             in handleExecute logSettings execReq
                    >>= traverse (postExecSimplify logSettings execReq._module)
    Implies _ ->
        loggedKore ImpliesM req
    Simplify simplifyReq -> handleSimplify simplifyReq
    AddModule _ -> do
        -- execute in booster first, assuming that kore won't throw an
        -- error if booster did not. The response is empty anyway.
        (boosterResult, boosterTime) <- withTime $ booster req
        case boosterResult of
            Left _err -> pure boosterResult
            Right _ -> do
                (koreRes, koreTime) <- withTime $ kore req
                logStats AddModuleM (boosterTime + koreTime, koreTime)
                pure koreRes
    GetModel _ ->
        loggedKore GetModelM req
    Cancel ->
        pure $ Left $ ErrorObj "Cancel not supported" (-32601) Null
  where
    handleSimplify :: SimplifyRequest -> m (Either ErrorObj (API 'Res))
    handleSimplify simplifyReq = do
        -- execute in booster first, then in kore. Log the difference
        (boosterResult, boosterTime) <- withTime $ booster (Simplify simplifyReq)
        case boosterResult of
            Right (Simplify boosterRes) -> do
                let koreReq = Simplify simplifyReq{SimplifyRequest.state = boosterRes.state}
                (koreResult, koreTime) <- withTime $ kore koreReq
                case koreResult of
                    Right (Simplify koreRes) -> do
                        logStats SimplifyM (boosterTime + koreTime, koreTime)
                        when (koreRes.state /= boosterRes.state) $
                            -- TODO pretty instance for KoreJson terms for logging
                            Log.logOtherNS "proxy" (Log.LevelOther "Simplify") . Text.pack . unlines $
                                [ "Booster simplification:"
                                , show boosterRes.state
                                , "to"
                                , show koreRes.state
                                ]
                        pure . Right . Simplify $
                            SimplifyResult
                                { state = koreRes.state
                                , logs = combineLogs [boosterRes.logs, koreRes.logs]
                                }
                    koreError ->
                        -- can only be an error
                        pure koreError
            Left ErrorObj{getErrMsg, getErrData = Object errObj} -> do
                -- in case of problems, log the problem and try with kore
                let boosterError = maybe "???" fromString $ Aeson.lookup "error" errObj
                    fromString (String s) = s
                    fromString other = Text.pack (show other)
                Log.logInfoNS "proxy" . Text.unwords $
                    ["Problem with simplify request: ", Text.pack getErrMsg, "-", boosterError]
                loggedKore SimplifyM req
            _wrong ->
                pure . Left $ ErrorObj "Wrong result type" (-32002) $ toJSON _wrong

    loggedKore method r = do
        Log.logInfoNS "proxy" . Text.pack $ show method <> " (using kore)"
        (result, time) <- withTime $ kore r
        logStats method (time, time)
        pure result

    withTime = if isJust mbStatsVar then Stats.timed else fmap (,0.0)

    logStats method (time, koreTime)
        | Just v <- mbStatsVar = do
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

    handleExecute :: LogSettings -> ExecuteRequest -> m (Either ErrorObj (API 'Res))
    handleExecute logSettings = executionLoop logSettings (0, 0.0, 0.0, Nothing)

    executionLoop ::
        LogSettings ->
        (Depth, Double, Double, Maybe [RPCLog.LogEntry]) ->
        ExecuteRequest ->
        m (Either ErrorObj (API 'Res))
    executionLoop logSettings (!currentDepth, !time, !koreTime, !rpcLogs) r = do
        Log.logInfoNS "proxy" . Text.pack $
            if currentDepth == 0
                then "Starting execute request"
                else "Iterating execute request at " <> show currentDepth
        let mbDepthLimit = flip (-) currentDepth <$> r.maxDepth
        (bResult, bTime) <- withTime $ booster (Execute r{maxDepth = mbDepthLimit})
        case bResult of
            Right (Execute boosterResult)
                -- if the new backend aborts, branches or gets stuck, revert to the old one
                --
                -- if we are stuck in the new backend we try to re-run
                -- in the old one to work around any potential
                -- unification bugs.
                | boosterResult.reason `elem` [Aborted, Stuck, Branching] -> do
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    -- simplify Booster's state with Kore's simplifier
                    Log.logInfoNS "proxy" . Text.pack $ "Simplifying booster state and falling back to Kore "
                    simplifyResult <- simplifyExecuteState logSettings r._module boosterResult.state
                    case simplifyResult of
                        Left logsOnly -> do
                            -- state was simplified to \bottom, return vacuous
                            Log.logInfoNS "proxy" "Vacuous state after simplification"
                            pure . Right . Execute $ makeVacuous logsOnly boosterResult
                        Right (simplifiedBoosterState, boosterStateSimplificationLogs) -> do
                            -- attempt to do one step in the old backend
                            (kResult, kTime) <-
                                withTime $
                                    kore
                                        ( Execute
                                            r
                                                { state = execStateToKoreJson simplifiedBoosterState
                                                , maxDepth = Just $ Depth 1
                                                }
                                        )
                            when (isJust mbStatsVar) $
                                Log.logInfoNS "proxy" . Text.pack $
                                    "Kore fall-back in " <> microsWithUnit kTime
                            case kResult of
                                Right (Execute koreResult)
                                    | koreResult.reason == DepthBound -> do
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
                                                    , koreResult.logs
                                                    ]
                                        executionLoop
                                            logSettings
                                            ( currentDepth + boosterResult.depth + koreResult.depth
                                            , time + bTime + kTime
                                            , koreTime + kTime
                                            , accumulatedLogs
                                            )
                                            r{ExecuteRequest.state = execStateToKoreJson koreResult.state}
                                    | otherwise -> do
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
                                                        , logs = combineLogs [rpcLogs, boosterResult.logs, koreResult.logs]
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
        ExecuteState ->
        m (Either (Maybe [RPCLog.LogEntry]) (ExecuteState, Maybe [RPCLog.LogEntry]))
    simplifyExecuteState
        LogSettings{logSuccessfulSimplifications, logFailedSimplifications}
        mbModule
        s = do
            Log.logInfoNS "proxy" "Simplifying execution state"
            simplResult <-
                handleSimplify $ toSimplifyRequest s
            case simplResult of
                -- This request should not fail, as the only possible
                -- failure mode would be malformed or invalid kore
                Right (Simplify simplified)
                    | KoreJson.KJBottom _ <- simplified.state.term ->
                        pure (Left simplified.logs)
                    | otherwise -> do
                        -- to convert back to a term/constraints form,
                        -- we run a trivial execute request (in booster)
                        -- We cannot call the booster internaliser without access to the server state
                        -- This call would fail for a \bottom state
                        let request =
                                (emptyExecuteRequest simplified.state)
                                    { _module = mbModule
                                    , maxDepth = Just $ Depth 0
                                    }
                        Log.logInfoNS "proxy" "Making 0-step execute request to convert back to a term/constraints form"
                        result <- booster $ Execute request
                        case result of
                            Right (Execute ExecuteResult{state = finalState}) ->
                                -- return state converted by Booster and logs from simplification.
                                -- The 0-step execute result won't have logs (no logs are requested)
                                pure $ Right (finalState, simplified.logs)
                            other -> do
                                Log.logWarnNS "proxy" $
                                    "Error in pseudo-execute step after simplification: "
                                        <> either (Text.pack . show) (Text.pack . show . encode) other
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
                    }

            emptyExecuteRequest :: KoreJson.KoreJson -> ExecuteRequest
            emptyExecuteRequest state =
                ExecuteRequest
                    { state
                    , maxDepth = Nothing
                    , _module = Nothing
                    , cutPointRules = Nothing
                    , terminalRules = Nothing
                    , movingAverageStepTimeout = Nothing
                    , stepTimeout = Nothing
                    , logSuccessfulSimplifications = Nothing
                    , logFailedSimplifications = Nothing
                    , logSuccessfulRewrites = Nothing
                    , logFailedRewrites = Nothing
                    }

    postExecSimplify ::
        LogSettings -> Maybe Text -> API 'Res -> m (API 'Res)
    postExecSimplify logSettings mbModule = \case
        Execute res -> Execute <$> simplifyResult res
        other -> pure other
      where
        simplifyResult :: ExecuteResult -> m ExecuteResult
        simplifyResult res@ExecuteResult{reason, state, nextStates} = do
            Log.logInfoNS "proxy" . Text.pack $ "Simplifying state in " <> show reason <> " result"
            simplified <- simplifyExecuteState logSettings mbModule state

            case simplified of
                Left logsOnly -> do
                    -- state simplified to \bottom, return vacuous
                    Log.logInfoNS "proxy" "Vacuous after simplifying result state"
                    pure $ makeVacuous logsOnly res
                Right (simplifiedState, simplifiedStateLogs) -> do
                    simplifiedNexts <-
                        maybe
                            (pure [])
                            (mapM $ simplifyExecuteState logSettings mbModule)
                            nextStates
                    let (logsOnly, (filteredNexts, filteredNextLogs)) =
                            second unzip $ partitionEithers simplifiedNexts
                        newLogs = simplifiedStateLogs : logsOnly <> filteredNextLogs

                    pure $ case reason of
                        Branching
                            | null filteredNexts ->
                                res
                                    { reason = Stuck
                                    , nextStates = Nothing
                                    , logs = combineLogs $ res.logs : simplifiedStateLogs : logsOnly
                                    }
                            | length filteredNexts == 1 ->
                                res -- What now? would have to re-loop. Return as-is.
                                -- otherwise falling through to _otherReason
                        CutPointRule
                            | null filteredNexts ->
                                makeVacuous (combineLogs newLogs) res
                        _otherReason ->
                            res
                                { state = simplifiedState
                                , nextStates =
                                    if null filteredNexts
                                        then Nothing
                                        else Just filteredNexts
                                , logs = combineLogs $ res.logs : newLogs
                                }

data LogSettings = LogSettings
    { logSuccessfulSimplifications :: Maybe Bool
    , logFailedSimplifications :: Maybe Bool
    , logSuccessfulRewrites :: Maybe Bool
    , logFailedRewrites :: Maybe Bool
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
