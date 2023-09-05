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

import Control.Applicative (liftA2)
import Control.Concurrent.MVar qualified as MVar
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger qualified as Log
import Data.Aeson (ToJSON (..))
import Data.Aeson.KeyMap qualified as Aeson
import Data.Aeson.Types (Value (..))
import Data.Maybe (isJust)
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
            handleExecute execReq >>= traverse (postExecSimplify execReq._module)
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
                                , logs = liftA2 (++) boosterRes.logs koreRes.logs
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

    handleExecute :: ExecuteRequest -> m (Either ErrorObj (API 'Res))
    handleExecute = executionLoop (0, 0.0, 0.0)

    executionLoop :: (Depth, Double, Double) -> ExecuteRequest -> m (Either ErrorObj (API 'Res))
    executionLoop (!currentDepth, !time, !koreTime) r = do
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
                    simplifiedBoosterState <- simplifyExecuteState r._module boosterResult.state
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
                                executionLoop
                                    ( currentDepth + boosterResult.depth + koreResult.depth
                                    , time + bTime + kTime
                                    , koreTime + kTime
                                    )
                                    r{ExecuteRequest.state = execStateToKoreJson koreResult.state}
                            | otherwise -> do
                                -- otherwise we have hit a different
                                -- HaltReason, at which point we should
                                -- return, setting the correct depth
                                Log.logInfoNS "proxy" . Text.pack $
                                    "Kore " <> show koreResult.reason <> " at " <> show koreResult.depth
                                logStats ExecuteM (time + bTime + kTime, koreTime + kTime)
                                pure $ Right $ Execute koreResult{depth = currentDepth + boosterResult.depth + koreResult.depth}
                        -- can only be an error at this point
                        res -> pure res
                | otherwise -> do
                    -- we were successful with the booster, thus we
                    -- return the booster result with the updated
                    -- depth, in case we previously looped
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    logStats ExecuteM (time + bTime, koreTime)
                    pure $ Right $ Execute boosterResult{depth = currentDepth + boosterResult.depth}
            -- can only be an error at this point
            res -> pure res

    simplifyExecuteState :: Maybe Text -> ExecuteState -> m ExecuteState
    simplifyExecuteState mbModule s = do
        Log.logInfoNS "proxy" "Simplifying execution state"
        simplResult <-
            handleSimplify $ toSimplifyRequest s
        case simplResult of
            -- This request should not fail, as the only possible
            -- failure mode would be malformed or invalid kore
            Right (Simplify simplified) -> do
                -- to convert back to a term/constraints form,
                -- we run a trivial execute request (in booster)
                -- We cannot call the booster internaliser without access to the server state
                -- Again this should not fail.
                let request =
                        (emptyExecuteRequest simplified.state)
                            { _module = mbModule
                            , maxDepth = Just $ Depth 0
                            }
                Log.logInfoNS "proxy" "Making 0-step execute request to convert back to a term/constraints form"
                result <- booster $ Execute request
                case result of
                    Right (Execute ExecuteResult{state = finalState}) -> pure finalState
                    _other -> pure s
            _other -> do
                -- if we hit an error here, return the original
                Log.logWarnNS "proxy" "Unexpected failure when calling Kore simplifier, returning original term"
                pure s
      where
        toSimplifyRequest :: ExecuteState -> SimplifyRequest
        toSimplifyRequest state =
            SimplifyRequest
                { state = execStateToKoreJson state
                , _module = mbModule
                , logSuccessfulSimplifications = Nothing
                , logFailedSimplifications = Nothing
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

    postExecSimplify :: Maybe Text -> API 'Res -> m (API 'Res)
    postExecSimplify mbModule = \case
        Execute res -> Execute <$> simplifyResult res
        other -> pure other
      where
        simplifyResult :: ExecuteResult -> m ExecuteResult
        simplifyResult res@ExecuteResult{reason, state, nextStates} = do
            Log.logInfoNS "proxy" . Text.pack $ "Simplifying state in " <> show reason <> " result"
            simplifiedState <- simplifyExecuteState mbModule state
            simplifiedNexts <- maybe (pure []) (mapM $ simplifyExecuteState mbModule) nextStates
            let filteredNexts = filter (not . isBottom) simplifiedNexts
            let result = case reason of
                    Branching
                        | null filteredNexts ->
                            res{reason = Stuck, nextStates = Nothing}
                        | length filteredNexts == 1 ->
                            res -- What now? would have to re-loop. Return as-is.
                            -- otherwise falling through to _otherReason
                    CutPointRule
                        | null filteredNexts ->
                            -- HACK. Would want to return the prior state
                            res{reason = Stuck, nextStates = Nothing}
                    _otherReason ->
                        res{state = simplifiedState, nextStates}
            pure result

        isBottom :: ExecuteState -> Bool
        isBottom ExecuteState{term}
            | KoreJson.KJBottom _ <- term.term = True
        isBottom ExecuteState{predicate = Just p}
            | KoreJson.KJBottom _ <- p.term = True
        isBottom _ = False
