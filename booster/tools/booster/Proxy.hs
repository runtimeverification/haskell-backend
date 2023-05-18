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
import Kore.Log qualified
import Kore.Syntax.Definition (SentenceAxiom)
import Stats (APIMethods (..), StatsVar, addStats, microsWithUnit, timed)

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
            loggedKore Stats.ExecuteM req
        | otherwise ->
            startLoop execReq
    Implies _ ->
        loggedKore Stats.ImpliesM req
    Simplify _ ->
        loggedKore Stats.SimplifyM req
    AddModule _ -> do
        -- execute in booster first, assuming that kore won't throw an
        -- error if booster did not. The response is empty anyway.
        (boosterResult, boosterTime) <- withTime $ booster req
        case boosterResult of
            Left _err -> pure boosterResult
            Right _ -> do
                (koreRes, koreTime) <- withTime $ kore req
                logStats Stats.AddModuleM (boosterTime + koreTime, koreTime)
                pure koreRes
    Cancel ->
        pure $ Left $ ErrorObj "Cancel not supported" (-32601) Null
  where
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

    startLoop = loop (0, 0.0, 0.0)

    -- loop :: (Depth, Double, Double) -> ExecuteRequest -> m (Either Response)
    loop (!currentDepth, !time, !koreTime) r = do
        Log.logInfoNS "proxy" . Text.pack $
            if currentDepth == 0
                then "Starting execute request"
                else "Iterating execute request at " <> show currentDepth
        let mbDepthLimit = flip (-) currentDepth <$> r.maxDepth
        (bResult, bTime) <- withTime $ booster (Execute r{maxDepth = mbDepthLimit})
        case bResult of
            Right (Execute boosterResult)
                -- if the new backend aborts or gets stuck, revert to the old one
                --
                -- if we are stuck in the new backend we try to re-run
                -- in the old one to work around any potential
                -- unification bugs.
                | boosterResult.reason `elem` [Aborted, Stuck] -> do
                    -- attempt to do one step in the old backend
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    (kResult, kTime) <-
                        withTime $
                            kore
                                ( Execute
                                    r
                                        { state = execStateToKoreJson boosterResult.state
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
                                Log.logInfoNS "proxy" "kore depth-bound, continuing"
                                loop
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
                                    "Kore " <> show koreResult.reason
                                logStats Stats.ExecuteM (time + bTime + kTime, koreTime + kTime)
                                pure $ Right $ Execute koreResult{depth = currentDepth + boosterResult.depth + koreResult.depth}
                        -- can only be an error at this point
                        res -> pure res
                | otherwise -> do
                    -- we were successful with the booster, thus we
                    -- return the booster result with the updated
                    -- depth, in case we previously looped
                    Log.logInfoNS "proxy" . Text.pack $
                        "Booster " <> show boosterResult.reason <> " at " <> show boosterResult.depth
                    logStats Stats.ExecuteM (time + bTime, koreTime)
                    pure $ Right $ Execute boosterResult{depth = currentDepth + boosterResult.depth}
            -- can only be an error at this point
            res -> pure res
