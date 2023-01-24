{- |
Module      : Kore.JsonRpc
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.JsonRpc (
    runServer,
) where

import Control.Concurrent (forkIO, throwTo)
import Control.Concurrent.STM.TChan (newTChan, readTChan, writeTChan)
import Control.Exception (ErrorCall (..), mask)
import Control.Monad (forever)
import Control.Monad.Catch (MonadCatch, catch, handle)
import Control.Monad.IO.Class
import Control.Monad.Logger.CallStack (LogLevel (LevelError), MonadLoggerIO)
import Control.Monad.Logger.CallStack qualified as Log
import Control.Monad.STM (atomically)
import Control.Monad.Trans.Except (runExcept)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Data.Aeson (object, toJSON, (.=))
import Data.Aeson.Types (Value (..))
import Data.Conduit.Network (serverSettings)
import Data.Foldable
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text qualified as Text
import Network.JSONRPC (
    BatchRequest (BatchRequest, SingleRequest),
    BatchResponse (BatchResponse, SingleResponse),
    ErrorObj (..),
    JSONRPCT,
    Request (..),
    Respond,
    Response (ResponseError),
    Ver (V2),
    buildResponse,
    fromRequest,
    receiveBatchRequest,
    sendBatchResponse,
 )
import Numeric.Natural

import Kore.Definition.Base (KoreDefinition (..))
import Kore.JsonRpc.Base
import Kore.LLVM.Internal qualified as LLVM
import Kore.Network.JsonRpc (jsonrpcTCPServer)
import Kore.Pattern.Base (Pattern)
import Kore.Pattern.Rewrite (RewriteResult (..), performRewrite)
import Kore.Syntax.Json (KoreJson (..), addHeader)
import Kore.Syntax.Json.Externalise (externalisePattern)
import Kore.Syntax.Json.Internalise (PatternError, internalisePattern)

respond ::
    forall m.
    MonadCatch m =>
    MonadLoggerIO m =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Respond (API 'Req) m (API 'Res)
respond def@KoreDefinition{} mLlvmLibrary =
    catchingServerErrors . \case
        Execute req -> do
            Log.logDebug "Testing JSON-RPC server."
            -- internalise given constrained term
            let internalised = runExcept $ internalisePattern Nothing def req.state.term

            case internalised of
                Left patternError -> do
                    Log.logDebug $ "Error internalising cterm" <> Text.pack (show patternError)
                    pure $ Left $ reportPatternError patternError
                Right pat -> do
                    let cutPoints = fromMaybe [] req.cutPointRules
                        terminals = fromMaybe [] req.terminalRules
                        mbDepth = fmap getNat req.maxDepth
                    execResponse <$> performRewrite def mLlvmLibrary mbDepth cutPoints terminals pat

        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left $ ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
        -- using "Method does not exist" error code

        _ -> pure $ Left $ ErrorObj "Not implemented" (-32601) Null
  where
    execResponse :: (Natural, RewriteResult Pattern) -> Either ErrorObj (API 'Res)
    execResponse (_, RewriteSingle{}) =
        error "Single rewrite result"
    execResponse (d, RewriteBranch p nexts) =
        Right $
            Execute
                ExecuteResult
                    { reason = Branching
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Just $ map toExecState $ toList nexts
                    , rule = Nothing
                    }
    execResponse (d, RewriteStuck p) =
        Right $
            Execute
                ExecuteResult
                    { reason = Stuck
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    execResponse (d, RewriteCutPoint lbl p next) =
        Right $
            Execute
                ExecuteResult
                    { reason = CutPointRule
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Just [toExecState next]
                    , rule = Just lbl
                    }
    execResponse (d, RewriteTerminal lbl p) =
        Right $
            Execute
                ExecuteResult
                    { reason = TerminalRule
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Just lbl
                    }
    execResponse (d, RewriteStopped p) =
        Right $
            Execute
                ExecuteResult
                    { reason = DepthBound
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    execResponse (d, RewriteAborted p) =
        Right $
            Execute
                ExecuteResult
                    { reason = Aborted
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }

    toExecState :: Pattern -> ExecuteState
    toExecState pat =
        ExecuteState{term = addHeader t, predicate = fmap addHeader p}
      where
        (t, p) = externalisePattern pat

    reportPatternError :: PatternError -> ErrorObj
    reportPatternError pErr =
        ErrorObj "Could not verify KORE pattern" (-32002) $ toJSON pErr

{- | Catches all calls to `error` from the guts of the engine, and
     returns json with the message and location as context.
-}
catchingServerErrors ::
    MonadCatch m =>
    MonadLoggerIO m =>
    m (Either ErrorObj res) ->
    m (Either ErrorObj res)
catchingServerErrors =
    let mkError (ErrorCallWithLocation msg loc) =
            object ["error" .= msg, "context" .= loc]
     in handle $ \err -> do
            Log.logError $ "Server error: " <> Text.pack (show err)
            pure $ Left (ErrorObj "Server error" (-32032) $ mkError err)

runServer :: Int -> KoreDefinition -> Maybe LLVM.API -> (LogLevel, [LogLevel]) -> IO ()
runServer port internalizedModule mLlvmLibrary (logLevel, customLevels) =
    do
        Log.runStderrLoggingT . Log.filterLogger levelFilter
        $ jsonrpcTCPServer
            rpcJsonConfig
            V2
            False
            srvSettings
            (srv internalizedModule mLlvmLibrary)
  where
    levelFilter _source lvl =
        lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

    srvSettings = serverSettings port "*"

srv :: MonadLoggerIO m => KoreDefinition -> Maybe LLVM.API -> JSONRPCT m ()
srv internalizedModule mLlvmLibrary = do
    reqQueue <- liftIO $ atomically newTChan
    let mainLoop tid =
            receiveBatchRequest >>= \case
                Nothing -> do
                    return ()
                Just (SingleRequest req) | Right (Cancel :: API 'Req) <- fromRequest req -> do
                    Log.logInfoN "Cancel Request"
                    liftIO $ throwTo tid CancelRequest
                    mainLoop tid
                Just req -> do
                    Log.logInfoN $ Text.pack (show req)
                    liftIO $ atomically $ writeTChan reqQueue req
                    mainLoop tid
    spawnWorker reqQueue >>= mainLoop
  where
    isRequest = \case
        Request{} -> True
        _ -> False

    cancelError = ErrorObj "Request cancelled" (-32000) Null

    bracketOnReqException before onCancel thing =
        mask $ \restore -> do
            a <- before
            restore (thing a) `catch` \(_ :: ReqException) -> onCancel a

    spawnWorker reqQueue = do
        rpcSession <- ask
        logger <- Log.askLoggerIO
        let withLog :: Log.LoggingT IO a -> IO a
            withLog = flip Log.runLoggingT logger

            sendResponses :: BatchResponse -> Log.LoggingT IO ()
            sendResponses r = flip Log.runLoggingT logger $ flip runReaderT rpcSession $ sendBatchResponse r
            respondTo :: Request -> Log.LoggingT IO (Maybe Response)
            respondTo = buildResponse (respond internalizedModule mLlvmLibrary)

            cancelReq :: BatchRequest -> Log.LoggingT IO ()
            cancelReq = \case
                SingleRequest req@Request{} -> do
                    let reqVersion = getReqVer req
                        reqId = getReqId req
                    sendResponses $ SingleResponse $ ResponseError reqVersion cancelError reqId
                SingleRequest Notif{} -> pure ()
                BatchRequest reqs -> do
                    sendResponses $ BatchResponse $ [ResponseError (getReqVer req) cancelError (getReqId req) | req <- reqs, isRequest req]

            processReq :: BatchRequest -> Log.LoggingT IO ()
            processReq = \case
                SingleRequest req -> do
                    rM <- respondTo req
                    mapM_ (sendResponses . SingleResponse) rM
                BatchRequest reqs -> do
                    rs <- catMaybes <$> mapM respondTo reqs
                    sendResponses $ BatchResponse rs

        liftIO $
            forkIO $
                forever $
                    bracketOnReqException
                        (atomically $ readTChan reqQueue)
                        (withLog . cancelReq)
                        (withLog . processReq)
