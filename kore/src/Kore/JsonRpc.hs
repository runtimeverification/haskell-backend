module Kore.JsonRpc (runServer) where

import Control.Concurrent (forkIO, throwTo)
import Control.Concurrent.STM.TChan (newTChan, readTChan, writeTChan)
import Control.Exception (Exception, catch, mask)
import Control.Monad (forever, liftM)
import Control.Monad.Logger (MonadLoggerIO, runStderrLoggingT)
import Control.Monad.Reader (ask, runReaderT)
import Control.Monad.STM (atomically)
import Data.Aeson.Types hiding (Error)
import Data.Conduit.Network (serverSettings)
import qualified Data.Foldable as F
import Data.Text (Text)
import Deriving.Aeson (
    CamelToKebab,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
    StripPrefix,
 )
import GHC.Generics (Generic)
import Network.JSONRPC (
    BatchRequest (BatchRequest, SingleRequest),
    BatchResponse (BatchResponse, SingleResponse),
    ErrorObj (..),
    FromRequest (..),
    JSONRPCT,
    Request (..),
    Respond,
    Response (ResponseError),
    Ver (V2),
    buildResponse,
    fromRequest,
    jsonrpcTCPServer,
    receiveBatchRequest,
    sendBatchResponse,
 )
import Prelude.Kore

data ExecuteRequest = ExecuteRequest
    { executeRequestState :: !Text
    , executeRequestMaxDepth :: !(Maybe Int)
    , executeRequestHaltPatterns :: ![Text]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "executeRequest", CamelToKebab]] ExecuteRequest

data StepRequest = StepRequest
    { stepRequestState :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "stepRequest", CamelToKebab]] StepRequest

data ImpliesRequest = ImpliesRequest
    { impliesRequestAntecedent :: !Text
    , impliesRequestConsequent :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "impliesRequest", CamelToKebab]] ImpliesRequest

data SimplifyRequest = SimplifyRequest
    { simplifyRequestState :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "simplifyRequest", CamelToKebab]] SimplifyRequest

data ReqException = CancelRequest deriving stock (Show)

instance Exception ReqException

instance FromRequest (API 'Req) where
    parseParams "execute" = Just $ fmap (Execute <$>) parseJSON
    parseParams "step" = Just $ fmap (Step <$>) parseJSON
    parseParams "implies" = Just $ fmap (Implies <$>) parseJSON
    parseParams "simplify" = Just $ fmap (Simplify <$>) parseJSON
    parseParams "cancel" = Just $ const $ return Cancel
    parseParams _ = Nothing

data PatternMatch = PatternMatch
    { patternMatchPattern :: !Int
    , patternMatchSubstitution :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "patternMatch", CamelToKebab]] PatternMatch

data ReasonForHalting
    = HaltBranching
        { branchingDepth :: !Int
        }
    | HaltStuck
        { stuckDepth :: !Int
        }
    | HaltDepthBound
    | HaltPatternMatch
        { patternMatchDepth :: !Int
        , patternMatchMatches :: ![PatternMatch]
        }
    deriving stock (Show, Eq)

instance ToJSON ReasonForHalting where
    toJSON = \case
        HaltBranching{branchingDepth} -> object ["reason" .= ("branching" :: Text), "depth" .= branchingDepth]
        HaltStuck{stuckDepth} -> object ["reason" .= ("stuck" :: Text), "depth" .= stuckDepth]
        HaltDepthBound -> object ["reason" .= ("depth-bound" :: Text)]
        HaltPatternMatch{patternMatchDepth, patternMatchMatches} ->
            object
                [ "reason" .= ("pattern-match" :: Text)
                , "depth" .= patternMatchDepth
                , "matches" .= patternMatchMatches
                ]

data StepState = StepState
    { stepStateState :: !Text
    , stepStateDepth :: !Int
    , stepStateCondition :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "stepState", CamelToKebab]] StepState

data ExecuteResult = ExecuteResult
    { executeResultState :: !Text
    , executeResultPatterns :: ![Text]
    , executeResultReason :: !ReasonForHalting
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "executeResult", CamelToKebab]] ExecuteResult

data StepResult = StepResult
    { stepResultStates :: ![StepState]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "stepResult", CamelToKebab]] StepResult

data ImpliesResult = ImpliesResult
    { impliesResultSatisfiable :: !Bool
    , impliesResultSubstitution :: !(Maybe Text)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "impliesResult", CamelToKebab]] ImpliesResult

data SimplifyResult = SimplifyResult
    { simplifyResultState :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "simplifyResult", CamelToKebab]] SimplifyResult

data ReqOrRes = Req | Res

data APIMethods = ExecuteM | StepM | ImpliesM | SimplifyM

type family APIPayload (api :: APIMethods) (r :: ReqOrRes) where
    APIPayload 'ExecuteM 'Req = ExecuteRequest
    APIPayload 'ExecuteM 'Res = ExecuteResult
    APIPayload 'StepM 'Req = StepRequest
    APIPayload 'StepM 'Res = StepResult
    APIPayload 'ImpliesM 'Req = ImpliesRequest
    APIPayload 'ImpliesM 'Res = ImpliesResult
    APIPayload 'SimplifyM 'Req = SimplifyRequest
    APIPayload 'SimplifyM 'Res = SimplifyResult

data API (r :: ReqOrRes) where
    Execute :: APIPayload 'ExecuteM r -> API r
    Step :: APIPayload 'StepM r -> API r
    Implies :: APIPayload 'ImpliesM r -> API r
    Simplify :: APIPayload 'SimplifyM r -> API r
    Cancel :: API 'Req

deriving stock instance Show (API 'Req)
deriving stock instance Show (API 'Res)
deriving stock instance Eq (API 'Req)
deriving stock instance Eq (API 'Res)

instance ToJSON (API 'Res) where
    toJSON = \case
        Execute payload -> toJSON payload
        Step payload -> toJSON payload
        Implies payload -> toJSON payload
        Simplify payload -> toJSON payload

respond :: MonadIO m => Respond (API 'Req) m (API 'Res)
respond = \case
    Execute _ -> pure $ Right $ Execute undefined
    Step StepRequest{} -> pure $ Right $ Step $ StepResult []
    Implies _ -> pure $ Right $ Implies undefined
    Simplify _ -> pure $ Right $ Simplify undefined
    Cancel -> pure $ Left $ ErrorObj "Cancel Request unsupported in batch mode" (-32001) Null

runServer :: IO ()
runServer = do
    runStderrLoggingT $ do
        let ss = serverSettings 31337 "*"
        jsonrpcTCPServer V2 False ss srv

srv :: MonadLoggerIO m => JSONRPCT m ()
srv = do
    reqQueue <- liftIO $ atomically newTChan
    qs <- ask
    let sendResponses r = runStderrLoggingT $ runReaderT (sendBatchResponse r) qs

        cancelReq = \case
            SingleRequest req@Request{} -> do
                let v = getReqVer req
                    i = getReqId req
                sendResponses $ SingleResponse $ ResponseError v cancelError i
            SingleRequest Notif{} -> pure ()
            BatchRequest reqs ->
                sendResponses $ BatchResponse $ [ResponseError (getReqVer req) cancelError (getReqId req) | req <- reqs, isRequest req]

        processReq = \case
            SingleRequest req -> do
                rM <- buildResponse respond req
                F.forM_ rM (sendResponses . SingleResponse)
            BatchRequest reqs -> do
                rs <- catMaybes `liftM` forM reqs (buildResponse respond)
                sendResponses $ BatchResponse rs

        spawnWorker =
            liftIO $
                forkIO $
                    forever $
                        bracketOnReqException
                            (atomically $ readTChan reqQueue)
                            cancelReq
                            processReq

        mainLoop tid =
            receiveBatchRequest >>= \case
                Nothing -> do
                    return ()
                Just (SingleRequest req) | Right (Cancel :: API 'Req) <- fromRequest req -> do
                    liftIO $ throwTo tid CancelRequest
                    spawnWorker >>= mainLoop
                Just req -> do
                    liftIO $ atomically $ writeTChan reqQueue req
                    mainLoop tid

    spawnWorker >>= mainLoop
  where
    isRequest = \case
        Request{} -> True
        _ -> False

    cancelError = ErrorObj "Request cancelled" (-32000) Null

    bracketOnReqException before onCancel thing =
        mask $ \restore -> do
            a <- before
            restore (thing a) `catch` \(_ :: ReqException) -> onCancel a

-- receiveRequests = runStderrLoggingT $ runReaderT receiveBatchRequest qs

-- processRequest = forever $
--     (atomically $ readTChan reqQueue) >>=
--     (\case
--       SingleRequest req -> do
--         rM <- buildResponse respond req
--         F.forM_ rM (sendResponses . SingleResponse)
--       BatchRequest reqs -> do
--         rs <- catMaybes `liftM` forM reqs (buildResponse respond)
--         sendResponses $ BatchResponse rs)

-- processRequest =
--   foreverBracketOnReqException
--     (do
--       req <- atomically $ readTChan reqQueue
--       runStderrLoggingT ($(logDebug) ("process Q: " <> T.pack (show req)))
--       return req
--       )
--     (\case
--       SingleRequest req@Request{} -> do
--         let v = getReqVer req
--             i = getReqId req
--         sendResponses $ SingleResponse $ ResponseError v cancelError i
--       SingleRequest _ -> pure ()
--       BatchRequest reqs ->
--         sendResponses $ BatchResponse $ [ ResponseError (getReqVer req) cancelError (getReqId req) | req <- reqs, isRequest req ])
--     (\case
--       SingleRequest req -> do
--         rM <- buildResponse respond req
--         F.forM_ rM (sendResponses . SingleResponse)
--       BatchRequest reqs -> do
--         rs <- catMaybes `liftM` forM reqs (buildResponse respond)
--         sendResponses $ BatchResponse rs)

------------

------------

-- liftIO $ withAsync processRequest $ \procReq ->
--   let
--     tid = asyncThreadId procReq
--     loop = receiveRequests >>= \case
--       Nothing -> do
--         return ()
--       Just (SingleRequest req) | Right Cancel <- fromRequest req -> do
--         runStderrLoggingT ($(logDebug) "sending cancel")
--         throwTo tid AsyncCancelled
--         loop
--       Just req -> do
--         runStderrLoggingT ($(logDebug) ("add to Q: " <> T.pack (show req)))
--         atomically $ writeTChan reqQueue req
--         loop
--   in
--     loop

-- srv2 :: MonadLoggerIO m => JSONRPCT m ()
-- srv2 = do
--     $(logDebug) "listening for new request"
--     qM <- receiveBatchRequest
--     case qM of
--         Nothing -> do
--             $(logDebug) "closed request channel, exting"
--             return ()
--         Just (SingleRequest q) -> do
--             $(logDebug) "got request"
--             rM <- buildResponse respond q
--             F.forM_ rM sendResponse
--             srv2
--         Just (BatchRequest qs) -> do
--             $(logDebug) "got request batch"
--             rs <- catMaybes `liftM` forM qs (buildResponse respond)
--             sendBatchResponse $ BatchResponse rs
--             srv2
