module Kore.JsonRpc (runServer) where

import Control.Concurrent (forkIO, throwTo)
import Control.Concurrent.STM.TChan (newTChan, readTChan, writeTChan)
import Control.Exception (Exception, catch, mask)
import Control.Monad (forever)
import Control.Monad.Logger (MonadLoggerIO, runStderrLoggingT)
import Control.Monad.Reader (ask, runReaderT)
import Control.Monad.STM (atomically)
import Data.Aeson.Types hiding (Error)
import Data.Conduit.Network (serverSettings)
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
    { state :: !Text
    , maxDepth :: !(Maybe Int)
    , haltPatterns :: ![Text]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteRequest

newtype StepRequest = StepRequest
    { state :: Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] StepRequest

data ImpliesRequest = ImpliesRequest
    { antecedent :: !Text
    , consequent :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ImpliesRequest

newtype SimplifyRequest = SimplifyRequest
    { state :: Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] SimplifyRequest

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
    { pmPattern :: !Int
    , pmSubstitution :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[StripPrefix "pm", CamelToKebab]] PatternMatch

data ReasonForHalting
    = HaltBranching
        { depth :: !Int
        }
    | HaltStuck
        { depth :: !Int
        }
    | HaltDepthBound
    | HaltPatternMatch
        { depth :: !Int
        , matches :: ![PatternMatch]
        }
    deriving stock (Show, Eq)

instance ToJSON ReasonForHalting where
    toJSON = \case
        HaltBranching{depth} -> object ["reason" .= ("branching" :: Text), "depth" .= depth]
        HaltStuck{depth} -> object ["reason" .= ("stuck" :: Text), "depth" .= depth]
        HaltDepthBound -> object ["reason" .= ("depth-bound" :: Text)]
        HaltPatternMatch{depth, matches} ->
            object
                [ "reason" .= ("pattern-match" :: Text)
                , "depth" .= depth
                , "matches" .= matches
                ]

data StepState = StepState
    { state :: !Text
    , depth :: !Int
    , condition :: !Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] StepState

data ExecuteResult = ExecuteResult
    { state :: !Text
    , patterns :: ![Text]
    , reason :: !ReasonForHalting
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteResult

newtype StepResult = StepResult
    { states :: [StepState]
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] StepResult

data ImpliesResult = ImpliesResult
    { satisfiable :: !Bool
    , substitution :: !(Maybe Text)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ImpliesResult

newtype SimplifyResult = SimplifyResult
    { state :: Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] SimplifyResult

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
                mapM_ (sendResponses . SingleResponse) rM
            BatchRequest reqs -> do
                rs <- catMaybes <$> forM reqs (buildResponse respond)
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
