{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.JsonRpc (runServer) where

import Colog (
    cmap,
 )
import Control.Concurrent (forkIO, throwTo)
import Control.Concurrent.STM.TChan (newTChan, readTChan, writeTChan)
import Control.Exception (Exception, catch, mask)
import Control.Monad (forever)
import Control.Monad.Logger (MonadLoggerIO, askLoggerIO, runLoggingT)
import Control.Monad.Reader (ask, runReaderT)
import Control.Monad.STM (atomically)
import Data.Aeson.Types (FromJSON (..), ToJSON (..), Value (..))
import Data.Conduit.Network (serverSettings)
import Data.Limit (Limit (..))
import Data.Text (Text)
import Deriving.Aeson (
    CamelToKebab,
    ConstructorTagModifier,
    CustomJSON (..),
    FieldLabelModifier,
    OmitNothingFields,
 )
import GHC.Generics (Generic)
import Kore.Builtin qualified as Builtin
import Kore.Exec qualified as Exec

-- import Kore.Internal.Pattern qualified as Pattern
-- import Kore.Internal.OrPattern qualified as OrPattern
-- import Kore.Reachability.Claim qualified as Claim
-- import  Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Log.JsonRpc (LogJsonRpcServer (..))
import Kore.Rewrite (ExecutionMode (All), Natural)

-- import Kore.Rewrite.RewritingVariable as RewritingVariable
-- import Kore.Simplify.API (
--     evalSimplifier,
--  )
import Kore.Syntax.Json (KoreJson)
import Kore.Syntax.Json qualified as PatternJson

-- import Kore.Unparser (unparseToText)
import Kore.Validate.PatternVerifier qualified as PatternVerifier
import Log qualified

-- import Logic qualified
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
import SMT qualified

newtype Depth = Depth Natural
    deriving stock (Show, Eq)
    deriving newtype (FromJSON, ToJSON)

data ExecuteRequest = ExecuteRequest
    { state :: !KoreJson
    , maxDepth :: !(Maybe Depth)
    , cutPointRules :: !(Maybe [Text])
    , terminalRules :: !(Maybe [Text])
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteRequest

-- newtype StepRequest = StepRequest
--     { state :: KoreJson
--     }
--     deriving stock (Generic, Show, Eq)
--     deriving
--         (FromJSON)
--         via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] StepRequest

data ImpliesRequest = ImpliesRequest
    { antecedent :: !KoreJson
    , consequent :: !KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ImpliesRequest

newtype SimplifyRequest = SimplifyRequest
    { state :: KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (FromJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] SimplifyRequest

data ReqException = CancelRequest deriving stock (Show)

instance Exception ReqException

instance FromRequest (API 'Req) where
    parseParams "execute" = Just $ fmap (Execute <$>) parseJSON
    -- parseParams "step" = Just $ fmap (Step <$>) parseJSON
    parseParams "implies" = Just $ fmap (Implies <$>) parseJSON
    parseParams "simplify" = Just $ fmap (Simplify <$>) parseJSON
    parseParams "cancel" = Just $ const $ return Cancel
    parseParams _ = Nothing

data ExecuteState = ExecuteState
    { state :: !KoreJson
    , condition :: !(Maybe Condition)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteState

data HaltReason
    = Branching
    | Stuck
    | DepthBound
    | CutPointRule
    | TerminalRule
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, ConstructorTagModifier '[CamelToKebab]] HaltReason

data ExecuteResult = ExecuteResult
    { reason :: HaltReason
    , depth :: !Depth
    , state :: ExecuteState
    , nextStates :: Maybe [ExecuteState]
    , rule :: Maybe Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteResult

data Condition = Condition
    { substitution :: !KoreJson
    , predicate :: !KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] Condition

data ImpliesResult = ImpliesResult
    { satisfiable :: !Bool
    , condition :: !(Maybe Condition)
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ImpliesResult

newtype SimplifyResult = SimplifyResult
    { state :: KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] SimplifyResult

data ReqOrRes = Req | Res

data APIMethods
    = ExecuteM
    | ImpliesM
    | SimplifyM

type family APIPayload (api :: APIMethods) (r :: ReqOrRes) where
    APIPayload 'ExecuteM 'Req = ExecuteRequest
    APIPayload 'ExecuteM 'Res = ExecuteResult
-- APIPayload 'StepM 'Req = StepRequest
-- APIPayload 'StepM 'Res = StepResult
    APIPayload 'ImpliesM 'Req = ImpliesRequest
    APIPayload 'ImpliesM 'Res = ImpliesResult
    APIPayload 'SimplifyM 'Req = SimplifyRequest
    APIPayload 'SimplifyM 'Res = SimplifyResult

data API (r :: ReqOrRes) where
    Execute :: APIPayload 'ExecuteM r -> API r
    -- Step :: APIPayload 'StepM r -> API r
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
        -- Step payload -> toJSON payload
        Implies payload -> toJSON payload
        Simplify payload -> toJSON payload

respond :: MonadIO m => (forall a. SMT.SMT a -> IO a) -> Exec.SerializedModule -> Respond (API 'Req) m (API 'Res)
respond
    runSMT
    serializedModule@Exec.SerializedModule
        { --sortGraph
        -- , overloadGraph
        -- , metadataTools
        verifiedModule
        -- , equations
        } = \case
        Execute ExecuteRequest{state, maxDepth} ->
            case PatternVerifier.runPatternVerifier context $
                PatternVerifier.verifyStandalonePattern Nothing $
                    PatternJson.toParsedPattern $ PatternJson.term state of
                Left err -> pure $ Left $ couldNotVerify $ toJSON err
                Right verifiedPattern -> do
                    (_, _finalPatt) <-
                        liftIO
                            ( runSMT $
                                Exec.exec
                                    ( case maxDepth of
                                        Nothing -> Unlimited
                                        Just (Depth n) -> Limit n
                                    )
                                    Unlimited
                                    serializedModule
                                    All
                                    verifiedPattern
                            )

                    pure $
                        Right $
                            Execute $
                                ExecuteResult -- dummy
                                    { state = ExecuteState{state, condition = Nothing}
                                    , -- state = PatternJson.fromPattern $ Pattern.fromTermLike finalPatt,
                                      depth = Depth 0 -- dummy
                                    , reason = DepthBound -- dummy
                                    , rule = Nothing
                                    , nextStates = Nothing
                                    }
          where
            context =
                PatternVerifier.verifiedModuleContext verifiedModule
                    & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

        -- Step StepRequest{} -> pure $ Right $ Step $ StepResult []
        Implies ImpliesRequest{antecedent, consequent} ->
            pure $ case PatternVerifier.runPatternVerifier context verify of
                Left err -> Left $ couldNotVerify $ toJSON err
                Right (_antVerified, _consVerified) -> Right $ Implies $ ImpliesResult True Nothing
          where
            -- let leftPatt = mkRewritingPattern $ Pattern.fromTermLike antVerified
            --     (consWOExistentials, existentialVars) =
            --         ClaimPattern.termToExistentials $
            --             RewritingVariable.mkRewritingTerm consVerified
            --     rightPatts = OrPattern.fromPattern $ Pattern.fromTermLike consWOExistentials
            --     claim = ClaimPattern.mkClaimPattern leftPatt rightPatts existentialVars
            -- liftIO $ (do
            --     res <-
            --         runSMT $
            --             evalSimplifier verifiedModule sortGraph overloadGraph metadataTools equations $
            --                 Logic.observeAllT $
            --                     Claim.checkImplicationWorker claim

            --     pure $ Right $ Implies $ case res of
            --         [Claim.Implied] -> ImpliesResult True Nothing
            --         _ ->  ImpliesResult False Nothing)
            --     `catch` \(err :: Error Claim.CheckImplicationError) ->
            --         pure $ Left $ implicationError $ toJSON err

            context =
                PatternVerifier.verifiedModuleContext verifiedModule
                    & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

            verify = do
                antVerified <-
                    PatternVerifier.verifyStandalonePattern Nothing $
                        PatternJson.toParsedPattern $ PatternJson.term antecedent
                consVerified <-
                    PatternVerifier.verifyStandalonePattern Nothing $
                        PatternJson.toParsedPattern $ PatternJson.term consequent
                pure (antVerified, consVerified)
        Simplify SimplifyRequest{state} -> pure $ Right $ Simplify SimplifyResult{state}
        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left $ ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
      where
        couldNotVerify err = ErrorObj "Could not verify KORE pattern" (-32002) err

-- implicationError err = ErrorObj "Implication check error" (-32003) err

runServer :: Int -> SMT.SolverSetup -> Log.LoggerEnv IO -> Exec.SerializedModule -> IO ()
runServer port solverSetup Log.LoggerEnv{logAction, context = entryContext} serializedModule = do
    flip runLoggingT logFun $
        jsonrpcTCPServer V2 False srvSettings $
            srv runSMT serializedModule
  where
    srvSettings = serverSettings port "*"

    someLogAction = cmap (\actualEntry -> Log.ActualEntry{actualEntry, entryContext}) logAction

    logFun loc src level msg =
        Log.logWith someLogAction $ LogJsonRpcServer{loc, src, level, msg}

    runSMT :: forall a. SMT.SMT a -> IO a
    runSMT m = flip Log.runLoggerT logAction $ SMT.runWithSolver m solverSetup

srv :: MonadLoggerIO m => (forall a. SMT.SMT a -> IO a) -> Exec.SerializedModule -> JSONRPCT m ()
srv runSMT serializedModule = do
    reqQueue <- liftIO $ atomically newTChan
    let mainLoop tid =
            receiveBatchRequest >>= \case
                Nothing -> do
                    return ()
                Just (SingleRequest req) | Right (Cancel :: API 'Req) <- fromRequest req -> do
                    liftIO $ throwTo tid CancelRequest
                    spawnWorker reqQueue >>= mainLoop
                Just req -> do
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
        logger <- askLoggerIO
        let sendResponses r = flip runLoggingT logger $ flip runReaderT rpcSession $ sendBatchResponse r

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
                    rM <- buildResponse (respond runSMT serializedModule) req
                    mapM_ (sendResponses . SingleResponse) rM
                BatchRequest reqs -> do
                    rs <- catMaybes <$> forM reqs (buildResponse (respond runSMT serializedModule))
                    sendResponses $ BatchResponse rs

        liftIO $
            forkIO $
                forever $
                    bracketOnReqException
                        (atomically $ readTChan reqQueue)
                        cancelReq
                        processReq
