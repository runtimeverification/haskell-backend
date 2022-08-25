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
import Control.Exception (ErrorCall (..), Exception, mask)
import Control.Monad (forever)
import Control.Monad.Catch (MonadCatch, catch, handle)
import Control.Monad.Except (runExceptT)
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
import Kore.Error (Error (..))
import Kore.Exec qualified as Exec
import Kore.Exec.GraphTraversal qualified as GraphTraversal
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (pattern PredicateTrue)
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.InfoExecDepth (ExecDepth (..))
import Kore.Log.JsonRpc (LogJsonRpcServer (..))
import Kore.Reachability.Claim qualified as Claim
import Kore.Rewrite (
    Natural,
    ProgramState,
    extractProgramState,
 )
import Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    getRewritingVariable,
    mkRewritingPattern,
    mkRewritingTerm,
 )
import Kore.Simplify.API (evalSimplifier)
import Kore.Syntax.Json (KoreJson)
import Kore.Syntax.Json qualified as PatternJson
import Kore.Validate.PatternVerifier qualified as PatternVerifier
import Log qualified
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
import Pretty qualified
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
    { term :: KoreJson
    , substitution :: Maybe KoreJson
    , predicate :: Maybe KoreJson
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
    , depth :: Depth
    , state :: ExecuteState
    , nextStates :: Maybe [ExecuteState]
    , rule :: Maybe Text
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] ExecuteResult

data Condition = Condition
    { substitution :: KoreJson
    , predicate :: KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[OmitNothingFields, FieldLabelModifier '[CamelToKebab]] Condition

data ImpliesResult = ImpliesResult
    { satisfiable :: Bool
    , condition :: Maybe Condition
    , term :: Maybe KoreJson
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

respond ::
    forall m.
    MonadIO m =>
    MonadCatch m =>
    (forall a. SMT.SMT a -> IO a) ->
    Exec.SerializedModule ->
    Respond (API 'Req) m (API 'Res)
respond runSMT serializedModule =
    withErrHandler . \case
        Execute ExecuteRequest{state, maxDepth} ->
            case PatternVerifier.runPatternVerifier context $
                PatternVerifier.verifyStandalonePattern Nothing $
                    PatternJson.toParsedPattern $ PatternJson.term state of
                Left err -> pure $ Left $ couldNotVerify $ toJSON err
                Right verifiedPattern -> do
                    traversalResult <-
                        liftIO
                            ( runSMT $
                                Exec.rpcExec
                                    (maybe Unlimited (\(Depth n) -> Limit n) maxDepth)
                                    serializedModule
                                    verifiedPattern
                            )

                    pure $ buildResult (TermLike.termLikeSort verifiedPattern) traversalResult
          where
            context =
                PatternVerifier.verifiedModuleContext verifiedModule
                    & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

            buildResult ::
                TermLike.Sort ->
                GraphTraversal.TraversalResult
                    (ExecDepth, ProgramState (Pattern TermLike.VariableName)) ->
                Either ErrorObj (API 'Res)
            buildResult sort = \case
                GraphTraversal.Ended [(ExecDepth depth, result)] ->
                    -- Actually not "ended" but out of instructions.
                    -- See @toTransitionResult@ in @rpcExec@.
                    Right $
                        Execute $
                            ExecuteResult
                                { state = patternToExecState sort result
                                , depth = Depth depth
                                , reason = DepthBound
                                , rule = Nothing
                                , nextStates = Nothing
                                }
                GraphTraversal.GotStuck _n [(ExecDepth depth, result)] ->
                    Right $
                        Execute $
                            ExecuteResult
                                { state = patternToExecState sort result
                                , depth = Depth depth
                                , reason = Stuck
                                , rule = Nothing
                                , nextStates = Nothing
                                }
                GraphTraversal.Stopped [(ExecDepth depth, result)] nexts ->
                    -- TODO add rule information, decide terminal or cut-point
                    Right $
                        Execute $
                            ExecuteResult
                                { state = patternToExecState sort result
                                , depth = Depth depth
                                , reason = Branching
                                , rule = Nothing
                                , nextStates = Just $ map (patternToExecState sort . snd) nexts
                                }
                -- these are programmer errors
                result@GraphTraversal.Aborted{} ->
                    Left $ serverError "aborted" $ asText result
                other ->
                    Left $ serverError "multiple states in result" $ asText other

            patternToExecState ::
                TermLike.Sort ->
                ProgramState (Pattern TermLike.VariableName) ->
                ExecuteState
            patternToExecState sort s =
                ExecuteState
                    { term =
                        PatternJson.fromTermLike $ Pattern.term p
                    , substitution =
                        PatternJson.fromSubstitution $ Pattern.substitution p
                    , predicate =
                        case Pattern.predicate p of
                            PredicateTrue -> Nothing
                            pr -> Just $ PatternJson.fromPredicate sort pr
                    }
              where
                p = fromMaybe (Pattern.bottomOf sort) $ extractProgramState s

        -- Step StepRequest{} -> pure $ Right $ Step $ StepResult []
        Implies ImpliesRequest{antecedent, consequent} ->
            case PatternVerifier.runPatternVerifier context verify of
                Left err ->
                    pure $ Left $ couldNotVerify $ toJSON err
                Right (antVerified, consVerified) -> do
                    let leftPatt =
                            mkRewritingPattern $ Pattern.parsePatternFromTermLike antVerified
                        sort = TermLike.termLikeSort antVerified
                        (consWOExistentials, existentialVars) =
                            ClaimPattern.termToExistentials $
                                mkRewritingTerm consVerified
                        rightPatt = Pattern.parsePatternFromTermLike consWOExistentials

                    result <-
                        liftIO
                            . runSMT
                            . evalInContext
                            . runExceptT
                            $ Claim.checkSimpleImplication
                                leftPatt
                                rightPatt
                                existentialVars
                    pure $ buildResult sort result
          where
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

            evalInContext =
                evalSimplifier
                    verifiedModule
                    sortGraph
                    overloadGraph
                    metadataTools
                    equations

            -- renderCond :: Pattern v -> Condition
            renderCond sort (toOutput -> pat) =
                let predicate =
                        PatternJson.fromPredicate sort $ Pattern.predicate pat
                    mbSubstitution =
                        PatternJson.fromSubstitution $ Pattern.substitution pat
                    noSubstitution = PatternJson.fromTermLike $ TermLike.mkTop sort
                 in Condition
                        { predicate
                        , substitution = fromMaybe noSubstitution mbSubstitution
                        }

            buildResult _ (Left err) = Left $ implicationError $ toJSON err
            buildResult sort (Right r) =
                Right . Implies $
                    case r of
                        Claim.Implied mbPat ->
                            ImpliesResult True (fmap (renderCond sort) mbPat) Nothing
                        Claim.NotImpliedStuck Nothing ->
                            ImpliesResult False Nothing Nothing
                        Claim.NotImpliedStuck (Just pat) ->
                            let term =
                                    Just
                                        . PatternJson.fromTermLike
                                        . Pattern.term
                                        $ toOutput pat
                                cond = Just $ renderCond sort pat
                             in ImpliesResult False cond term
                        Claim.NotImplied _ ->
                            ImpliesResult False Nothing Nothing

            toOutput = Pattern.mapVariables getRewritingVariable
        Simplify SimplifyRequest{state} -> pure $ Right $ Simplify SimplifyResult{state}
        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left $ ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
  where
    Exec.SerializedModule
        { sortGraph
        , overloadGraph
        , metadataTools
        , verifiedModule
        , equations
        } = serializedModule

    couldNotVerify err = ErrorObj "Could not verify KORE pattern" (-32002) err

    serverError detail payload =
        ErrorObj ("Server error: " <> detail) (-32032) payload

    asText :: Pretty.Pretty a => a -> Value
    asText = String . Pretty.renderText . Pretty.layoutOneLine . Pretty.pretty

    implicationError err = ErrorObj "Implication check error" (-32003) err

    -- catch all calls to `error` that may occur within the guts of the engine
    withErrHandler ::
        m (Either ErrorObj res) ->
        m (Either ErrorObj res)
    withErrHandler =
        let mkError (ErrorCallWithLocation msg loc) =
                Error{errorContext = [loc], errorError = msg}
         in handle (pure . Left . serverError "crashed" . toJSON . mkError)

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
