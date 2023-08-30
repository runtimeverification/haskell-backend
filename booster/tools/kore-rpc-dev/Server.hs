{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Control.Concurrent.MVar (newMVar)
import Control.Concurrent.MVar qualified as MVar
import Control.Exception (AsyncException (UserInterrupt), handleJust)
import Control.Monad (forM_, void, when)
import Control.Monad.Catch (bracket)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logger (
    LogLevel (..),
    LoggingT (runLoggingT),
    MonadLoggerIO (askLoggerIO),
    ToLogStr (toLogStr),
    defaultLoc,
 )
import Control.Monad.Logger qualified as Log
import Control.Monad.Logger qualified as Logger
import Data.Aeson.Types (Value (..))
import Data.Conduit.Network (serverSettings)
import Data.IORef (writeIORef)
import Data.InternedText (globalInternedTextCache)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Network.JSONRPC
import Options.Applicative
import System.Clock (
    Clock (..),
    getTime,
 )
import System.Exit

import Booster.CLOptions
import Booster.Trace
import GlobalMain qualified
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.BugReport (BugReportOption (..), withBugReport)
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.Internal.TermLike (TermLike, VariableName)
import Kore.JsonRpc (ServerState (..))
import Kore.JsonRpc qualified as Kore
import Kore.JsonRpc.Error
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types
import Kore.Log (
    ExeName (..),
    KoreLogType (LogSomeAction),
    LogAction (LogAction),
    TimestampsSwitch (TimestampsDisable),
    defaultKoreLogOptions,
    swappableLogger,
    withLogger,
 )
import Kore.Log qualified
import Kore.Log qualified as Log
import Kore.Log.DebugSolver qualified as Log
import Kore.Rewrite.SMT.Lemma (declareSMTLemmas)
import Kore.Syntax.Definition (ModuleName (ModuleName), SentenceAxiom)
import Options.SMT (KoreSolverOptions (..), parseKoreSolverOptions)
import SMT qualified

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

respond ::
    forall m.
    Log.MonadLogger m =>
    Respond (API 'Req) m (API 'Res) ->
    Respond (API 'Req) m (API 'Res)
respond kore req = case req of
    Execute _ ->
        loggedKore ExecuteM req >>= \case
            Right (Execute koreResult) -> do
                Log.logInfoNS "proxy" . Text.pack $
                    "Kore " <> show koreResult.reason <> " at " <> show koreResult.depth
                pure . Right . Execute $ koreResult
            res -> pure res
    Implies _ -> loggedKore ImpliesM req
    Simplify simplifyReq -> handleSimplify simplifyReq
    AddModule _ -> kore req
    GetModel _ ->
        loggedKore GetModelM req
    Cancel ->
        pure $ Left $ ErrorObj "Cancel not supported" (-32601) Null
  where
    handleSimplify :: SimplifyRequest -> m (Either ErrorObj (API 'Res))
    handleSimplify simplifyReq = do
        let koreReq = Simplify simplifyReq
        koreResult <- kore koreReq
        case koreResult of
            Right (Simplify koreRes) -> do
                pure . Right . Simplify $
                    SimplifyResult
                        { state = koreRes.state
                        , logs = koreRes.logs
                        }
            koreError ->
                pure koreError

    loggedKore method r = do
        Log.logInfoNS "proxy" . Text.pack $ show method <> " (using kore)"
        kore r

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <- execParser clParser
    let CLProxyOptions
            { clOptions =
                clOPts@CLOptions
                    { port
                    , logLevels
                    , eventlogEnabledUserEvents
                    }
            , koreSolverOptions
            , debugSolverOptions
            } = options
        (logLevel, customLevels) = adjustLogLevels logLevels
        levelFilter :: Logger.LogSource -> LogLevel -> Bool
        levelFilter _source lvl =
            lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

    Logger.runStderrLoggingT $ Logger.filterLogger levelFilter $ do
        liftIO $ forM_ eventlogEnabledUserEvents $ \t -> do
            putStrLn $ "Tracing " <> show t
            enableCustomUserEvent t

        monadLogger <- askLoggerIO

        let coLogLevel = fromMaybe Log.Info $ toSeverity logLevel
            koreLogOptions =
                (defaultKoreLogOptions (ExeName "") startTime)
                    { Log.logLevel = coLogLevel
                    , Log.timestampsSwitch = TimestampsDisable
                    , Log.debugSolverOptions = debugSolverOptions
                    , Log.logType = LogSomeAction $ LogAction $ \txt -> liftIO $ monadLogger defaultLoc "kore" logLevel $ toLogStr txt
                    }
            srvSettings = serverSettings port "*"

        liftIO $ void $ withBugReport (ExeName "kore-rpc-dev") BugReportOnError $ \reportDirectory ->
            withLogger reportDirectory koreLogOptions $ \actualLogAction -> do
                mvarLogAction <- newMVar actualLogAction
                let logAction = swappableLogger mvarLogAction

                kore@KoreServer{runSMT} <- mkKoreServer Log.LoggerEnv{logAction} clOPts koreSolverOptions
                runLoggingT (Logger.logInfoNS "proxy" "Starting RPC server") monadLogger

                let koreRespond :: Respond (API 'Req) (LoggingT IO) (API 'Res)
                    koreRespond = Kore.respond kore.serverState (ModuleName kore.mainModule) runSMT
                    server =
                        jsonRpcServer
                            srvSettings
                            (const $ respond koreRespond)
                            [handleErrorCall, handleSomeException]
                    interruptHandler _ = do
                        when (logLevel >= LevelInfo) $
                            putStrLn "[Info#proxy] Server shutting down"
                        exitSuccess
                handleJust isInterrupt interruptHandler $ runLoggingT server monadLogger
  where
    clParser =
        info
            (clProxyOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

    isInterrupt :: AsyncException -> Maybe ()
    isInterrupt UserInterrupt = Just ()
    isInterrupt _other = Nothing

toSeverity :: LogLevel -> Maybe Log.Severity
toSeverity LevelDebug = Just Log.Debug
toSeverity LevelInfo = Just Log.Info
toSeverity LevelWarn = Just Log.Warning
toSeverity LevelError = Just Log.Error
toSeverity LevelOther{} = Nothing

data CLProxyOptions = CLProxyOptions
    { clOptions :: CLOptions
    , koreSolverOptions :: !KoreSolverOptions
    , debugSolverOptions :: !Log.DebugSolverOptions
    }

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header "kore-rpc-dev - a JSON RPC for Kore with the interface of kore-rpc-booster"

clProxyOptionsParser :: Parser CLProxyOptions
clProxyOptionsParser =
    CLProxyOptions
        <$> clOptionsParser
        <*> parseKoreSolverOptions
        <*> Log.parseDebugSolverOptions

mkKoreServer :: Log.LoggerEnv IO -> CLOptions -> KoreSolverOptions -> IO KoreServer
mkKoreServer loggerEnv@Log.LoggerEnv{logAction} CLOptions{definitionFile, mainModuleName} koreSolverOptions =
    flip Log.runLoggerT logAction $ do
        sd@GlobalMain.SerializedDefinition{internedTextCache} <-
            GlobalMain.deserializeDefinition
                koreSolverOptions
                definitionFile
                (ModuleName mainModuleName)
        liftIO $ writeIORef globalInternedTextCache internedTextCache

        loadedDefinition <- GlobalMain.loadDefinitions [definitionFile]
        serverState <-
            liftIO $
                MVar.newMVar
                    Kore.ServerState
                        { serializedModules = Map.singleton (ModuleName mainModuleName) sd
                        , loadedDefinition
                        }

        pure $
            KoreServer
                { serverState
                , mainModule = mainModuleName
                , runSMT
                , loggerEnv
                }
  where
    KoreSolverOptions{timeOut, rLimit, resetInterval, prelude} = koreSolverOptions
    smtConfig =
        SMT.defaultConfig
            { SMT.timeOut = timeOut
            , SMT.rLimit = rLimit
            , SMT.resetInterval = resetInterval
            , SMT.prelude = prelude
            }

    -- SMT solver with user declared lemmas
    runSMT ::
        forall a.
        SmtMetadataTools StepperAttributes ->
        [SentenceAxiom (TermLike VariableName)] ->
        SMT.SMT a ->
        IO a
    runSMT metadataTools lemmas m =
        flip Log.runLoggerT logAction $
            bracket (SMT.newSolver smtConfig) SMT.stopSolver $ \refSolverHandle -> do
                let userInit = SMT.runWithSolver $ declareSMTLemmas metadataTools lemmas
                    solverSetup =
                        SMT.SolverSetup
                            { userInit
                            , refSolverHandle
                            , config = smtConfig
                            }
                SMT.initSolver solverSetup
                SMT.runWithSolver m solverSetup
