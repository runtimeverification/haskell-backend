{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Control.Concurrent.MVar (newMVar)
import Control.Concurrent.MVar qualified as MVar
import Control.DeepSeq (force)
import Control.Exception (AsyncException (UserInterrupt), evaluate, handleJust)
import Control.Monad (forM_, unless, void, when)
import Control.Monad.Catch (bracket)
import Control.Monad.Extra (whenJust)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logger (
    LogLevel (..),
    LoggingT (runLoggingT),
    MonadLoggerIO (askLoggerIO),
    ToLogStr (toLogStr),
    defaultLoc,
 )
import Control.Monad.Logger qualified as Logger
import Data.Conduit.Network (serverSettings)
import Data.IORef (writeIORef)
import Data.InternedText (globalInternedTextCache)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set qualified as Set
import Options.Applicative
import System.Clock (
    Clock (..),
    getTime,
 )
import System.Exit
import System.IO (hPutStrLn, stderr)

import Booster.CLOptions
import Booster.JsonRpc qualified as Booster
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace
import Data.Text qualified as Text
import GlobalMain qualified
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.BugReport (BugReportOption (..), withBugReport)
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.Internal.TermLike (TermLike, VariableName)
import Kore.JsonRpc (ServerState (..))
import Kore.JsonRpc qualified as Kore
import Kore.JsonRpc.Error
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types (API, ReqOrRes (Req, Res))
import Kore.JsonRpc.Types.Depth (Depth (..))
import Kore.Log (
    ExeName (..),
    KoreLogType (LogSomeAction),
    LogAction (LogAction),
    TimestampsSwitch (TimestampsDisable),
    defaultKoreLogOptions,
    swappableLogger,
    withLogger,
 )
import Kore.Log qualified as Log
import Kore.Log.DebugSolver qualified as Log
import Kore.Log.Registry qualified as Log
import Kore.Rewrite.SMT.Lemma (declareSMTLemmas)
import Kore.Syntax.Definition (ModuleName (ModuleName), SentenceAxiom)
import Options.SMT (KoreSolverOptions (..), parseKoreSolverOptions)
import Proxy (KoreServer (..), ProxyConfig (..))
import Proxy qualified
import SMT qualified
import Stats qualified

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <- execParser clParser
    let CLProxyOptions
            { clOptions =
                clOPts@CLOptions
                    { definitionFile
                    , mainModuleName
                    , port
                    , logLevels
                    , llvmLibraryFile
                    , eventlogEnabledUserEvents
                    }
            , koreSolverOptions
            , proxyOptions = ProxyOptions{printStats, forceFallback}
            , debugSolverOptions
            } = options
        (logLevel, customLevels) = adjustLogLevels logLevels
        levelFilter :: Logger.LogSource -> LogLevel -> Bool
        levelFilter _source lvl =
            lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError
        koreLogExtraLevels =
            Set.unions $ mapMaybe (`Map.lookup` koreExtraLogs) customLevels

    Logger.runStderrLoggingT $ Logger.filterLogger levelFilter $ do
        liftIO $ forM_ eventlogEnabledUserEvents $ \t -> do
            putStrLn $ "Tracing " <> show t
            enableCustomUserEvent t
        Logger.logInfoNS "proxy" $
            Text.pack $
                "Loading definition from "
                    <> definitionFile
                    <> ", main module "
                    <> show mainModuleName
        definitions <-
            liftIO $
                loadDefinition definitionFile
                    >>= evaluate . force . either (error . show) id
        unless (isJust $ Map.lookup mainModuleName definitions) $ do
            Logger.logErrorNS "proxy" $
                "Main module " <> mainModuleName <> " not found in " <> Text.pack definitionFile
            liftIO exitFailure

        monadLogger <- askLoggerIO

        let coLogLevel = fromMaybe Log.Info $ toSeverity logLevel

            koreLogOptions =
                (defaultKoreLogOptions (ExeName "") startTime)
                    { Log.logLevel = coLogLevel
                    , Log.logEntries = koreLogExtraLevels
                    , Log.timestampsSwitch = TimestampsDisable
                    , Log.debugSolverOptions = debugSolverOptions
                    , Log.logType = LogSomeAction $ LogAction $ \txt -> liftIO $ monadLogger defaultLoc "kore" logLevel $ toLogStr txt
                    }
            srvSettings = serverSettings port "*"

        liftIO $ void $ withBugReport (ExeName "kore-rpc-booster") BugReportOnError $ \reportDirectory ->
            withLogger reportDirectory koreLogOptions $ \actualLogAction -> do
                mvarLogAction <- newMVar actualLogAction
                let logAction = swappableLogger mvarLogAction

                let defaultTactic = fromMaybe (SMT.List [SMT.Atom "check-sat-using", SMT.Atom "smt"]) koreSolverOptions.tactic
                kore@KoreServer{runSMT} <-
                    mkKoreServer Log.LoggerEnv{logAction} clOPts koreSolverOptions{tactic = Just defaultTactic}

                withMDLib llvmLibraryFile $ \mdl -> do
                    mLlvmLibrary <- maybe (pure Nothing) (fmap Just . mkAPI) mdl
                    boosterState <-
                        liftIO $
                            newMVar Booster.ServerState{definitions, defaultMain = mainModuleName, mLlvmLibrary}
                    statsVar <- if printStats then Just <$> Stats.newStats else pure Nothing

                    runLoggingT (Logger.logInfoNS "proxy" "Starting RPC server") monadLogger

                    let koreRespond, boosterRespond :: Respond (API 'Req) (LoggingT IO) (API 'Res)
                        koreRespond = Kore.respond kore.serverState (ModuleName kore.mainModule) runSMT
                        boosterRespond = Booster.respond boosterState

                        proxyConfig = ProxyConfig{statsVar, forceFallback, boosterState}
                        server =
                            jsonRpcServer
                                srvSettings
                                (const $ Proxy.respondEither proxyConfig boosterRespond koreRespond)
                                [handleErrorCall, handleSomeException]
                        interruptHandler _ = do
                            when (logLevel >= LevelInfo) $
                                hPutStrLn stderr "[Info#proxy] Server shutting down"
                            whenJust statsVar Stats.showStats
                            exitSuccess
                    handleJust isInterrupt interruptHandler $ runLoggingT server monadLogger
  where
    clParser =
        info
            (clProxyOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

    withMDLib Nothing f = f Nothing
    withMDLib (Just fp) f = withDLib fp $ \dl -> f (Just dl)

    isInterrupt :: AsyncException -> Maybe ()
    isInterrupt UserInterrupt = Just ()
    isInterrupt _other = Nothing

toSeverity :: LogLevel -> Maybe Log.Severity
toSeverity LevelDebug = Just Log.Debug
toSeverity LevelInfo = Just Log.Info
toSeverity LevelWarn = Just Log.Warning
toSeverity LevelError = Just Log.Error
toSeverity LevelOther{} = Nothing

koreExtraLogs :: Map.Map LogLevel Log.EntryTypes
koreExtraLogs =
    Map.map (Set.fromList . mapMaybe (`Map.lookup` Log.textToType Log.registry)) $
        Map.fromList
            [ (LevelOther "SimplifyKore", ["DebugAttemptEquation", "DebugApplyEquation"])
            , (LevelOther "RewriteKore", ["DebugAttemptedRewriteRules", "DebugAppliedRewriteRules"])
            , (LevelOther "SimplifySuccess", ["DebugApplyEquation"])
            , (LevelOther "RewriteSuccess", ["DebugAppliedRewriteRules"])
            ]

data CLProxyOptions = CLProxyOptions
    { clOptions :: CLOptions
    , proxyOptions :: ProxyOptions
    , koreSolverOptions :: !KoreSolverOptions
    , debugSolverOptions :: !Log.DebugSolverOptions
    }

data ProxyOptions = ProxyOptions
    { printStats :: Bool
    -- ^ print timing statistics per request and on shutdown
    , forceFallback :: Maybe Depth
    -- ^ force fallback every n-steps
    }

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header "Haskell Backend Booster Proxy - a JSON RPC server combining kore and booster backends"

clProxyOptionsParser :: Parser CLProxyOptions
clProxyOptionsParser =
    CLProxyOptions
        <$> clOptionsParser
        <*> parseProxyOptions
        <*> parseKoreSolverOptions
        <*> Log.parseDebugSolverOptions
  where
    parseProxyOptions =
        ProxyOptions
            <$> switch
                ( long "print-stats"
                    <> help "(development) Print timing information per request and on shutdown"
                )
            <*> optional
                ( option
                    (Depth <$> auto)
                    ( metavar "INTERIM_SIMPLIFICATION"
                        <> long "interim-simplification"
                        <> help "Perform pattern-wide simplification every N steps"
                        <> showDefault
                    )
                )

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
            Proxy.KoreServer
                { serverState
                , mainModule = mainModuleName
                , runSMT
                , loggerEnv
                }
  where
    KoreSolverOptions{timeOut, rLimit, resetInterval, prelude, tactic} = koreSolverOptions
    smtConfig =
        SMT.defaultConfig
            { SMT.timeOut = timeOut
            , SMT.rLimit = rLimit
            , SMT.resetInterval = resetInterval
            , SMT.prelude = prelude
            , SMT.tactic = tactic
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
