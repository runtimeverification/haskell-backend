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
import Control.Exception (evaluate)
import Control.Monad (forM_, void)
import Control.Monad.Catch (bracket)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logger (LogLevel (..), LoggingT (runLoggingT), MonadLoggerIO (askLoggerIO), ToLogStr (toLogStr), defaultLoc)
import Control.Monad.Logger qualified as Logger
import Data.Conduit.Network (serverSettings)
import Data.IORef (writeIORef)
import Data.InternedText (globalInternedTextCache)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Options.Applicative
import System.Clock (
    Clock (..),
    getTime,
 )

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
import Kore.Log (ExeName (..), KoreLogType (LogSomeAction), LogAction (LogAction), TimestampsSwitch (TimestampsDisable), defaultKoreLogOptions, swappableLogger, withLogger)
import Kore.Log qualified as Log
import Kore.Rewrite.SMT.Lemma (declareSMTLemmas)
import Kore.Syntax.Definition (ModuleName (ModuleName), SentenceAxiom)
import Options.SMT (KoreSolverOptions (..), parseKoreSolverOptions)
import Proxy (KoreServer (..))
import Proxy qualified
import SMT qualified

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <- execParser clParser
    let CLProxyOptions{clOptions = clOPts@CLOptions{definitionFile, mainModuleName, port, logLevels, llvmLibraryFile, eventlogEnabledUserEvents}, koreSolverOptions} = options
        (logLevel, customLevels) = adjustLogLevels logLevels
        levelFilter :: Logger.LogSource -> LogLevel -> Bool
        levelFilter _source lvl =
            lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

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

        monadLogger <- askLoggerIO

        let coLogLevel = fromMaybe Log.Info $ toSeverity logLevel
            koreLogOptions =
                (defaultKoreLogOptions (ExeName "") startTime)
                    { Log.logLevel = coLogLevel
                    , Log.timestampsSwitch = TimestampsDisable
                    , Log.logType = LogSomeAction $ LogAction $ \txt -> liftIO $ monadLogger defaultLoc "kore" logLevel $ toLogStr txt
                    }
            srvSettings = serverSettings port "*"

        liftIO $ void $ withBugReport (ExeName "hs-booster-proxy") BugReportOnError $ \reportDirectory ->
            withLogger reportDirectory koreLogOptions $ \actualLogAction -> do
                mvarLogAction <- newMVar actualLogAction
                let logAction = swappableLogger mvarLogAction

                kore@KoreServer{runSMT} <- mkKoreServer Log.LoggerEnv{logAction} clOPts koreSolverOptions

                withMDLib llvmLibraryFile $ \mdl -> do
                    mLlvmLibrary <- maybe (pure Nothing) (fmap Just . mkAPI) mdl
                    boosterState <-
                        liftIO $
                            newMVar Booster.ServerState{definitions, defaultMain = mainModuleName, mLlvmLibrary}

                    runLoggingT (Logger.logInfoNS "proxy" "Starting RPC server") monadLogger

                    let koreRespond, boosterRespond :: Respond (API 'Req) (LoggingT IO) (API 'Res)
                        koreRespond = Kore.respond kore.serverState (ModuleName kore.mainModule) runSMT
                        boosterRespond = Booster.respond boosterState
                        server =
                            jsonRpcServer
                                srvSettings
                                (const $ Proxy.respondEither boosterRespond koreRespond)
                                [handleErrorCall, handleSomeException]
                    runLoggingT server monadLogger
  where
    clParser =
        info
            (clProxyOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

    withMDLib Nothing f = f Nothing
    withMDLib (Just fp) f = withDLib fp $ \dl -> f (Just dl)

toSeverity :: LogLevel -> Maybe Log.Severity
toSeverity LevelDebug = Just Log.Debug
toSeverity LevelInfo = Just Log.Info
toSeverity LevelWarn = Just Log.Warning
toSeverity LevelError = Just Log.Error
toSeverity LevelOther{} = Nothing

data CLProxyOptions = CLProxyOptions
    { clOptions :: CLOptions
    , koreSolverOptions :: !KoreSolverOptions
    }

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header "Haskell Backend Booster Proxy - a JSON RPC server combining kore and booster backends"

clProxyOptionsParser :: Parser CLProxyOptions
clProxyOptionsParser =
    CLProxyOptions
        <$> clOptionsParser
        <*> parseKoreSolverOptions

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
