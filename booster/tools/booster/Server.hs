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
    runNoLoggingT,
 )
import Control.Monad.Logger qualified as Logger
import Data.Conduit.Network (serverSettings)
import Data.IORef (writeIORef)
import Data.InternedText (globalInternedTextCache)
import Data.List (intercalate)
import Data.List.Extra (splitOn)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text (decodeUtf8)
import Options.Applicative
import System.Clock (
    Clock (..),
    getTime,
 )
import System.Exit
import System.FilePath.Glob qualified as Glob
import System.IO qualified as IO

import Booster.CLOptions
import Booster.Definition.Attributes.Base (ComputedAxiomAttributes (notPreservesDefinednessReasons))
import Booster.Definition.Base (HasSourceRef (sourceRef), RewriteRule (computedAttributes))
import Booster.Definition.Ceil (ComputeCeilSummary (..), computeCeilsDefinition)
import Booster.GlobalState
import Booster.JsonRpc qualified as Booster
import Booster.Log qualified
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Prettyprinter (renderText)
import Booster.SMT.Base qualified as SMT (SExpr (..), SMTId (..))
import Booster.SMT.Interface (SMTOptions (..))
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace
import Booster.Util qualified as Booster
import Data.Limit (Limit (..))
import GlobalMain qualified
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.BugReport (BugReportOption (..), withBugReport)
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.Internal.TermLike (TermLike, VariableName)
import Kore.JsonRpc (ServerState (..))
import Kore.JsonRpc qualified as Kore
import Kore.JsonRpc.Error hiding (Aborted, error)
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types (API, HaltReason (..), ReqOrRes (Req, Res))
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
import Options.SMT as KoreSMT (KoreSolverOptions (..), Solver (..))
import Prettyprinter qualified as Pretty
import Proxy (KoreServer (..), ProxyConfig (..))
import Proxy qualified
import SMT qualified as KoreSMT
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
                    , llvmLibraryFile
                    , logLevels
                    , logContexts
                    , notLogContexts
                    , smtOptions
                    , equationOptions
                    , eventlogEnabledUserEvents
                    , simplificationLogFile
                    }
            , proxyOptions =
                ProxyOptions
                    { printStats
                    , forceFallback
                    , boosterSMT
                    , fallbackReasons
                    , simplifyAtEnd
                    }
            } = options
        (logLevel, customLevels) = adjustLogLevels logLevels
        globPatterns = map (Glob.compile . filter (\c -> not (c == '\'' || c == '"'))) logContexts
        negGlobPatterns = map (Glob.compile . filter (\c -> not (c == '\'' || c == '"'))) notLogContexts
        levelFilter :: Logger.LogSource -> LogLevel -> Bool
        levelFilter _source lvl =
            lvl `elem` customLevels || case lvl of { LevelOther l -> 
                not (any (flip Glob.match (Text.unpack l)) negGlobPatterns) &&
                any (flip Glob.match (Text.unpack l)) globPatterns; _ -> False } || lvl >= logLevel && lvl <= LevelError 
        koreLogExtraLevels =
            Set.unions $ mapMaybe (`Map.lookup` koreExtraLogs) customLevels
        koreSolverOptions = translateSMTOpts smtOptions

    Booster.withLogFile simplificationLogFile $ \mLogFileHandle -> do
        let logLevelToHandle = \case
                Logger.LevelOther "SimplifyJson" -> fromMaybe IO.stderr mLogFileHandle
                _ -> IO.stderr

        Booster.runHandleLoggingT logLevelToHandle . Logger.filterLogger levelFilter $ do
            liftIO $ forM_ eventlogEnabledUserEvents $ \t -> do
                putStrLn $ "Tracing " <> show t
                enableCustomUserEvent t
            Logger.logInfoNS "proxy" $
                Text.pack $
                    "Loading definition from "
                        <> definitionFile
                        <> ", main module "
                        <> show mainModuleName

            monadLogger <- askLoggerIO

            liftIO $ void $ withBugReport (ExeName "kore-rpc-booster") BugReportOnError $ \reportDirectory -> withMDLib llvmLibraryFile $ \mdl -> do
                let coLogLevel = fromMaybe Log.Info $ toSeverity logLevel
                    koreLogOptions =
                        (defaultKoreLogOptions (ExeName "") startTime)
                            { Log.logLevel = coLogLevel
                            , Log.logEntries = koreLogExtraLevels
                            , Log.timestampsSwitch = TimestampsDisable
                            , Log.debugSolverOptions =
                                Log.DebugSolverOptions . fmap (<> ".kore") $ smtOptions >>= (.transcript)
                            , Log.logType = LogSomeAction $ LogAction $ \txt -> liftIO $ monadLogger defaultLoc "kore" logLevel $ toLogStr txt
                            }
                    srvSettings = serverSettings port "*"

                withLogger reportDirectory koreLogOptions $ \actualLogAction -> do
                    mLlvmLibrary <- maybe (pure Nothing) (fmap Just . mkAPI) mdl
                    definitionsWithCeilSummaries <-
                        liftIO $
                            loadDefinition definitionFile
                                >>= mapM (mapM (runNoLoggingT . computeCeilsDefinition mLlvmLibrary))
                                >>= evaluate . force . either (error . show) id
                    unless (isJust $ Map.lookup mainModuleName definitionsWithCeilSummaries) $ do
                        flip runLoggingT monadLogger $
                            Logger.logErrorNS "proxy" $
                                "Main module " <> mainModuleName <> " not found in " <> Text.pack definitionFile
                        liftIO exitFailure

                    flip runLoggingT monadLogger $
                        forM_ (Map.elems definitionsWithCeilSummaries) $ \(_, summaries) ->
                            forM_ summaries $ \ComputeCeilSummary{rule, ceils} ->
                                Logger.logOtherNS "booster" (Logger.LevelOther "Ceil") $
                                    renderText $
                                        Pretty.vsep $
                                            [ "Partial symbols found in rule"
                                            , Pretty.pretty (sourceRef rule)
                                            , Pretty.indent 2 . Pretty.vsep $
                                                map Pretty.pretty rule.computedAttributes.notPreservesDefinednessReasons
                                            ]
                                                <> if null ceils
                                                    then ["discharged all ceils, rule preserves definedness"]
                                                    else
                                                        [ "rule does NOT preserve definedness. Partially computed ceils:"
                                                        , Pretty.indent 2 . Pretty.vsep $
                                                            map
                                                                (either Pretty.pretty (\t -> "#Ceil(" Pretty.<+> Pretty.pretty t Pretty.<+> ")"))
                                                                (Set.toList ceils)
                                                        ]

                    mvarLogAction <- newMVar actualLogAction
                    let logAction = swappableLogger mvarLogAction

                    kore@KoreServer{runSMT} <-
                        mkKoreServer Log.LoggerEnv{logAction} clOPts koreSolverOptions

                    boosterState <-
                        liftIO $
                            newMVar
                                Booster.ServerState
                                    { definitions = Map.map fst definitionsWithCeilSummaries
                                    , defaultMain = mainModuleName
                                    , mLlvmLibrary
                                    , mSMTOptions = if boosterSMT then smtOptions else Nothing
                                    , addedModules = mempty
                                    }
                    statsVar <- if printStats then Just <$> Stats.newStats else pure Nothing

                    writeGlobalEquationOptions equationOptions

                    runLoggingT (Logger.logInfoNS "proxy" "Starting RPC server") monadLogger

                    let koreRespond, boosterRespond :: Respond (API 'Req) (LoggingT IO) (API 'Res)
                        koreRespond = Kore.respond kore.serverState (ModuleName kore.mainModule) runSMT
                        boosterRespond = Booster.Log.runLogger . Booster.Log.withContext "booster" . Booster.respond boosterState

                        proxyConfig =
                            ProxyConfig
                                { statsVar
                                , forceFallback
                                , boosterState
                                , fallbackReasons
                                , simplifyAtEnd
                                , customLogLevels = customLevels
                                }
                        server =
                            jsonRpcServer
                                srvSettings
                                (const $ Proxy.respondEither proxyConfig boosterRespond koreRespond)
                                [ Kore.handleDecidePredicateUnknown
                                , Booster.handleSmtError
                                , handleErrorCall
                                , handleSomeException
                                ]
                        interruptHandler _ = do
                            when (logLevel >= LevelInfo) $
                                IO.hPutStrLn IO.stderr "[Info#proxy] Server shutting down"
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
            ,
                ( LevelOther "RewriteKore"
                , ["DebugAttemptedRewriteRules", "DebugAppliedLabeledRewriteRule", "DebugAppliedRewriteRules"]
                )
            , (LevelOther "SimplifySuccess", ["DebugApplyEquation"])
            , (LevelOther "RewriteSuccess", ["DebugAppliedRewriteRules"])
            ]

data CLProxyOptions = CLProxyOptions
    { clOptions :: CLOptions
    , proxyOptions :: ProxyOptions
    }

data ProxyOptions = ProxyOptions
    { printStats :: Bool
    -- ^ print timing statistics per request and on shutdown
    , forceFallback :: Maybe Depth
    -- ^ force fallback every n-steps
    , boosterSMT :: Bool
    -- ^ whether to use an SMT solver in booster code (but keeping kore-rpc's SMT solver)
    , fallbackReasons :: [HaltReason]
    -- ^ halt reasons to re-execute (fallback) to double-check the result
    , simplifyAtEnd :: Bool
    -- ^ whether to run a post-exec simplification
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
            <*> flag
                True
                False
                ( long "no-booster-smt"
                    <> help "Disable SMT solver for booster code (but keep enabled for legacy code)"
                )
            <*> option
                (eitherReader $ mapM reasonReader . splitOn ",")
                ( long "fallback-on"
                    <> metavar "REASON1,REASON2..."
                    <> value [Branching, Stuck, Aborted]
                    <> help "Halt reasons for which requests should be re-executed with kore-rpc"
                    <> showDefaultWith (intercalate "," . map show)
                )
            <*> flag
                True
                False
                ( long "no-post-exec-simplify"
                    <> help "disable post-exec simplification"
                )

    reasonReader :: String -> Either String HaltReason
    reasonReader = \case
        "Branching" -> Right Branching
        "Stuck" -> Right Stuck
        "Aborted" -> Right Aborted
        other -> Left $ "Reason `" <> other <> "' not supported"

translateSMTOpts :: Maybe SMTOptions -> KoreSMT.KoreSolverOptions
translateSMTOpts = \case
    Just smtOpts ->
        defaultKoreSolverOptions
            { timeOut = KoreSMT.TimeOut . Limit . fromIntegral $ smtOpts.timeout
            , retryLimit =
                KoreSMT.RetryLimit . maybe Unlimited (Limit . fromIntegral) $ smtOpts.retryLimit
            , tactic = fmap translateSExpr smtOpts.tactic
            }
    Nothing ->
        defaultKoreSolverOptions{solver = KoreSMT.None}
  where
    defaultKoreSolverOptions =
        KoreSMT.KoreSolverOptions
            { timeOut = KoreSMT.TimeOut Unlimited
            , retryLimit = KoreSMT.RetryLimit Unlimited
            , rLimit = KoreSMT.RLimit Unlimited
            , resetInterval = KoreSMT.ResetInterval 100
            , prelude = KoreSMT.Prelude Nothing
            , solver = KoreSMT.Z3
            , tactic = Nothing
            }
    translateSExpr :: SMT.SExpr -> KoreSMT.SExpr
    translateSExpr (SMT.Atom (SMT.SMTId x)) = KoreSMT.Atom (Text.decodeUtf8 x)
    translateSExpr (SMT.List ss) = KoreSMT.List $ map translateSExpr ss

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
                        , receivedModules = mempty
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
    KoreSMT.KoreSolverOptions{timeOut, retryLimit, tactic} = koreSolverOptions
    smtConfig :: KoreSMT.Config
    smtConfig =
        KoreSMT.defaultConfig
            { KoreSMT.executable = KoreSMT.defaultConfig.executable
            , -- hack to shut up GHC field warning
              KoreSMT.timeOut = timeOut
            , KoreSMT.retryLimit = retryLimit
            , KoreSMT.tactic = tactic
            }

    -- SMT solver with user declared lemmas
    runSMT ::
        forall a.
        SmtMetadataTools StepperAttributes ->
        [SentenceAxiom (TermLike VariableName)] ->
        KoreSMT.SMT a ->
        IO a
    runSMT metadataTools lemmas m =
        flip Log.runLoggerT logAction $
            bracket (KoreSMT.newSolver smtConfig) KoreSMT.stopSolver $ \refSolverHandle -> do
                let userInit = KoreSMT.runWithSolver $ declareSMTLemmas metadataTools lemmas
                    solverSetup =
                        KoreSMT.SolverSetup
                            { userInit
                            , refSolverHandle
                            , config = smtConfig
                            }
                KoreSMT.initSolver solverSetup
                KoreSMT.runWithSolver m solverSetup
